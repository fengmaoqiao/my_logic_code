//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author: $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : 
//   This module acts as the decryption controller during reception. It takes over
//   control from the Rx controller and forms a parallel path for routing data
//   from the S2P block into the Rx FIFO. It sends all the control signals to
//   the WEP-TKIP block. After the processing is over by the WEP/TKIP block, it gives
//   a two bit status signal, indicating whether decryption passed or failed.
//   If KLG returns a null key indication, this block returns to idle.
//   If rxError_p is asserted, all remaining bytes in the buffer are flushed.
//   If CCMP encryption is to be used, this block writes the received data to the
//   CCMP input buffer instead of the receive FIFO. The CCMP block decrypts
//   the data and writes it into the receive FIFO.
//                    
// Simulation Notes : 
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :                                                       
// Open issues and future enhancements :                                    
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module encryptRxCntrl(

   //$port_g Input ports
   input  wire        hardRstBbClk_n,       // reset signal from hardware
   input  wire        softRstBbClk_p,       // reset signal from software
   
   input  wire        pClk,                 // baseband clock signal
   input  wire        initEncrRxCntrl_p,    // init signal for the wep receive controller
   input  wire        rxDataEnd_p,          // signal to indicate end of reception
   input  wire        rxError_p,            // signal to indicate receive error has occurred
   input  wire        bufferAlmostEmpty,    // indicates that 8 bytes are left in the buffer
   input  wire        bufferEmpty,          // indicates that buffer is empty
   input  wire [7:0]  dataFromBuffer,       // data bus from wep rx buffer

   input  wire        icvCRCOk,             // status signal from the CRC-32 block
   input  wire        initDone_p,           // indicates that PRNG has finished initialisation
   input  wire        prnOutValid_p,        // indicates valid PRND output
   input  wire [7:0]  dataFromXor,          // data bus from XOR block
   input  wire        rxCsIsIdle,           // signal to indicate whether core is in rx or tx
   input  wire        rxFifoReady,          // Flow control signal indicating readiness of
                                            // RX FIFO to accept the decrypted data
   input  wire        writeFCSEn,           // indicates if FCS should be written into Rx FIFO

   input  wire [2:0]  cipherType,           // Cipher Type Input from TX or RX Controller 

   `ifdef CCMP
   input  wire        rxCCMP,               // indicates that CCMP should be used to decrypt
                                            // the received frame.
   input  wire        ccmpRegFull,          // indicates that CCMP input register is full
   input  wire        nextccmpRegFull,      // indicates that CCMP input register is full
   input  wire        nullKeyFound,         // indicates null key
   input  wire        micFailed_p,          // indicates that MIC check is done
   input  wire        micPassed_p,          // indicates that the MIC check passed
   input  wire        stopPopFromBuffer,    // stop reading the encryption buffer 
   input  wire [15:0] rxPayloadLen,         // payload length for the received frame
   input  wire        ccmpOutLastMux_p,     // Last data from CCMP
   input  wire [7:0]  ccmpOutDataMux,       // ccmp shift register out

   `endif

   //$port_g output ports
   `ifdef CCMP
   output reg  [7:0]  dataFromBufferReg,    // indicates that the data is comming from Encryption Buffer
   output reg         rxCCMPDataWrEn_p,     // write enable to the CCMP input buffer
   output wire        rxpayloadEnd_p,       // Indicates that last byte of payload sent to CCMP
                                            // block
   output wire        micEnd,               // Indicates that MIC has been written to the CCMP
                                            // block
   `endif

   output reg         initPRNG_p,           // init signal to PRNG
   
   `ifdef PRNG_FASTER_CLK
   output reg         icvEnable_p,          // enable signal to ICV
   `else
   output wire        icvEnable_p,          // enable signal to ICV
   `endif
   output wire        icvStart_p,           // init signal to ICV
   output reg         prnStrobe_p,          // strobe pulse for releasing PRN output
   output reg         wrFIFOEn_p,           // pulse to write data into Rx FIFO
   output reg         wepPassed_p,          // signal to indicate WEP ICV passed
   output reg         wepFailed_p,          // signal to indicate WEP ICV failed

   output wire  [7:0] dataToFIFO,           // Data to RX FIFO
   output reg         popDataOutBuffer_p,   // pulse to pop data from wep rx buffer
   output reg   [3:0] encrRxCntrlCs,        // Encr. RX Control State machine

   output wire        plainOutDataEnd_p,    // End of Decrypted data pulse
   output wire        plainOutICVEnd_p,     // End of ICV field pulse
   output wire        plainOutFCSValid,     // FCS field valid
   output wire        plainOutMIC           // MIC from buffer to plain
   );


   // ---------------- outputs declared as wires / registers ----------------
   reg          nextPopDataOutBuffer_p;
   reg          popDataOutBufferDelayed_p;

  //--------------------- internal registers & wires -------------------
   reg [3:0]    bytesLeftInBuffer;
   reg [3:0]    nextBytesLeftInBuffer;
   reg [3:0]    encrRxCntrlNs;
   reg          rxEnd;
   reg          initEncrRxCntrl;
   `ifdef CCMP
   reg [15:0]   rxCCMPByteCnt;
   reg [15:0]   readByteCnt;
   reg [7:0]    dataFromBufferReg1;
   reg [7:0]    dataFromBufferReg2;
   reg          popDataOutBufferDone;
   reg          singleReadDone;
   reg          twoReadsDone;
   reg          useBuf1;
   reg          useBuf2;
   reg          stopPopFromBufferReg;
   reg          micStatusDone;
   reg          rxfifo_16th_or_last_byte_poped;
   `endif

   reg          nextInitPRNG_p;
   reg          nextPRNStrobe_p;
   reg          nextWrFIFOEn_p;
   reg          bufferToFIFO;

   wire         nextWEPPassed_p;
   wire         nextWEPFailed_p;

   wire [7:0]   dataToFIFOMux1;
   wire [7:0]   dataToFIFOMux2;
   wire [7:0]   dataToFIFOMux3;

    reg         ccmpOutLastMux_p_ff1;
  `ifdef SBOX_RDATA_CAPT
   reg [1:0]    waitCounter;
  `endif

`ifdef SBOX_RDATA_CAPT
  `define INSERT_DELAY
`else
  `ifndef PRNG_FASTER_CLK
    `define INSERT_DELAY
  `else
    `undef INSERT_DELAY
  `endif
`endif

//--------------------- encrRxCntrlCs declarations -------------------
//$fsm_sd encrRxCntrlCs
localparam
           IDLE                     = 4'd0, // Do nothing
           WAIT_FOR_INIT_DONE       = 4'd1, // wait until init_done is asserted
           READ_BUFFER_SEND_ENABLES = 4'd2, // send enables to PRNG and Buffer
           WAIT1                    = 4'd3, // wait encrRxCntrlCs 1
           `ifdef INSERT_DELAY
             WAIT2                    = 4'd4, // wait encrRxCntrlCs 2
           `endif
           WRITE_FCS                = 4'd5, // write FCS from Encr Rx Buffer directly to RX FIFO
           `ifdef CCMP
           WAIT_BEFORE_MIC          = 4'd6, // wait decryption of last block before MIC
           WRITE_MIC                = 4'd7, // write MIC from Encr Rx Buffer directly to RX FIFO
           `endif
           ERROR                    = 4'd8, // empty buffer when error occurs
           `ifdef CCMP
           WAIT_FOR_MIC_DONE        = 4'd9; // FCS into the receive FIFO
           `endif

`ifdef RW_SIMU_ON
// String definition to display encrRxCntrlCs current state
reg [25*8:0] encrRxCntrlCs_str;
`endif // RW_SIMU_ON


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// ICV block is not triggered if a CCMP packet is to be decrypted
`ifdef CCMP
assign       icvStart_p = (encrRxCntrlCs == WAIT_FOR_INIT_DONE) && !rxCCMP && initDone_p;
`else
assign       icvStart_p = (encrRxCntrlCs == WAIT_FOR_INIT_DONE) && initDone_p;
`endif

// FSM modified to incorporate WEP/TKIP Decryption RX control logic
    // IDLE:
    // remain in idle encrRxCntrlCs until initEncrRxCntrl_p is asserted
    // when initEncrRxCntrl_p is asserted, send init signals to PRBS and KLG
    // when initEncrRxCntrl_p is asserted, it is assumed that txRxAddress and 
    // wepDefaultKID are valid. These two values are fields in the received MPDU.
    // KLG will start searching for a key corresponding to this txRxAddress

    // WAIT_FOR_INIT_DONE: 
    // remain in this encrRxCntrlCs until the PRNG block finishes it's transformation
    // and gives signal initDone_p, then proceed with data in WEP Rx buffer
    // If CCMP decryption is to be used, remain in this state till the ccmp buffer
    // full indication is de-asserted and data is available in the receive buffer.

    // READ_BUFFER_SEND_ENABLES:
    // if rxEnd has not been asserted, take in data till bufferAlmostEmpty is 
    // asserted. 
    // after rxEnd is asserted, take in data till bufferAlmostEmpty. after
    // this only 8 bytes of data are left, 4 bytes of ICV and 4 bytes of
    // FCS. The ICV should not get written into the FIFO, FCS should
    // not pass through the ICV
    // During CCMP decryption, the data is read from the buffer and given to the 
    // CCMP block till the ccmpRegFull is asserted. The state machine moves back to
    // WAIT_FOR_INIT_DONE on ccmpRegFull being asserted or end of payload being 
    // detected. Once the payload has been written to the CCMP block and ccmpRegFull
    // is de-asserted again and rxEnd is asserted, 8 bytes of MIC are written to the
    // CCMP block and the state machine transitions to WAIT_BEFORE_MIC.

    // WAIT1:
    // if mode is dot11a, only one wait encrRxCntrlCs is required, because PRNG
    // works at double the baseband clock
    // this wait encrRxCntrlCs gives time to the PRNG block to produce valid output

    // WAIT2:
    // this wait encrRxCntrlCs gives time to the PRNG block to produce valid output

    // WAIT_BEFORE_MIC:
    // only 4 bytes of FCS are left. The FCS should be written to the receive
    // FIFO only after the CCMP block has written the last byte of data to the
    // receive fifo. Hence wait in this state till MIC has been checked.

    // WRITE_FCS:
    // only 4 bytes of FCS are left here, process these in this encrRxCntrlCs.

    // ERROR:
    // when a receive error occurs, remain in this encrRxCntrlCs until all bytes are
    // flushed from the WEP Rx buffer. this encrRxCntrlCs is only used for garbage 
    // collection.
    // If bytes are present in the buffer (ie bufferEmpty is low), wait till
    // rxEnd is asserted before starting flushing.
    // If no bytes are present (ie bufferEmpty is high), directly jump to IDLE.


always @(*)
begin
  case (encrRxCntrlCs)
    IDLE:
    begin
      //$fsm_s In IDLE, the state waits for init pulse 
      if (initEncrRxCntrl_p == 1'b1 && cipherType != 3'b100)
        //$fsm_t If init pulse received, the state goes to WAIT_FOR_INIT_DONE state
        encrRxCntrlNs = WAIT_FOR_INIT_DONE;
      else
        //$fsm_t While no init pulse or the encryption mode is WAPI, the state waits in IDLE state
        encrRxCntrlNs = IDLE;
    end

    WAIT_FOR_INIT_DONE: 
    begin
      //$fsm_s In WAIT_FOR_INIT_DONE, the state wait for either the wep/tkip init is done or the ccmp buffer ready
      `ifdef CCMP
      if (rxCCMP)
      begin
        if (!(ccmpRegFull || bufferEmpty))
        begin
          if (rxEnd == 1'b1 && bufferAlmostEmpty == 1'b1 && bytesLeftInBuffer[3:0] <= 4'd12)
            //$fsm_t If CCMP and the end of encrypted payload is detected, the state goes to WAIT_BEFORE_MIC state
            encrRxCntrlNs = WAIT_BEFORE_MIC;
          else
            encrRxCntrlNs = READ_BUFFER_SEND_ENABLES;
        end
        else 
          encrRxCntrlNs = WAIT_FOR_INIT_DONE;
      end
      else
      `endif
      if (initDone_p == 1'b1)
        //$fsm_t If CCMP and ccmp buffer not full,
        //       or WEP/TKIP init done, the state goes to READ_BUFFER_SEND_ENABLES state 
        encrRxCntrlNs = READ_BUFFER_SEND_ENABLES;
      else
        //$fsm_t If CCMP and not end of payload or ccmp buffer is full, or WEP/TKIP and init is not done, the state stays in WAIT_FOR_INIT_DONE state
        encrRxCntrlNs = WAIT_FOR_INIT_DONE;
    end 

    READ_BUFFER_SEND_ENABLES:
    begin
      //$fsm_s In READ_BUFFER_SEND_ENABLES, the encryption engine forward the byte from encrypt buffer to either CCMP or WEP/TKIP
      `ifdef CCMP
      if (rxCCMP)
      begin
        if(nullKeyFound == 1'b1) 
        begin
          if((bufferEmpty == 1'b1) && (rxEnd == 1'b1))
            //$fsm_t If CCMP and no key and rxend and encrypt buffer is empty, the state goes to IDLE state
            encrRxCntrlNs = IDLE; 
          else
            encrRxCntrlNs = READ_BUFFER_SEND_ENABLES;
        end
        else if (rxEnd == 1'b0 && bufferAlmostEmpty == 1'b1)
          encrRxCntrlNs = READ_BUFFER_SEND_ENABLES;
        else if (rxEnd == 1'b1 && bufferAlmostEmpty == 1'b1 && bytesLeftInBuffer[3:0] <= 4'd12)
          //$fsm_t when CCMP and only 12 bytes of MIC + FCS remaining, the state goes to WAIT_BEFORE_MIC state
          encrRxCntrlNs = WAIT_BEFORE_MIC;
        else if (nextccmpRegFull == 1'b1)
          //$fsm_t If CCMP and ccmp buffer is full, the state goes to WAIT_FOR_INIT_DONE state
          encrRxCntrlNs = WAIT_FOR_INIT_DONE;
        else
          encrRxCntrlNs = READ_BUFFER_SEND_ENABLES;
      end
      else 
      `endif
      if (rxEnd == 1'b0 && bufferAlmostEmpty == 1'b1)
        encrRxCntrlNs = READ_BUFFER_SEND_ENABLES;
      else if (rxEnd == 1'b1 && bufferAlmostEmpty == 1'b1 && (bytesLeftInBuffer[3:0] > 4'd4) && rxFifoReady)
         encrRxCntrlNs = WAIT1;
       else if (rxEnd == 1'b1 && bufferAlmostEmpty == 1'b1 && bytesLeftInBuffer[3:0] <= 4'd4)
         //$fsm_t If WEP/TKIP and next 4 bytes are FCS, the state goes to WRITE_FCS state 
         encrRxCntrlNs = WRITE_FCS; 
       else if (rxFifoReady)
         //$fsm_t If WEP/TKIP and next 8 bytes are ICV and FCS,
         //       or if WEP/TKIP and rxFifoReady  is high, the state goes to WAIT1 state 
         encrRxCntrlNs = WAIT1;
       else
         //$fsm_t If CCMP and null key and not the last byte in encrypt buffer,
         //       or if CCMP and good key and not last payload byte and ccmp buffer is not full,
         //       or if not the end of payload but the bufferAlmostEmpty is set, the state stays in READ_BUFFER_SEND_ENABLES state
         encrRxCntrlNs = READ_BUFFER_SEND_ENABLES;
     end

    WAIT1:
    begin
      //$fsm_s In WAIT1, it gives time to the PRNG block to produce valid output
      `ifndef INSERT_DELAY
          //$fsm_t If WEP/TKIP clock is faster than the macCore clock, the state goes to READ_BUFFER_SEND_ENABLES state
          encrRxCntrlNs = READ_BUFFER_SEND_ENABLES;
      `else

      //$fsm_t If WEP/TKIP clock is the same as the macCore clock, the state goes to WAIT2 state
      encrRxCntrlNs = WAIT2;
      `endif
    end

    `ifdef INSERT_DELAY

    WAIT2:
    begin
      //$fsm_s In WAIT2, it gives time to the PRNG block to produce valid output
      `ifdef SBOX_RDATA_CAPT
        `ifdef PRNG_FASTER_CLK
		  if (waitCounter == 2'h0)
        `else
          if (waitCounter == 2'h2)
        `endif
        encrRxCntrlNs = READ_BUFFER_SEND_ENABLES; 
      else
        //$fsm_t if normal ram is used and not 2 clock cycles, the state stays in WAIT2 state
        encrRxCntrlNs = WAIT2;
      `else
      //$fsm_t if normal ram is used and after 2 clock cycles,
      //       or if dual port ram is used and after 1 clock cycle, the state goes to READ_BUFFER_SEND_ENABLES state
      encrRxCntrlNs = READ_BUFFER_SEND_ENABLES;
      `endif
    end
    `endif
    

    `ifdef CCMP
    WAIT_BEFORE_MIC:
    begin
      //$fsm_s In WAIT_BEFORE_MIC, th state waits for ccmp computation of the last payload
      if (ccmpOutLastMux_p || ccmpOutLastMux_p_ff1)
        //$fsm_t When CCMP last payload is computed, the state goes to  WRITE_MIC state
        encrRxCntrlNs = WRITE_MIC;
      else
        //$fsm_t While the CCMP last payload is not done, the state stays in WAIT_BEFORE_MIC state
        encrRxCntrlNs = WAIT_BEFORE_MIC;
    end

    WRITE_MIC:
    begin
      //$fsm_s In WRITE_MIC, the state push the mic from encrypt buffer to CCMP and rxController
      if (bytesLeftInBuffer[3:0] <= 4'd4)
        //$fsm_t When the mic is pushed, the state goes to WRITE_FCS state
        encrRxCntrlNs = WRITE_FCS;
      else
        //$fsm_t When the mic is not pushed, the state stays in WRITE_MIC state
        encrRxCntrlNs = WRITE_MIC;
    end

    WAIT_FOR_MIC_DONE:
    begin
      //$fsm_s In WAIT_FOR_MIC_DONE the state wait for the mic computation
      if (micPassed_p || micFailed_p || micStatusDone)
        //$fsm_t If CCMP mic is done, the state goes to IDLE
        encrRxCntrlNs = IDLE;
      else
        //$fsm_t While the mic is not done, the state stays in WAIT_FOR_MIC_DONE state
        encrRxCntrlNs = WAIT_FOR_MIC_DONE;
    end
    `endif

    WRITE_FCS:
    begin
      //$fsm_s In WRITE_FCS the state pushes 4 bytes from encryption buffer to rxController
      if (bytesLeftInBuffer[3:0] == 4'd0)
      begin
        `ifdef CCMP
        if (rxCCMP)
          //$fsm_t If fcs is pushed and CCMP but the mic is not done, the state goes to WAIT_FOR_MIC_DONE state
          encrRxCntrlNs = WAIT_FOR_MIC_DONE;
        else
        `endif
          //$fsm_t If fcs is done and not CCMP, or CMMP and mic done, the state goes to IDLE state
          encrRxCntrlNs = IDLE;
      end
      else
        //$fsm_t While fcs is not done, the state stays in WRITE_FCS state
        encrRxCntrlNs = WRITE_FCS;
    end

    ERROR:
    begin
      //$fsm_s In ERROR, the state flush the encrypt buffer
      if (bufferEmpty == 1'b0)
        //$fsm_t When the flush is not done, the state stays in ERROR state
        encrRxCntrlNs = ERROR;
      else
        //$fsm_t When the flush is done, the state goes to IDLE state
        encrRxCntrlNs = IDLE;
    end

    default:
    begin
     encrRxCntrlNs = IDLE;
    end
  endcase
end

// build the encrRxCntrlCs flip flops
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    encrRxCntrlCs <= IDLE;
  else if (softRstBbClk_p)
    encrRxCntrlCs <= IDLE;  
  else if (rxError_p)
    // if rxError_p is asserted here, the s/m goes to ERROR for garbage collection.
    encrRxCntrlCs <= ERROR;
  else 
    encrRxCntrlCs <= encrRxCntrlNs;
end

// --------- Logic added for WEP-TKIP RX Control ----- starts here ----------

// logic for nextInitPRNG_p
// send init signal to PRNG after all data has been written or error occurs
// this ensures that the initialisation process of the PRNG is always
// complete well in advance
always @(*)
begin
  case (encrRxCntrlCs)
  WRITE_FCS:
    if (bytesLeftInBuffer[3:0] == 4'b0 && encrRxCntrlNs == IDLE)
      nextInitPRNG_p = 1'b1;
    else
      nextInitPRNG_p = 1'b0;

  ERROR:
    if (bufferEmpty)
      nextInitPRNG_p = 1'b1;
    else
      nextInitPRNG_p = 1'b0;

  default:
    nextInitPRNG_p = 1'b0;
  endcase
end

// logic for initPRNG_p, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    initPRNG_p <= 1'b0;
  else if (softRstBbClk_p)
    initPRNG_p <= 1'b0;
  else
    initPRNG_p <= nextInitPRNG_p;
end

// logic for nextWrFIFOEn_p
// wrFIFOEn_p should be given for all data bytes in the buffer if CCMP 
// decryption is not to be used.
// If CCMP decryption is to be used the undecrypted data is written to the
// CCMP block from the buffer. Only the FCS is written to the recieve FIFO.
// it should not be given for the ICV bytes. therefore as long as
// bytesLeftInBuffer holds values 4, 5, 6, 7, do no send wrFIFOEn_p.
// prnOutValid_p is used because it will be asserted correct number of times.
// it should be given for bytes of FCS, if writeFCSEn has been set.
// popDataOutBuffer_p is used because it will be asserted correct number of 
// times.
always @(*)
begin
  case (encrRxCntrlCs)
    READ_BUFFER_SEND_ENABLES:
    begin
      `ifdef CCMP
      if (rxCCMP == 1'b0)
      begin
        if ((bytesLeftInBuffer[3:0] > 4'd3 && bytesLeftInBuffer[3:0] < 4'd8) || rxError_p)
          nextWrFIFOEn_p = 1'b0;
        else
          nextWrFIFOEn_p = prnOutValid_p;
      end
      else
        nextWrFIFOEn_p = 1'b0;
      `else
      if (rxError_p)
        nextWrFIFOEn_p = 1'b0;
      else if (bytesLeftInBuffer[3:0] > 4'd3 && bytesLeftInBuffer[3:0] < 4'd8) 
        nextWrFIFOEn_p = popDataOutBuffer_p;
      else
        nextWrFIFOEn_p = prnOutValid_p;
      `endif
    end

    WAIT1:
    begin
      if (rxError_p)
        nextWrFIFOEn_p = 1'b0;
      `ifdef CCMP
      else if (!rxCCMP && nextBytesLeftInBuffer[3:0] > 4'd3 && nextBytesLeftInBuffer[3:0] < 4'd8) 
        nextWrFIFOEn_p = popDataOutBuffer_p;
      else if (rxCCMP && bytesLeftInBuffer[3:0] > 4'd3 && bytesLeftInBuffer[3:0] < 4'd8)
        nextWrFIFOEn_p = 1'b0;
      `else
      else if (nextBytesLeftInBuffer[3:0] > 4'd3 && nextBytesLeftInBuffer[3:0] < 4'd8) 
        nextWrFIFOEn_p = popDataOutBuffer_p;
      `endif
      else
        nextWrFIFOEn_p = prnOutValid_p;
    end

    `ifdef INSERT_DELAY
    WAIT2:
    begin
      if (rxError_p)
        nextWrFIFOEn_p = 1'b0;
      `ifdef CCMP
      else if (!rxCCMP && nextBytesLeftInBuffer[3:0] > 4'd3 && nextBytesLeftInBuffer[3:0] < 4'd8) 
        nextWrFIFOEn_p = popDataOutBuffer_p;
      else if (rxCCMP && bytesLeftInBuffer[3:0] > 4'd3 && bytesLeftInBuffer[3:0] < 4'd8)
        nextWrFIFOEn_p = 1'b0;
      `else
      else if (nextBytesLeftInBuffer[3:0] > 4'd3 && nextBytesLeftInBuffer[3:0] < 4'd8) 
        nextWrFIFOEn_p = popDataOutBuffer_p;
      `endif
      else
        nextWrFIFOEn_p = prnOutValid_p;
    end
    `endif

    `ifdef CCMP
    WRITE_MIC:
    begin
      nextWrFIFOEn_p = 1'b0;
    end
    `endif

    WRITE_FCS:
    begin 
      if (writeFCSEn == 1'b1)
        `ifdef CCMP
        nextWrFIFOEn_p = popDataOutBuffer_p && !rxCCMP;
        `else
        nextWrFIFOEn_p = popDataOutBuffer_p;
        `endif
      else
        nextWrFIFOEn_p = 1'b0;
    end

    default:
    begin
      nextWrFIFOEn_p = 1'b0;
    end
  endcase
end

// logic for wrFIFOEn_p, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    wrFIFOEn_p  <= 1'b0;
  else if (softRstBbClk_p)
    wrFIFOEn_p  <= 1'b0;
  else
    wrFIFOEn_p  <= nextWrFIFOEn_p;
end

//always @
//begin
//  wrFIFOEn_p  = nextWrFIFOEn_p;
//end

// logic for nextPRNStrobe_p
// Send strobes for PRN output as long as data has to be passed
// to the XOR block from the buffer, ie for all data bytes and for
// 4 bytes of ICV
always @(*)
begin
  case (encrRxCntrlCs)
    READ_BUFFER_SEND_ENABLES:
    begin
      if (rxEnd == 1'b0 && bufferAlmostEmpty == 1'b1)
        nextPRNStrobe_p = 1'b0; // do nothing
      else if (rxEnd == 1'b1 && bufferAlmostEmpty == 1'b1 && bytesLeftInBuffer[3:0] > 4'd4)
        nextPRNStrobe_p = rxFifoReady; // send strobe when RX FIFO is ready
      else if (rxEnd == 1'b1 && bufferAlmostEmpty == 1'b1 && bytesLeftInBuffer[3:0] <= 4'd4)
        nextPRNStrobe_p = 1'b0; // do nothing
      else
        nextPRNStrobe_p = rxFifoReady; // send strobe when RX FIFO is ready
    end

    default:
    begin
      nextPRNStrobe_p = 1'b0; // do nothing
    end
  endcase
end

// logic for prnStrobe_p, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    prnStrobe_p  <= 1'b0;
  else if (softRstBbClk_p)
    prnStrobe_p  <= 1'b0;
  else
    `ifdef CCMP
    prnStrobe_p  <= nextPRNStrobe_p & ~(rxCCMP);
    `else
    prnStrobe_p  <= nextPRNStrobe_p;
    `endif
end


// logic for wepPassed_p, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    wepPassed_p  <= 1'b0;
  else if (softRstBbClk_p)
    wepPassed_p  <= 1'b0;
  else
    wepPassed_p  <= nextWEPPassed_p;
end

// logic for wepFailed_p, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    wepFailed_p  <= 1'b0;
  else if (softRstBbClk_p)
    wepFailed_p  <= 1'b0;
  else
    wepFailed_p  <= nextWEPFailed_p;
end

// logic for bufferToFIFO
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (!hardRstBbClk_n)
    bufferToFIFO <= 1'b0;
  else if (!initEncrRxCntrl)
    bufferToFIFO <= 1'b0;
  `ifdef CCMP
  else if ((nextBytesLeftInBuffer[3:0] == 4'd7) && !rxCCMP)
    bufferToFIFO <= 1'b1;
  `else
  else if (nextBytesLeftInBuffer[3:0] == 4'd7)
    bufferToFIFO <= 1'b1;
  `endif
  else if (encrRxCntrlNs == WRITE_MIC)
    bufferToFIFO <= 1'b1;
  else
    bufferToFIFO <= bufferToFIFO;
end

// logic for nextWEPPassed_p
// send nextWEPPassed_p when the last byte of FCS has been read from
// buffer. This can be used as flag for end of processing by Rx controller.
assign nextWEPPassed_p = (encrRxCntrlCs == WRITE_FCS && bytesLeftInBuffer[3:0] == 4'b0) &&
                         `ifdef CCMP
                         ~(rxCCMP)                                                      &&
                         `endif
                         icvCRCOk;

// logic for nextWEPFailed_p
// send nextWEPFailed_p when the last byte of FCS has been read from
// buffer. This can be used as flag for end of processing by Rx controller.
assign nextWEPFailed_p = (encrRxCntrlCs == WRITE_FCS && bytesLeftInBuffer[3:0] == 4'b0) &&
                         `ifdef CCMP
                         ~(rxCCMP)                                                      &&
                         `endif
                         ~icvCRCOk;

// logic for dataToFIFO
// multiplex data sent to Rx FIFO from two sources: WEP Rx Buffer and output
// from XOR. If bufferToFIFO is set, data goes from the WEP Rx Buffer direct
// to the FIFO, without XORing it with PRNG output. Otherwise, bytes from
// WEP Rx Buffer are XORed with PRNG bytes and then sent to the FIFO
`ifdef CCMP
 assign dataToFIFOMux1 = rxCCMP ? ccmpOutDataMux : dataFromXor[7:0];
`else
 assign dataToFIFOMux1 = dataFromXor[7:0];
`endif
 assign dataToFIFOMux2 = (useBuf1) ? dataFromBufferReg1 : dataFromBuffer;
 assign dataToFIFOMux3 = bufferToFIFO ? dataToFIFOMux2 : dataToFIFOMux1;
 assign dataToFIFO     = initEncrRxCntrl ? dataToFIFOMux3 : 8'b0;

// prnOutValid_p can be sent as trigger for the icv, ie icvEnable_p
// but this should not be done when the core is transmitting
// therefore tie icvEnable_p to zero during transmission
// When PRNG_FASTER_CLK is enabled, the icvEnable_p is being delayed by 1 
// clock, to allow for the data output from WEP Rx Buffer to be latched.
`ifdef PRNG_FASTER_CLK
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (!hardRstBbClk_n)
    icvEnable_p <= 1'b0;
  else if (!rxCsIsIdle && prnOutValid_p )
    icvEnable_p <= 1'b1;
  else
    icvEnable_p <= 1'b0;
end
`else
  assign icvEnable_p = rxCsIsIdle ? 1'b0 : prnOutValid_p;
`endif


`ifdef SBOX_RDATA_CAPT
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (!hardRstBbClk_n)
    waitCounter[1:0] <= 2'b0;
  else if (softRstBbClk_p)
    waitCounter[1:0] <= 2'b0;
  else if (encrRxCntrlCs == WAIT2)
    waitCounter[1:0] <= waitCounter[1:0] + 1'b1;
  else
    waitCounter[1:0] <= 2'b0;
end
`endif
// ----------------- Addtnl Logic for WEP-TKIP Rx Control ends -------------

// logic for nextBytesLeftInBuffer
// bytesLeftInBuffer is used only for processing the last 8 bytes, ie
// 4 bytes of ICV and 4 bytes of FCS.
// For CCMP, it is used to process the last 12 bytes, ie 8 bytes of MIC and
// 4 bytes of FCS
// it is decremented when bytes are popped from the buffer after
// bufferAlmostEmpty has been asserted.
// it is reset to 8, when bytesLeftInBuffer is 0.
always @(*)
begin
  `ifdef CCMP
  if ((bytesLeftInBuffer[3:0] == 4'h0) || (encrRxCntrlCs == ERROR) || (encrRxCntrlCs == IDLE) || (bufferEmpty && !rxCCMP)) 
    nextBytesLeftInBuffer = 4'd8;
  else if (rxCCMP && !rxEnd)
    nextBytesLeftInBuffer = 4'd12;
  else if (rxCCMP && rxEnd && ccmpRegFull && (encrRxCntrlCs == WAIT_FOR_INIT_DONE))
    nextBytesLeftInBuffer = bytesLeftInBuffer[3:0];
  `else
  if ((bytesLeftInBuffer[3:0] == 4'h0) || (encrRxCntrlCs == ERROR) || (encrRxCntrlCs == IDLE) || bufferEmpty) 
    nextBytesLeftInBuffer = 4'd8;
  `endif
  else if (bufferAlmostEmpty && popDataOutBuffer_p)
    nextBytesLeftInBuffer[3:0] = bytesLeftInBuffer[3:0] - 4'h1;
  else
    nextBytesLeftInBuffer[3:0] = bytesLeftInBuffer[3:0];
end

// logic for bytesLeftInBuffer, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    bytesLeftInBuffer[3:0] <= 4'd8;
  else if (softRstBbClk_p)
    bytesLeftInBuffer[3:0] <= 4'd8;
  else
    bytesLeftInBuffer[3:0] <= nextBytesLeftInBuffer[3:0];
end

`ifdef CCMP
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    rxfifo_16th_or_last_byte_poped <= 1'b0;
  else if (softRstBbClk_p)
    rxfifo_16th_or_last_byte_poped <= 1'b0;
  else if(encrRxCntrlCs == IDLE || ccmpRegFull == 1'b1)
    rxfifo_16th_or_last_byte_poped <= 1'b0;
  else if(((readByteCnt[3:0] >= 4'hE)  || (readByteCnt == (rxPayloadLen - 16'h00c - 16'h002))) && nextPopDataOutBuffer_p && popDataOutBuffer_p)
    rxfifo_16th_or_last_byte_poped <= 1'b1;
end
`endif

// logic for nextPopDataOutBuffer_p
// Read data from buffer until it goes empty. s/m enters WAIT1 only when a byte
// is needed from PRNG, so popDataOutBuffer_p can be asserted here.
// Read 4 bytes of FCS from buffer, while the s/m is in WRITE_FCS and 
// bytesLeftInBuffer > 1;
// in ERROR encrRxCntrlCs, just pop all bytes from the buffer till it goes empty.
always @(*)
begin
  case (encrRxCntrlCs)
    `ifdef CCMP
    WAIT_FOR_INIT_DONE:
    begin
      if (rxCCMP)
      begin
        if (bufferAlmostEmpty)
          nextPopDataOutBuffer_p = 1'b0; 
        else if ((nextccmpRegFull && ccmpRegFull) || stopPopFromBuffer || stopPopFromBufferReg)
          nextPopDataOutBuffer_p = 1'b0;
        else if (rxpayloadEnd_p)
          nextPopDataOutBuffer_p = 1'b0;
        else if((readByteCnt + 16'd13 >= rxPayloadLen) && popDataOutBuffer_p)
          nextPopDataOutBuffer_p = 1'b0;
        else
          nextPopDataOutBuffer_p = 1'b1;
      end
      else
        nextPopDataOutBuffer_p = 1'b0;
    end
    `endif

    READ_BUFFER_SEND_ENABLES:
    begin
      `ifdef CCMP
      if (rxCCMP)
      begin
        if (bufferAlmostEmpty)
          nextPopDataOutBuffer_p = 1'b0; // do nothing
        else if (stopPopFromBuffer || stopPopFromBufferReg || rxpayloadEnd_p || (rxfifo_16th_or_last_byte_poped && !ccmpRegFull && !nextccmpRegFull))
          nextPopDataOutBuffer_p = 1'b0;
        else if((readByteCnt + 16'd13 >= rxPayloadLen) && popDataOutBuffer_p)
          nextPopDataOutBuffer_p = 1'b0;
        else
          nextPopDataOutBuffer_p = 1'b1;
      end
      else
      `endif

      `ifdef PRNG_FASTER_CLK 
      if (!rxEnd && bufferAlmostEmpty)
        nextPopDataOutBuffer_p = 1'b0; // do nothing
      else if (rxEnd && bufferAlmostEmpty && bytesLeftInBuffer[3:0] >= 4'd4)
        nextPopDataOutBuffer_p = rxFifoReady; // send pop when FIFO is ready
      else if (rxEnd && bufferAlmostEmpty && bytesLeftInBuffer[3:0] < 4'd4)
        nextPopDataOutBuffer_p = 1'b0; // do nothing 
      else
        nextPopDataOutBuffer_p = rxFifoReady; // send pop when FIFO is ready
      `else 
        nextPopDataOutBuffer_p = 1'b0; // do nothing 
      `endif
    end

    WAIT1:
    begin
      `ifdef PRNG_FASTER_CLK
      nextPopDataOutBuffer_p = 1'b0; // do nothing 
      `else
      nextPopDataOutBuffer_p = 1'b1; // pop the next cipher text byte
      `endif
    end

    `ifdef CCMP
    WAIT_BEFORE_MIC:
    begin
      if (ccmpOutLastMux_p)
        nextPopDataOutBuffer_p = rxFifoReady; // pop MIC when FIFO is ready
      else
        nextPopDataOutBuffer_p = 1'b0;
    end

    WRITE_MIC:
    begin
      nextPopDataOutBuffer_p = rxFifoReady; // pop MIC when FIFO is ready
    end
    `endif

    WRITE_FCS:
    begin
      if (!bufferEmpty && nextBytesLeftInBuffer[3:0] > 4'h0)
        nextPopDataOutBuffer_p = rxFifoReady;
      else
        nextPopDataOutBuffer_p = 1'b0;
    end 

    ERROR: 
    begin
      `ifdef CCMP
      if(!bufferEmpty)
        nextPopDataOutBuffer_p = 1'b1;
      `else
      if (rxEnd && !bufferEmpty)
        nextPopDataOutBuffer_p = 1'b1;
      `endif
      else
        nextPopDataOutBuffer_p = 1'b0;
    end 

    default:
    begin
      nextPopDataOutBuffer_p = 1'b0;
    end
  endcase
end

// logic for popDataOutBuffer_p, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    popDataOutBuffer_p <= 1'b0;
  else if (softRstBbClk_p)
    popDataOutBuffer_p <= 1'b0;
  else
    popDataOutBuffer_p <= nextPopDataOutBuffer_p;
end

// Logic for popDataOutBufferDelayed_p
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    popDataOutBufferDelayed_p <= 1'b0;
  else if (popDataOutBuffer_p)
    popDataOutBufferDelayed_p <= 1'b1;
  else
    popDataOutBufferDelayed_p <= 1'b0;
end

// register posedge of rxEnd_p in variable rxEnd for furthur use
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0) 
    rxEnd <= 1'b0;
  else if (encrRxCntrlCs == IDLE)
    rxEnd <= 1'b0;
  else if (rxDataEnd_p)
    rxEnd <= 1'b1;
  else 
    rxEnd <= rxEnd;
end

// register posedge of initEncrRxCntrl_p in var initEncrRxCntrl for furthur use
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0) 
    initEncrRxCntrl <= 1'b0;
  else if (initEncrRxCntrl_p)
    initEncrRxCntrl <= 1'b1;
  else if (encrRxCntrlCs == IDLE)
    initEncrRxCntrl <= 1'b0;
  else
    initEncrRxCntrl <= initEncrRxCntrl;
end

// rxController interface for RX FIFO writing
`ifdef CCMP
assign plainOutDataEnd_p = (!rxCCMP &&
                           ((encrRxCntrlCs == READ_BUFFER_SEND_ENABLES) ||
                           `ifdef PRNG_FASTER_CLK
                           (encrRxCntrlCs == WAIT1)) &&
                           `else
                           (encrRxCntrlCs == WAIT2)) &&
                           `endif
                           popDataOutBuffer_p &&
                           (nextBytesLeftInBuffer[3:0] == 4'd7)) || ccmpOutLastMux_p;
assign plainOutICVEnd_p  = !rxCCMP &&
                           ((encrRxCntrlCs == READ_BUFFER_SEND_ENABLES) ||
                           `ifdef INSERT_DELAY
                             (encrRxCntrlCs == WAIT2)) &&
                           `else
                             (encrRxCntrlCs == WAIT1)) &&
                           `endif
                           popDataOutBufferDelayed_p &&
                           (bytesLeftInBuffer[3:0] == 4'd4);
`else
assign plainOutDataEnd_p = (((encrRxCntrlCs == READ_BUFFER_SEND_ENABLES) ||
                           (encrRxCntrlCs == WAIT1)) &&
                           popDataOutBuffer_p &&
                           (nextBytesLeftInBuffer[3:0] == 4'd7)) || ccmpOutLastMux_p;
assign plainOutICVEnd_p  = ((encrRxCntrlCs == READ_BUFFER_SEND_ENABLES) ||
                           (encrRxCntrlCs == WAIT1)) &&
                           popDataOutBufferDelayed_p &&
                           (bytesLeftInBuffer[3:0] == 4'd4);
`endif

assign plainOutFCSValid  = (encrRxCntrlCs == WRITE_FCS);
assign plainOutMIC       = ((encrRxCntrlCs == WRITE_MIC) && (bytesLeftInBuffer == 4'd12)) ? popDataOutBufferDelayed_p : 
                           ((encrRxCntrlCs == WRITE_MIC) && (bytesLeftInBuffer <  4'd12)) ? popDataOutBuffer_p        :
                                                                                                                 1'b0 ;

// Patch the case of the pulse arrive before rxend is detected refs: #1816
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    ccmpOutLastMux_p_ff1 <= 1'b0;
  else if (softRstBbClk_p)
    ccmpOutLastMux_p_ff1 <= 1'b0;
  else if(((encrRxCntrlCs != IDLE) &&  (encrRxCntrlNs == IDLE)) || ((encrRxCntrlCs != WRITE_MIC) &&  (encrRxCntrlNs == WRITE_MIC)))
    ccmpOutLastMux_p_ff1 <= 1'b0;
  else if(ccmpOutLastMux_p && rxCCMP)
    ccmpOutLastMux_p_ff1 <= 1'b1;
end

`ifdef CCMP
// logic for popDataOutBufferDone, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    popDataOutBufferDone  <= 1'b0;
  else 
  begin
    if(rxError_p || (encrRxCntrlCs == IDLE)) 
      popDataOutBufferDone <= 1'b0;
    else if(popDataOutBufferDelayed_p && (nextccmpRegFull || ccmpRegFull))
      popDataOutBufferDone <= 1'b1;
    else if(nextccmpRegFull && ccmpRegFull && !rxCCMPDataWrEn_p && ((readByteCnt - rxCCMPByteCnt) == 16'h001))
      popDataOutBufferDone <= 1'b1;
    else if(rxCCMPDataWrEn_p)
      popDataOutBufferDone <= 1'b0;
    else 
      popDataOutBufferDone <= popDataOutBufferDone;
  end // End of else
end // End of always

// logic for singleReadDone, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    singleReadDone  <= 1'b0;
  else 
  begin
    if(rxError_p || (encrRxCntrlCs == IDLE))
      singleReadDone <= 1'b0;
    else if(rxCCMPDataWrEn_p && !ccmpRegFull)
      singleReadDone <= 1'b0;
    else if(!nextccmpRegFull && useBuf1)
      singleReadDone <= 1'b1;
    else
      singleReadDone <= singleReadDone;
  end // End of else
end // End of always

// logic for twoReadsDone, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    twoReadsDone  <= 1'b0;
  else 
  begin
    if(rxError_p || (encrRxCntrlCs == IDLE))
      twoReadsDone <= 1'b0;
    else if(!ccmpRegFull && useBuf2)
      twoReadsDone <= 1'b1;
    else if(rxCCMPDataWrEn_p && !ccmpRegFull)
      twoReadsDone <= 1'b0;
    else
      twoReadsDone <= twoReadsDone;
  end // End of else
end // End of always

// logic for dataFromBufferReg1, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    dataFromBufferReg1 <= 8'h00;
  else 
  begin
    if(rxError_p)
      dataFromBufferReg1 <= 8'h00;
    else if (popDataOutBufferDelayed_p)
      dataFromBufferReg1 <= dataFromBuffer;
    else
      dataFromBufferReg1 <= dataFromBufferReg1;
  end // End of else
end // End of always
 
// logic for dataFromBufferReg2, registered on clock
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    dataFromBufferReg2 <= 8'h00;
  else 
  begin
    if(rxError_p)
      dataFromBufferReg2 <= 8'h00;
    else if (popDataOutBufferDelayed_p)
      dataFromBufferReg2 <= dataFromBufferReg1;
    else
      dataFromBufferReg2 <= dataFromBufferReg2;
  end // End of else
end // End of always

// Logic for dataFromBufferReg.
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0) 
    dataFromBufferReg <= 8'h00;
  else 
  begin
    if((encrRxCntrlCs == WAIT_FOR_INIT_DONE) && !nextccmpRegFull)
    begin
      if(popDataOutBufferDelayed_p) 
      begin
        if(popDataOutBufferDone)
          dataFromBufferReg <= dataFromBufferReg1;
        else
          dataFromBufferReg <= dataFromBuffer;
      end // End of if
      else if(popDataOutBuffer_p)
        dataFromBufferReg <= dataFromBufferReg1;
      else if(useBuf2)
        dataFromBufferReg <= dataFromBufferReg2;
      else if(useBuf1)
        dataFromBufferReg <= dataFromBufferReg1;
      else
        dataFromBufferReg <= dataFromBuffer;
    end // End of if
    else if((encrRxCntrlCs == READ_BUFFER_SEND_ENABLES) && !ccmpRegFull)
    begin
      if(nullKeyFound)
        dataFromBufferReg <= dataFromBuffer;
      else if(popDataOutBufferDone && ((singleReadDone && !rxCCMPDataWrEn_p) || twoReadsDone)) 
      begin
        if(useBuf2)
          dataFromBufferReg <= dataFromBufferReg2;
        else if(useBuf1)
          dataFromBufferReg <= dataFromBufferReg1;
        else
          dataFromBufferReg <= dataFromBufferReg1;
      end // End of if
      else if(popDataOutBufferDelayed_p)
        dataFromBufferReg <= dataFromBuffer;
      else
        dataFromBufferReg <= dataFromBufferReg1;
    end // End of else if
    else if((encrRxCntrlCs == WRITE_MIC) && !ccmpRegFull)
    begin
      if(nullKeyFound)
        dataFromBufferReg <= dataFromBuffer;
      else if(popDataOutBufferDone && ((singleReadDone && !rxCCMPDataWrEn_p) || twoReadsDone)) 
      begin
        if(useBuf2)
          dataFromBufferReg <= dataFromBufferReg2;
        else if(useBuf1)
          dataFromBufferReg <= dataFromBufferReg1;
        else
          dataFromBufferReg <= dataFromBufferReg1;
      end // End of if
      else if(popDataOutBufferDelayed_p)
        dataFromBufferReg <= dataFromBuffer;
      else
        dataFromBufferReg <= dataFromBufferReg1;
    end // End of if
    else
      dataFromBufferReg <= dataFromBufferReg1;  
  end // End of else 
end // End of always

// Logic for useBuf2
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    useBuf2 <= 1'b0;
  else 
  begin
    `ifdef CCMP
    if(rxError_p || (encrRxCntrlCs == IDLE) || (encrRxCntrlCs == WRITE_FCS) || !rxCCMP)
      useBuf2 <= 1'b0;
    `else
    if(rxError_p || (encrRxCntrlCs == IDLE) || (encrRxCntrlCs == WRITE_FCS))
      useBuf2 <= 1'b0;
    `endif
    else if(ccmpRegFull && popDataOutBuffer_p && popDataOutBufferDelayed_p)
      useBuf2 <= 1'b1;
    else if(nextccmpRegFull && ccmpRegFull && popDataOutBufferDelayed_p &&
      !rxCCMPDataWrEn_p && ((readByteCnt - rxCCMPByteCnt) == 16'h002))
      useBuf2 <= 1'b1;
    else if(nextccmpRegFull && rxpayloadEnd_p && popDataOutBuffer_p && 
      popDataOutBufferDelayed_p)
      useBuf2 <= 1'b1;
    else if(!nextccmpRegFull && (encrRxCntrlCs == WAIT_FOR_INIT_DONE))
      useBuf2 <= 1'b0;
    else if(!ccmpRegFull && (encrRxCntrlCs == READ_BUFFER_SEND_ENABLES))
      useBuf2 <= 1'b0;
    else
      useBuf2 <= useBuf2;
  end // End of else
end // End of always
  
// Logic for stopPopFromBufferReg
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    stopPopFromBufferReg <= 1'b0;
  else 
  begin
    `ifdef CCMP
    if(rxError_p || !rxCCMP)
      stopPopFromBufferReg <= 1'b0;
    `else
    if(rxError_p)
      stopPopFromBufferReg <= 1'b0;
    `endif
    else if(stopPopFromBuffer)
      stopPopFromBufferReg <= 1'b1;
    else if(stopPopFromBufferReg && rxCCMPDataWrEn_p)
      stopPopFromBufferReg <= 1'b0;
    else
      stopPopFromBufferReg <= stopPopFromBufferReg;
  end // End of else
end // End of always
  
// Logic for useBuf1
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    useBuf1 <= 1'b0;
  else 
  begin
    `ifdef CCMP
    if(rxError_p || (encrRxCntrlCs == IDLE) || (encrRxCntrlCs == WRITE_FCS) || !rxCCMP)
      useBuf1 <= 1'b0;
    `else
    if(rxError_p || (encrRxCntrlCs == IDLE) || (encrRxCntrlCs == WRITE_FCS))
      useBuf1 <= 1'b0;
    `endif
    else if((ccmpRegFull || nextccmpRegFull) && 
      (popDataOutBuffer_p || popDataOutBufferDelayed_p))
      useBuf1 <= 1'b1;
    else if(nextccmpRegFull && ccmpRegFull && !rxCCMPDataWrEn_p && 
      ((readByteCnt - rxCCMPByteCnt) == 16'h001))
      useBuf1 <= 1'b1;
    else if(rxCCMPDataWrEn_p)
      useBuf1 <= 1'b0;
    else
      useBuf1 <= useBuf1;
  end // End of else
end // End of always
  
// write enable signal to the CCMP input register block
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    rxCCMPDataWrEn_p <= 1'b0;
  else 
  begin
    if (rxError_p || (encrRxCntrlCs == ERROR) || (encrRxCntrlCs == IDLE))
      rxCCMPDataWrEn_p <= 1'b0;
    else if (nullKeyFound)
      rxCCMPDataWrEn_p <= popDataOutBufferDelayed_p;
    else if (rxpayloadEnd_p)
      rxCCMPDataWrEn_p <= 1'b0;
    `ifdef CCMP
    else if (encrRxCntrlCs == WRITE_MIC) 
    begin
      if (!nextccmpRegFull && popDataOutBufferDone && rxCCMP) 
      begin
        if (useBuf2)
          rxCCMPDataWrEn_p <= 1'b1;
        else if(!ccmpRegFull && ((popDataOutBufferDone && !rxCCMPDataWrEn_p) || 
                                  popDataOutBufferDelayed_p))
          rxCCMPDataWrEn_p <= 1'b1;
        else
          rxCCMPDataWrEn_p <= 1'b0;
      end // End of if
      else if(!nextccmpRegFull && popDataOutBufferDelayed_p && rxCCMP)
          rxCCMPDataWrEn_p <= 1'b1;
      else
         rxCCMPDataWrEn_p <= 1'b0;
    end // End of else if
    else if((encrRxCntrlCs == READ_BUFFER_SEND_ENABLES) && 
      (popDataOutBufferDelayed_p || (popDataOutBufferDone &&
      ((singleReadDone && !rxCCMPDataWrEn_p) || twoReadsDone))) &&
      !ccmpRegFull && rxCCMP  && !(rxEnd && (readByteCnt > (rxPayloadLen - 16'h00c))))
      rxCCMPDataWrEn_p <= 1'b1; 
    else if (encrRxCntrlCs == WAIT_FOR_INIT_DONE) 
    begin
      if (!nextccmpRegFull && popDataOutBufferDone && rxCCMP) 
      begin
        if (useBuf2)
          rxCCMPDataWrEn_p <= 1'b1;
        else if(!ccmpRegFull && (popDataOutBufferDone || popDataOutBufferDelayed_p))
          rxCCMPDataWrEn_p <= 1'b1;
        else
          rxCCMPDataWrEn_p <= 1'b0;
      end // End of if
      else if(!nextccmpRegFull && popDataOutBufferDelayed_p && rxCCMP)
          rxCCMPDataWrEn_p <= 1'b1;
      else
         rxCCMPDataWrEn_p <= 1'b0;
    end // End of else if
    `endif
    else
      rxCCMPDataWrEn_p <= 1'b0;
  end // End of else
end // End of always  

// The payload length is extracted by the receive controller. payload end
// indication is generated when the last byte of payload is being written to
// the CCMP block
assign rxpayloadEnd_p = (rxCCMPByteCnt == (rxPayloadLen - 16'h00c - 16'h001)) && rxCCMPDataWrEn_p;

// Logic to count the number of bytes of payload written to the CCMP block. This
// signal is used to detect the last byte of pay load being written to the CCMP
// block.
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    rxCCMPByteCnt <= 16'h0000;
  else if (!initEncrRxCntrl)
    rxCCMPByteCnt <= 16'h0000;
  else if (rxCCMPDataWrEn_p)
    rxCCMPByteCnt <= rxCCMPByteCnt + 16'h0001;
  else
    rxCCMPByteCnt <= rxCCMPByteCnt;
end

// Logic to count the number of bytes of payload written to the CCMP block. This
// signal is used to detect the last byte of pay load being written to the CCMP
// block.
always @(posedge pClk or negedge hardRstBbClk_n) 
begin
  if (hardRstBbClk_n == 1'b0)
    readByteCnt <= 16'h0000;
  else
  begin
    if(rxError_p)
      readByteCnt <= 16'h0000;
    else if (!initEncrRxCntrl)
      readByteCnt <= 16'h0000;
    else if (popDataOutBuffer_p)
      readByteCnt <= readByteCnt + 16'h0001;
    else
      readByteCnt <= readByteCnt;
  end // End of else
end // End of always

// Logic to indicate that the MIC has been written to the CCMP block
assign micEnd = (encrRxCntrlCs == WRITE_FCS) || (encrRxCntrlCs == WAIT_FOR_MIC_DONE);

// Logic to indicate that MIC status has been received
always @(posedge pClk or negedge hardRstBbClk_n)
begin
  if (hardRstBbClk_n == 1'b0)
    micStatusDone <= 1'b0;
  else if (softRstBbClk_p || (encrRxCntrlCs == IDLE))
    micStatusDone <= 1'b0;
  else if (micPassed_p || micFailed_p)
    micStatusDone <= 1'b1;
end
`endif //  `ifdef CCMP

///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////
// Display FSM State in string for RTL simulation waveform
//////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// encrRxCntrlCs FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (encrRxCntrlCs)
                       IDLE  :  encrRxCntrlCs_str = {"IDLE"};
         WAIT_FOR_INIT_DONE  :  encrRxCntrlCs_str = {"WAIT_FOR_INIT_DONE"};
   READ_BUFFER_SEND_ENABLES  :  encrRxCntrlCs_str = {"READ_BUFFER_SEND_ENABLES"};
                      WAIT1  :  encrRxCntrlCs_str = {"WAIT1"};
`ifdef INSERT_DELAY
                      WAIT2  :  encrRxCntrlCs_str = {"WAIT2"};
`endif
            WAIT_BEFORE_MIC  :  encrRxCntrlCs_str = {"WAIT_BEFORE_MIC"};
                  WRITE_MIC  :  encrRxCntrlCs_str = {"WRITE_MIC"};
                  WRITE_FCS  :  encrRxCntrlCs_str = {"WRITE_FCS"};
                      ERROR  :  encrRxCntrlCs_str = {"ERROR"};
          WAIT_FOR_MIC_DONE  :  encrRxCntrlCs_str = {"WAIT_FOR_MIC_DONE"};
                    default  :  encrRxCntrlCs_str = {"XXX"};
   endcase
end
`endif // RW_SIMU_ON

endmodule
//------------------- END OF FILE ----------------//
