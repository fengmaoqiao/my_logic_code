//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author          : $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : FSM of Decryption procedure
//                    
// Simulation Notes : 
//    For simulation, two defines are available
//
//    RW_SIMU_ON   : which creates string signals to display the FSM states on  
//                the waveform viewer.
//
//    RW_ASSERT_ON : which enables System Verilog Assertions.
//
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
//     For simulation with RW_ASSERT_ON, the simulator must support System 
//     Verilog Assertions
//
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :                                                       
// Open issues and future enhancements :                                    
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


module decryptFsm( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreRxClk,            // MAC Core Receive Clock
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain 
                                                        // active low
            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
                                                        // active low
            ///////////////////////////////////////////////
            //$port_g A-MPDU Deaggregator
            ///////////////////////////////////////////////
            input wire [ 7:0]  rxData,                  // Rx data read from MAC-PHY interface FIFO
            input wire         rxDataValid,             // Rx data is valid
            output wire        decryptCntrlReady,       // Indicate that the Crypto is ready to receive data
            
            ///////////////////////////////////////////////
            //$port_g Encryption Engine
            ///////////////////////////////////////////////
            input wire         plainOutDataValid,       // Decrypted data valid
            input wire         plainOutDataEnd_p,       // End of Decrypted data pulse
            input wire         plainOutICVEnd_p,        // End of ICV field pulse
            input wire         encrBufferFull,          // Encryption Buffer full flag
            
            output wire        rxFifoReady,             // Flow control for receiving decrypted data
            output wire        rxError_p,               // Indicates received frame can be discarded
            output wire        encrRxBufFlush_p,        // Flush after end of reception
            output wire        initEncrRxCntrl_p,       // Starting decryption sequence
            output reg         rxCryptoKeyValid,        // Validating Key
            output reg         nullKeyFound,            // Null Key found in RAM
            
            output wire        pushRxDataInBuffer,      // Write pulse to Encryption buffer
            output wire [7:0]  wrDataToEncrBuffer,      // Write data to Encryption buffer

            ///////////////////////////////////////////////
            //$port_g Key Search Engine
            ///////////////////////////////////////////////
            input wire         keyStorageValid_p,       // Key Storage Index Valid
            input wire         keyStorageError_p,       // Error indicating MAC address not found
            
            input wire [1:0]   sppKSR,                  // SPP from RAM
            input wire [2:0]   cTypeKSR,                // Cipher Type from RAM
            input wire [3:0]   vlanIDKSR,               // Virtual LAN ID from RAM
            input wire         useDefKeyKSR,            // Use Default Key from RAM
            
            output wire        indexSearchTrig_p,       // Trigger for searching index from MAC address
            output wire        rxKeySearchIndexTrig_p,  // Trigger for searching parameter from index
            output wire  [9:0] rxKeySearchIndex,        // RAM Index to be searched
            
            ///////////////////////////////////////////////
            //$port_g RX Controller FSM
            ///////////////////////////////////////////////
            input wire         rxControlIdle,           // FSM in idle
            input wire         rxControlToError_p,      // RX FSM goes to error
            input wire         rxControlToFrmBody_p,    // RX FSM goes to frame body
            input wire         acceptProtected,         // Accept protected frame -> trig Encryption Engine
            input wire         discardFrm,              // End of frame with discard command
            input wire         rxFIFOOverFlowError,     // RX FIFO overflow
            input wire         rxInitVectorEnd_p,       // FSM IV end pulse
            input wire         rxExtIV_p,               // Indicate if there is a extended IV
            input wire         decrStatusValid_p,       // Decryption status valid pulse            
            output reg         rxIndexSearchDone,       // Key Search Done Flag
            
            ///////////////////////////////////////////////
            //$port_g Frame decoder
            ///////////////////////////////////////////////
            input wire         bcMcRcved,               // Broadcast/Multicast
            input wire         ctrlFrame,               // Control frame
            input wire         rxAMSDUPresent,          // A-MSDU present
            input wire         barRcved_p,              // BAR received pulse
            input wire         myFrameRcvedTrig_p,      // my Frame pulse trigger for KSR
            input wire         unknownRcved_p,          // Unknown frame received pulse
            input wire  [1:0]  rxDefKeyID,              // Default Key ID

            ///////////////////////////////////////////////
            //$port_g RX FIFO Interface Controller
            ///////////////////////////////////////////////
            input wire         endHeaderDone,           // End of the Header done
            
            output reg         rxDataSelect,            // Select data from Encryption Engine
            output reg         encrPadding4BytesFIFOEn, // Encryption padding 4 bytes enable
            output reg         encrPadding4BytesWriteEn,// Encryption padding 4 bytes write enable
            output wire        encrPadding2BytesFIFOEn, // Encryption padding 2 bytes enable
            output wire        keyIndexCapture_p,       // Key Index returned by keySearch capture pulse

            output wire [15:0] debugPortDecryptFsm      // Port for debug purpose
            );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// decryption FSM states definition
//$fsm_sd decryptCs
parameter 
                       IDLE  =  3'd0,
        KSR_TRIG_WITH_INDEX  =  3'd1,
             KSR_INDEX_WAIT  =  3'd2,
         KSR_TRIG_WITH_ADDR  =  3'd3,
              KSR_ADDR_WAIT  =  3'd4,
              READY_TO_TRIG  =  3'd5,
                  ENCR_TRIG  =  3'd6;


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// decryption FSM signals definition
reg [2:0] decryptCs;  // decryption FSM Current State
reg [2:0] decryptNs;  // decryption FSM Next State

// Encryption padding 4 bytes enable
reg       encrPadding4BytesEn;      

// Ready to trig encryption
reg       rxProtHdrValid;
reg       rxExtIVValid;

// Flag the address search error
reg       ksrAddrError;


// RX Controller pulse delayed by one cc
reg       rxControlIdle_ff1;
reg       rxControlToError_ff1_p;

`ifdef RW_SIMU_ON
// String definition to display decrypt current state
reg [19*8:0] decryptCs_str;
`endif // RW_SIMU_ON

reg keyStorageValid;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


assign debugPortDecryptFsm =  {indexSearchTrig_p,
                               rxKeySearchIndexTrig_p,
                               keyStorageError_p,
                               keyStorageValid_p,
                               1'b0,
                               rxError_p,
                               keyIndexCapture_p,
                               rxControlIdle,
                               decryptCs[2:0],
                               bcMcRcved,
                               myFrameRcvedTrig_p,
                               unknownRcved_p,
                               rxInitVectorEnd_p,
                               rxIndexSearchDone};


// decryption FSM Current State Logic 
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    decryptCs <= IDLE;
  else if(macCoreClkSoftRst_n == 1'b0)
    decryptCs <= IDLE;
  else
    decryptCs <= decryptNs;
end


// decryption FSM Next State Logic.
always @* 
begin
  case(decryptCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits encrypted frame
      if (myFrameRcvedTrig_p || unknownRcved_p)
        //$fsm_t When the frame is received is potentially for this device (myFrameRcvedTrig_p or unknownRcved_p), 
        //the state machine goes to KSR_TRIG_WITH_ADDR state
        decryptNs = KSR_TRIG_WITH_ADDR;
      else
        //$fsm_t While no frame is received, the state machine stays in IDLE state
        decryptNs = IDLE;

    KSR_TRIG_WITH_INDEX:
      //$fsm_s In KSR_TRIG_WITH_INDEX state, the state machine wait for the end of IV fetching
      if((rxInitVectorEnd_p && (!rxProtHdrValid)) || rxProtHdrValid)
      begin
        if(ksrAddrError && (rxExtIVValid || rxExtIV_p))
          //$fsm_t One clock cycle after rxInitVectorEnd_p or rxProtHdrValid, if there is a ksr addr error and extended IV, the state machine goes to IDLE state
          decryptNs = IDLE;
        else
          //$fsm_t One clock cycle after rxInitVectorEnd_p or rxProtHdrValid, the state machine goes to KSR_INDEX_WAIT state
          decryptNs = KSR_INDEX_WAIT;
      end
      else
        //$fsm_t While not rxProtHdrValid or rxInitVectorEnd_p, the state machine stays in KSR_TRIG_WITH_INDEX
        decryptNs = KSR_TRIG_WITH_INDEX;
    
    KSR_INDEX_WAIT:
      //$fsm_s In KSR_INDEX_WAIT state, the state machine waits pulse from KSR
      if (keyStorageValid_p) 
        //$fsm_t When keyStorageValid_p is received, the state machine goes to READY_TO_TRIG state
        decryptNs = READY_TO_TRIG; 
      else
        //$fsm_t While keyStorageValid_p is not received, the state machine stays in KSR_INDEX_WAIT state
        decryptNs = KSR_INDEX_WAIT;

    KSR_TRIG_WITH_ADDR:
      //$fsm_s In KSR_TRIG_WITH_ADDR state, the state machine goes to KSR_ADDR_WAIT state

      //$fsm_t After one clock cycle, the state machine goes to KSR_ADDR_WAIT state
      decryptNs = KSR_ADDR_WAIT; 

    KSR_ADDR_WAIT:
      //$fsm_s In KSR_WAIT state, the state machine waits pulse from KSR
      if (!ctrlFrame && ((keyStorageValid_p && (useDefKeyKSR || bcMcRcved)) || keyStorageError_p))
`ifdef RW_WAPI_EN
        if(cTypeKSR == 3'b100)  
          decryptNs = READY_TO_TRIG;
        else     
`endif //RW_WAPI_EN
        //$fsm_t When keyStorageValid_p is received and useDefKeyKSR or bcMcRcved is active or 
        // when address is not found, the state machine goes to KSR_TRIG_WITH_INDEX state
        decryptNs = KSR_TRIG_WITH_INDEX;
      else if (keyStorageValid_p || (ctrlFrame && keyStorageError_p))
        //$fsm_t When keyStorageValid_p is received, or no address found and the frame is control type, then the state machine goes to READY_TO_TRIG state
        decryptNs = READY_TO_TRIG;
      else
        //$fsm_t While keyStorageValid_p or keyStorageError_p are not received, the state machine stays in KSR_ADDR_WAIT state
        decryptNs = KSR_ADDR_WAIT;

    READY_TO_TRIG:
      //$fsm_s In READY_TO_TRIG state, the state machine waits Init vector valid
      if (rxProtHdrValid)
      begin
`ifdef RW_WAPI_EN
        if (acceptProtected && !nullKeyFound && ((rxExtIVValid == cTypeKSR[1]) || (rxExtIVValid && (cTypeKSR == 3'b100))) )
`else
        if (acceptProtected && !nullKeyFound && (rxExtIVValid == cTypeKSR[1]))
`endif //RW_WAPI_EN
          //$fsm_t When rxProtHdrValid is received and frame decryption is accepted and the key is not null, the state machine goes to ENCR_TRIG state
          decryptNs = ENCR_TRIG; 
        else
          //$fsm_t When rxProtHdrValid is received and frame is not accepted or the key is null, the state machine goes to IDLE state
          decryptNs = IDLE; 
      end
      else
        //$fsm_t While rxProtHdrValid is not received, the state machine stays in READY_TO_TRIG state
        decryptNs = READY_TO_TRIG;

    ENCR_TRIG:
      //$fsm_s In ENCR_TRIG state, the state machine goes to IDLE state

      //$fsm_t After one clock cycle, the state machine goes to IDLE state
      decryptNs = IDLE; 

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        decryptNs = IDLE; 
    // pragma coverage block = on
  endcase

  if (((decryptCs != IDLE) && rxControlToError_p) || rxControlIdle)
    //$fsm_t When rxError_p or rxControlIdle are true, then fsm goes to IDLE state
    decryptNs = IDLE; 
  
end

// Trigger to Key Search Engine
assign indexSearchTrig_p      = (decryptCs == KSR_TRIG_WITH_ADDR) || 
                                (barRcved_p && !bcMcRcved);
assign rxKeySearchIndexTrig_p = (decryptCs == KSR_TRIG_WITH_INDEX) && (decryptNs == KSR_INDEX_WAIT);
assign rxKeySearchIndex       = {4'b0,vlanIDKSR[3:0],rxDefKeyID};

// Mux between data from deaggregator or encryption Engine
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)                             // Asynchronous Reset
    rxDataSelect <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || 
           (rxControlIdle == 1'b1)       || 
           decrStatusValid_p             ||
           nullKeyFound                  ||
           (rxFIFOOverFlowError == 1'b1)) // Synchronous Reset
    rxDataSelect <= 1'b0;
  else if (acceptProtected && !nullKeyFound && rxControlToFrmBody_p)
    rxDataSelect <= 1'b1;
end


assign keyIndexCapture_p = (decryptCs == KSR_ADDR_WAIT) && (keyStorageValid_p || keyStorageError_p);
// By default the flag is valid
// When start searching it goes in invalid until keySearchValid ot keySearchError
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)      // Asynchronous Reset
    rxIndexSearchDone <= 1'b1;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1)) // Synchronous Reset
    rxIndexSearchDone <= 1'b1;
  else if ((decryptCs != KSR_ADDR_WAIT) && (decryptNs == KSR_ADDR_WAIT))
    rxIndexSearchDone <= 1'b0;
  else if ((decryptCs == KSR_ADDR_WAIT) && (keyStorageError_p || keyStorageValid_p))
    rxIndexSearchDone <= 1'b1;
end

// Trigger to Encryption Engine
assign rxError_p          = rxDataSelect && rxControlToError_ff1_p;
assign encrRxBufFlush_p   = rxDataSelect && rxControlIdle && !rxControlIdle_ff1;
assign initEncrRxCntrl_p  = (decryptCs == ENCR_TRIG);

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    rxControlIdle_ff1      <= 1'b1;
    rxControlToError_ff1_p <= 1'b1;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    rxControlIdle_ff1      <= 1'b1;
    rxControlToError_ff1_p <= 1'b1;
  end
  else
  begin
    rxControlIdle_ff1      <= rxControlIdle;
    rxControlToError_ff1_p <= rxControlToError_p;
  end
end

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)      // Asynchronous Reset
    rxProtHdrValid <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1)) // Synchronous Reset
    rxProtHdrValid <= 1'b0;
  else if (rxControlToFrmBody_p)
    rxProtHdrValid <= 1'b1;
end

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)      // Asynchronous Reset
    keyStorageValid <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1)) // Synchronous Reset
    keyStorageValid <= 1'b0;
  else if (keyStorageValid_p)
    keyStorageValid <= 1'b1;
end

// Null Key information to Encryption Engine
// Set when the keySearchEngine found keyStorageValid_p and the cipher type is 0
// Set when the keySearchEngine does not match address and the frame has extended IV field
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)      // Asynchronous Reset
    nullKeyFound <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1)) // Synchronous Reset
    nullKeyFound <= 1'b0;
  else if ((((decryptCs == KSR_INDEX_WAIT) || ((decryptCs == KSR_ADDR_WAIT) && !useDefKeyKSR)) && keyStorageValid_p && (cTypeKSR == 3'b00)) 
            || ((decryptCs == KSR_TRIG_WITH_INDEX) && (decryptNs == IDLE)))
    nullKeyFound <= 1'b1;
`ifdef RW_WAPI_EN
  else if ((cTypeKSR == 3'b100) && rxProtHdrValid && !rxExtIVValid && keyStorageValid)
    nullKeyFound <= 1'b1;
  else if ((cTypeKSR != 3'b100) && rxProtHdrValid && (rxExtIVValid != cTypeKSR[1]) && keyStorageValid)
`else
  else if (rxProtHdrValid && (rxExtIVValid != cTypeKSR[1]) && keyStorageValid)
`endif //RW_WAPI_EN
    nullKeyFound <= 1'b1;
end

// Null Key information to Encryption Engine
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)      // Asynchronous Reset
    rxCryptoKeyValid <= 1'b0;
  
  else if((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1) || decrStatusValid_p) // Synchronous Reset
    rxCryptoKeyValid <= 1'b0;
  else if (decryptNs == ENCR_TRIG)
    rxCryptoKeyValid <= 1'b1;
end

// RX Encryption FIFO data
assign pushRxDataInBuffer = rxDataValid && rxDataSelect;
assign wrDataToEncrBuffer = rxData;
assign decryptCntrlReady  = (rxDataSelect) ? !encrBufferFull: 1'b1;

// RX FIFO Interface Controller -> Padding control for Encryption
always @*
begin
  if (rxDataSelect && endHeaderDone)
  begin
    if (((cTypeKSR == 2'b01) || (cTypeKSR == 2'b10)) && 
      ((plainOutICVEnd_p && plainOutDataValid) || 
       (encrPadding4BytesFIFOEn && !encrPadding4BytesWriteEn)))
      // Add 2 quadlets in WEP or TKIP for CCMP MIC
      encrPadding4BytesEn = 1'b1;
    else if ((cTypeKSR == 2'b11) && plainOutDataEnd_p && plainOutDataValid)
      // Add 1 quadlet in CCMP for ICV
      encrPadding4BytesEn = 1'b1;
    else
      encrPadding4BytesEn = 1'b0;
  end
  else
    encrPadding4BytesEn = 1'b0;
end

// Encryption padding outputs to RX FIFO Interface Controller
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    encrPadding4BytesFIFOEn  <= 1'b0;
    encrPadding4BytesWriteEn <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    encrPadding4BytesFIFOEn  <= 1'b0;
    encrPadding4BytesWriteEn <= 1'b0;
  end
  else if (discardFrm)
  begin
    encrPadding4BytesFIFOEn  <= 1'b0;
    encrPadding4BytesWriteEn <= 1'b0;
  end
  else
  begin
    encrPadding4BytesWriteEn <= encrPadding4BytesFIFOEn;
    encrPadding4BytesFIFOEn  <= encrPadding4BytesEn;
  end
end

// Complete quadlet when end of frame body
assign encrPadding2BytesFIFOEn = plainOutDataEnd_p && plainOutDataValid;


// RX FIFO Interface Controller -> Ready to receive data from Encryption Engine
assign rxFifoReady        = rxDataSelect && !encrPadding4BytesEn;

// Flag the keySearchEngine error on Address Search
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)      // Asynchronous Reset
    ksrAddrError <= 1'b0;
  else if((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1)) // Synchronous Reset
    ksrAddrError <= 1'b0;
  else if ((decryptCs == KSR_ADDR_WAIT) && (keyStorageError_p))
    ksrAddrError <= 1'b1;
end

// Flag the rxExtIV_p from rxControllerFSM
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)      // Asynchronous Reset
    rxExtIVValid <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1)) // Synchronous Reset
    rxExtIVValid <= 1'b0;
  else if (rxExtIV_p)
    rxExtIVValid <= 1'b1;
end


///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////
// Display FSM State in string for RTL simulation waveform
//////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// decryptCs FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (decryptCs)
                         IDLE  :  decryptCs_str = {"IDLE"};
          KSR_TRIG_WITH_INDEX  :  decryptCs_str = {"KSR_TRIG_WITH_INDEX"};
               KSR_INDEX_WAIT  :  decryptCs_str = {"KSR_INDEX_WAIT"};
           KSR_TRIG_WITH_ADDR  :  decryptCs_str = {"KSR_TRIG_WITH_ADDR"};
                KSR_ADDR_WAIT  :  decryptCs_str = {"KSR_ADDR_WAIT"};
                READY_TO_TRIG  :  decryptCs_str = {"READY_TO_TRIG"};
                    ENCR_TRIG  :  decryptCs_str = {"ENCR_TRIG"};
                      default  :  decryptCs_str = {"XXX"};
   endcase
end
`endif // RW_SIMU_ON

endmodule
