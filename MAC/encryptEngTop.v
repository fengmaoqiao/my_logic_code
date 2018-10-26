//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $RCSmodulefile   : Encryption Engine Top
// $Author          : jvanthou
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: 0.1                                                             
// $Date: 4-Dec-2008                                                                
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : Top level of Encryption Engine module
//                    
// Simulation Notes : 
//    For simulation, five defines are available
//
//    RX_BUFFER_ADDR_WIDTH : Configurable address width of Encryption
//                           Buffer
//    WEP           : Enable WEP encryption / decryption 
//    TKIP          : Enable TKIP encryption / decryption 
//    CCMP          : Enable CCMP encryption / decryption 
//    RW_SIMU_ON       : which creates string signals to display the FSM states 
//                    on the waveform viewers
//
// Synthesis Notes  :
//
//     false_path from ()
//                to   (macCoreClk)
//
// Application Note : 
//     All the signals are coming from MAC Controller clock domain. Hence, no
//     resynchronizations are needed.
//
// Simulator        :
//     
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

`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module encryptEngTop( 
      //$port_g Clock and Reset interface
      input  wire                               macCoreClk,            // macCore clock signal (freerunning clock)
      input  wire                               macCryptClk,           // macCrypt clock signal (gated clock for crypto engine)
      input  wire                               macWTClk,              // Faster Clock for WEP/TKIP engine

      input  wire                               macCoreClkHardRst_n,   // Active low hard reset signal synchronized to the macCoreClk
      input  wire                               macWTClkHardRst_n,     // Active low hard reset signal synchronized to the macWTClk
      
      input  wire                               macCoreClkSoftRst_n,   // Active low soft reset signal synchronized to the macCoreClk
      input  wire                               macWTClkSoftRst_n,     // Active low soft reset signal synchronized to the macWTClk

      output wire                               macCryptClkEn,         // Enable MAC Crypt Clock
      output wire                               macWTClkEn,            // Enable Faster Clock for WEP/TKIP engine

      //$port_g TX Controller Interface
      input  wire [7:0]                         plainTxData,           // Plain (unencrypted) data from TX Controller
      input  wire                               plainTxDataValid,      // Validating signal for plain TX data
      output reg                                cryptoDataReady,       // Flow control signal indicating readiness of crypto  
                                                                       // module for accepting input data 
      output reg [7:0]                          encryptDataOut,        // Encrypted data output for writing into FCS block
      output wire                               encryptDataValid,      // Validating signal for the output encrypted data. 
                                                                       // This signal will be asserted only when 
                                                                       // fcsBusy input is low.
      input  wire                               fcsBusy,               // Flow control signal indicating FCS block is busy 
                                                                       // and not ready for accepting data from crypto module

                                                                       // of encryption
      input  wire [23:0]                        txWEPIV,               // WEP IV from SW
      input  wire                               txWEPIVValid,          // WEP IV Valid
      input  wire                               initPRNG_p_tx,         // Initialize Pseudo Random Number Generator
      input  wire                               icvStart_p_tx,         // Indication to start taking in the data
      input  wire                               txError_p,             // Indication of error signal from TX Controller 
                                                                       // during transmission operation
      input  wire                               txCsIsIdle,            // State machine information from TX Controller
      input  wire                               txTKIP,                // Indication for TKIP encryption
      input  wire [47:0]                        txTkipSeqCntr,         // TKIP Sequence Counter for TKIP encryption

      input  wire                               txCCMP,                // Indication for CCMP encryption
      input  wire                               txCCMPStart,           // Init the CCMP Tx
      input  wire                               txCCMPDataWrEn_p,      // Write pulse for CCMP input buffer for TX
      input  wire                               txPushCCMPHdrInBuffer_p, // Write pulse for storing CCMP header
                                                                       // without encryption into Encr. Buffer
      input  wire                               txEnd_p,               // Pulse to indicate end of transmission
      input  wire                               txPayLoadEnd_p,        // End of payload from TX or RX Controller
                                                                       // needed by CCMP

      input  wire [15:0]                        tcPayLoadLen,          // Transmit payload length in TX Frame
      input  wire [47:0]                        txAddr1,               // Address1 field of TX frame
      input  wire [47:0]                        tcSfc,                 // Transmit SFC field in TX Frame
      input  wire                               txAddress4Pres,        // Tx flag indicating address 4 is present
      input  wire                               txQoSFrame,            // Tx flag indicating the current frame is a QoS Frame
      input  wire [3:0]                         txTID,                 // Tx priority information for QoS frames
      input  wire                               txQoS7,                // HT spp Tx QoS bit 7

      input  wire                               ccmpHTMode,            // HT Flag
      input  wire [1:0]                         sppKSR,                // HT A MSDU Capability

                                                                       // writing encrypted frame to FCS block 
      output wire                               encrTxCCMPBusy,        // Indicates to txController that the ccmp is busy and stop reading the txFifo
      output wire                               encrTxCCMPMicDone,     // tx MIC done indication
      output wire                               initDone_p,            // Indicated PRNG has finished initialization 
                                                                       // and transformation phases
      output reg                                initSBOXDone,          // Flag for WEP and TKIP init done

      //$port_g RX Controller Interface
      input  wire                               rxCsIsIdle,            // Signal to indicate whether core is in TX or RX mode
      input  wire [47:0]                        rxAddr1,               // Address1 field of received frame
      input  wire [47:0]                        rxAddr2,               // Address2 field of received frame
      input  wire [23:0]                        rxInitVector,          // Initialization Vector extracted from frame received
      input  wire [47:0]                        rxTkipSeqCntr,         // TKIP Sequence Counter for TKIP decryption 
      input  wire [15:0]                        rxPayLoadLen,          // RX frame length including MIC and FCS
      input  wire                               rxFifoReady,           // Flow control signal indicating readiness of
                                                                       // Rx FIFO to accept the decrypted data
      input  wire                               rxError_p,             // Trigger indicating received frame should
                                                                       // not be deciphered and can be discarded
      input  wire                               encrRxBufFlush_p,      // Flushing signal asserted after end of current
                                                                       // reception
      input  wire                               writeFCSEn,            // Indication that FCS to be written in RX FIFO
      input  wire                               rxDataEnd_p,           // Signal indicatin last bit of received
                                                                       // frame fed to MAC used by encryption
                                                                       // receive controller 
      input  wire                               rxAddress4Pres,        // Rx flag indicating address 4 is present
      input  wire                               rxQoSFrame,            // Rx flag indicating the current frame is a QoS Frame
      input  wire [3:0]                         rxTID,                 // Rx priority information for QoS frames
      input  wire                               rxQoS7,                // HT spp Rx QoS bit 7
      input  wire                               initEncrRxCntrl_p,     // Trigger signal to crypto engines for starting 
                                                                       // encryption / decryption of the input data
      input  wire                               nullKeyFound,          // Null Key found in RAM
      input  wire                               pushRxDataInBuffer,    // Write pulse from RX controller
      input  wire [7:0]                         wrDataToEncrBuffer,    // Write data from Rx controller
      input  wire                               rxCCMPAADwrEn_p,       // Write enable to CCMP for AAD writing

      output wire [7:0]                         plainDataOut,          // Decrypted (plain) data output to RX 
                                                                       // Controller for writing into RX FIFO
      output wire                               plainOutDataValid,     // Validating signal for the output plain 
                                                                       // data after decryption
      
      output wire                               plainOutDataEnd_p,     // End of Decrypted data pulse
      output wire                               plainOutICVEnd_p,      // End of ICV field pulse
      output wire                               plainOutFCSValid,      // FCS field valid

      output wire                               wepTkipPassed_p,       // Indicates WEP/TKIP decryption was a success
      output wire                               wepTkipFailed_p,       // Indicates WEP/TKIP decryption was a failure
      output reg                                ccmpPassed_p,          // Indicates CCMP description was a success
      output reg                                ccmpFailed_p,          // Indicates CCMP description was a failure
      
      output wire                               wrFIFOEn_c,            // Write enable pulse to RX FIFO 
      
      output wire                               encrBufferFull,        // Encryption FIFO full indication 
      output wire                               encrBufferEmpty,       // Encryption FIFO empty indication 

      //$port_g Control and status registers
      input  wire [47:0]                        macAddress,            // MAC address of the system
      input  wire                               encrRxFIFOReset,       // Encryption RX FIFO Reset
      output wire                               encrRxFIFOResetIn,     // encrRxFIFOResetIn
      output wire                               encrRxFIFOResetInValid,// Clear the encrRxFIFOReset bit
      input  wire                               activeClkGating,       // Active Clock Gating This bit is set by SW to turn on 
                                                                       // active clock gating in HW. When reset, the HW does not 
                                                                       // perform active clock gating, i.e. does not turn off 
                                                                       // clocks to save power in ACTIVE state.



`ifdef RW_WAPI_EN
      //$port_g WAPI Control Interface
      input  wire                               txWAPI,                // WAPI encryption active indication
      input  wire                               txWAPIStart,           // WAPI Start pule 
      input  wire                               rxWAPI,                // WAPI decryption active indication
      
      output wire                               wapiPassed_p,          // WAPI decryption succesfull pulse 
      output wire                               wapiFailed_p,          // WAPI decryption failed pulse 
      
      input  wire [127:0]                       cryptoIntKey,          // Integrity key to be used for encryption or  
                                                                       // decryption operations
      output wire                               wpiDone_p,             // Pulse indicating completion of the processing
      output wire                               encrTxWAPIBusy,        // Indicates to txController that the wapi is busy and stop reading the txFifo
      //$port_g WAPI MAC Header Interface
      input  wire [15:0]                        txFrameControl,        // Frame control field
      input  wire [47:0]                        txAddr3,               // Address 3 from MAC Header
      input  wire [47:0]                        txAddr4,               // Address 4 from MAC Header
      input  wire [15:0]                        txQosCF,               // QoS control field
      input  wire [15:0]                        txSeqControl,          // Sequence control field
      input  wire [7:0]                         txKeyIdx,              // Key index
      input  wire [127:0]                       txPN,                  // Packet number
      
      
      input  wire [15:0]                        rxFrameControl,        // Frame control field of receive frame
      input  wire [47:0]                        rxAddr3,               // Address3 field of received frame
      input  wire [47:0]                        rxAddr4,               // Address4 field of received frame
      input  wire [15:0]                        rxQosCF,               // QoS control field of received frame
      input  wire [15:0]                        rxSeqControl,          // Sequence control field of received frame
      input  wire [7:0]                         rxKeyIdx,              // Key index of received frame
      input  wire [127:0]                       rxPN,                  // Packet number of received frame
      
     
`endif // RW_WAPI_EN
      //$port_g Key search Engine
      input  wire [127:0]                       cryptoKey,             // Key to be used for encryption or decryption 
                                                                       // operations
      input  wire                               cryptoKeyValid,        // Key validating signal
      input  wire [2:0]                         cipherType,            // Cipher Type Input from TX or RX Controller 
      input  wire                               cipherLen,             // Cipher Length Input from TX or RX Controller

      //$port_g DPRAM Interface [s-Box for WEP-TKIP engine]
      input  wire [7:0]                         sBoxAReadData,         // SBox RAM port A read data bus
      input  wire [7:0]                         sBoxBReadData,         // SBox RAM port B read data bus
      output wire [7:0]                         sBoxAAddr,             // SBox RAM port A address bus
      output wire [7:0]                         sBoxBAddr,             // SBox RAM port B address bus
      output wire [7:0]                         sBoxAWriteData,        // SBox RAM port A write data bus
      output wire [7:0]                         sBoxBWriteData,        // SBox RAM port B write data bus
      output wire                               sBoxAWriteEn,          // Write Enable SBox RAM port A
      output wire                               sBoxBWriteEn,          // Write Enable SBox RAM port B
      output wire                               sBoxAEn,               // Enable SBox RAM port A
      output wire                               sBoxBEn,               // Enable SBox RAM port B

      //$port_g DPRAM Interface [Encryption Buffer]
      input  wire [7:0]                         encrRxFIFOReadData,    // Encryption Receive FIFO Read Data bus
      output wire                               encrRxFIFOWriteEn,     // Encryption Receive FIFO Write Enable
      output wire [`RX_BUFFER_ADDR_WIDTH-1:0]   encrRxFIFOWriteAddr,   // Encryption Receive write address 
      output wire [7:0]                         encrRxFIFOWriteData,   // Encryption Receive write data bus
      output wire                               encrRxFIFOReadEn,      // Read enable signal for Encr Buffer
      output wire [`RX_BUFFER_ADDR_WIDTH-1:0]   encrRxFIFOReadAddr,    // Encryption Receive FIFO read address


      input  wire                               debugUseDefaultKeyKSR,    // debug ports
      input  wire                               debugKeyIndexTrig,        // debug ports
      input  wire  [5:0]                        debugKeyIndexKSR,         // debug ports
`ifdef RW_WAPI_EN
      output wire  [15:0]                       debugPortWapi,         // debug ports
`endif //RW_WAPI_EN
      output wire  [31:0]                       debugPortEncryptionEngine // debug ports
      );

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

wire                  encrBufferAlmostEmpty;
wire                  nextccmpRegFull, ccmpRegFull;
wire                  micPassed_p, micFailed_p;
wire                  stopPopFromBuffer;
wire                  ccmpOutValidMux_p;
wire                  ccmpOutLastMux_p;
wire                  rxCCMPDataWrEn_p;
wire                  rxCCMPDataWrEnMux_p;
wire                  rxPayloadEnd_p;

wire                  wepCCMPPlainOutDataEnd_p;

wire [47:0]           tkipSeqCntr;

wire                  rxCCMP;
wire [7:0]            ccmpOutDataMux;
wire [7:0]            dataToRxFIFO;
wire [7:0]            dataFromBufferRegCCMP;
wire [7:0]            dataFromBufferRegCCMPMux;

wire                  initPRNG_p, initPRNG_p_rx, initPRNGSynch_p;
wire                  prnStrobe_p, prnStrobe_p_rx;
wire                  icvStart_p, icvStart_p_rx;
wire                  icvEnable_p, icvEnable_p_rx;
wire                  wrFIFOEn_p;
wire [7:0]            plainText;
wire [7:0]            dataFromXor;

`ifdef SBOX_RDATA_CAPT
  wire [4:0]            prngCs;
`else
  wire [3:0]            prngCs;
`endif
wire [3:0]            encryptRxCntrlCs;
wire                  rxPopDataOutBuffer_p,popRxDataOutBuffer_p;
wire                  icvCRCOk;
wire                  prnOutValid_p;

reg                   latchEncrDataOutBuffer_p;   
reg                   initCCMP_p, encryptDataValidInt;
reg [7:0]             dataFromBufferReg;
reg                   icvEnableLat_p;

wire                  initSBoxIndexDone_p; // signal indicating end of SBOX Index init process

wire                  pushDataInBuffer;
wire                  micEnd;

wire [15:0]           ccmpPayloadLen;
wire [47:0]           ccmpSfc;

wire                  txrxBufferFull;
wire                  ccmp_isIdle;
wire                  plainOutMIC;
wire                  plainOutFCSValidCcmp;
reg                   txCCMPStart_p_ff1;

wire                  flush_rx_buffer_p;

wire [7:0]            txPlainDataOut;
wire                  txBufferNextFull;
wire                  prnStrobe_p_txint;
wire                  icvSDrain_p_int;
wire                  icvEnable_p_txint;

reg  [7:0]            debug_cnt;
reg  [31:0]           debug_lsh_reg;
reg                   debug_valid;
reg  [5:0]            debug_keyindex;
wire [3:0]            ccmp_cntlCS;
wire                  debug_initDonemacWTClk_p;


reg  [7:0]            wrDataToEncrBufferCapt;    // Write data from Rx controller

`ifdef RW_WAPI_EN
wire                  abortWPI_p;
wire                  wpiMode;               // Flag indicating the WPI Mode (0:Encryption, 1:Decryption)
wire                  wpiMICPassed;          // Flag indicating MIC check successful

wire [7:0]            wpiDataIn;             // input data bus to WPI engine
wire                  wpiDataInValid;        // Valid signal for the input WPI data
wire [7:0]            wpiDataOut;            // Output data bus from WPI engine
wire [7:0]            wpiDataOutMux;         // Output data bus from WPI engine mux with MIC and FCS
wire                  wpiDataOutValidMux;         // Valid signal from WPI engine mux with MIC and FCS
wire                  wpiDataOutReady;            // 
wire                  wpiDataOutLast_p;            // 
wire                  wpiDataOutEnd_p;
wire                  wpiDataOutValid_p;     // Valid signal for the output WPI data
wire                  wpiRegFull;            // Flag indicating WPI input register is full and cannot accept new dataIn
wire                  plainOutFCSValidWapi;         // Flag allowing to send FCS from encryption Fifo even if wpi block is busy
wire                  wpiRegAlmostFull;      // Flag indicating WPI input register is almost full and can only accept one byte.
reg                   initWPI_p;             // Initialization trigger pulse for WPI
wire                  wpiIsIdle;             // Flag indicating that the WPI module is back to IDLE state

wire [15:0]           wpiFrameControl;       // Frame Control field for wpi block
wire [47:0]           wpiAddr1;              // Address 1 field for wpi block
wire [47:0]           wpiAddr2;              // Address 2 field for wpi block
wire [47:0]           wpiAddr3;              // Address 3 field for wpi block
wire [47:0]           wpiAddr4;              // Address 4 field for wpi block
wire                  wpiAddress4Pres;       // Flag indicating address 4 is present in MAC Header
wire                  wpiQosFrame;           // Flag indicating that the current frame is a qos frame
wire [15:0]           wpiQosCF;              // QoS control field for wpi block 
wire [15:0]           wpiPduLength;          // Payload length for WPI block
wire [15:0]           wpiSeqControl;         // Sequence Control Field for wpi block
wire [7:0]            wpiKeyIdx;             // WPI Key Index
wire [127:0]          wpiPN;                 // WPI Packet Number
wire                  payloadEnd_p;          // Pulse for payload end indication

wire                  wpiRxPopData;
wire                  wpiRxPayloadEnd_p;
wire                  wpiRxDataInValid;
wire                  nextBufferEmptyFlag;
wire  [7:0]           wpiRxDataIn;
`endif //RW_WAPI_EN


//////////////////////////////////////////////////////////////////////////////
// Beginning of Logic part
//////////////////////////////////////////////////////////////////////////////



// Instanciation of encryptEngClkCntl
// Name of the instance : u_encryptEngClkCntl
// Name of the file containing this module : encryptEngClkCntl.v
encryptEngClkCntl u_encryptEngClkCntl (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.macCryptClkEn          (macCryptClkEn),
		.macWTClkEn             (macWTClkEn),
		.txCsIsIdle             (txCsIsIdle),
		.initSBoxIndexDone_p    (initSBoxIndexDone_p),
		.rxCsIsIdle             (rxCsIsIdle),
		.cipherType             (cipherType),
		.activeClkGating        (activeClkGating)
		);


assign encrRxFIFOWriteData      = wrDataToEncrBuffer; // $todo could be gated by data valid
assign encrTxCCMPBusy           = ((!rxCsIsIdle || !txCsIsIdle) &&  (nextccmpRegFull || ccmpRegFull) && (!ccmp_isIdle || ((initEncrRxCntrl_p || txCCMPStart || txCCMPStart_p_ff1) && cryptoKeyValid))) ? 1'b1 : txBufferNextFull;

// ------------- Encrypted output with flow control logic starts ---------------
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    initSBOXDone <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0 || txEnd_p)
    initSBOXDone <= 1'b0;
  else 
    if(initDone_p == 1'b1)
      initSBOXDone <= 1'b1;
    else if(initSBOXDone && (txCsIsIdle || txEnd_p))
      initSBOXDone <= 1'b0;
end

always @(posedge macCryptClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    txCCMPStart_p_ff1 <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    txCCMPStart_p_ff1 <= 1'b0;
  else if((cryptoKeyValid == 1'b0) && (txCCMPStart == 1'b1))
    txCCMPStart_p_ff1 <= 1'b1;
  else if(txCCMPStart_p_ff1)
    txCCMPStart_p_ff1 <= 1'b0;
end

// Encrypted output data (during transmission)
always @(posedge macCoreClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    encryptDataOut <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    encryptDataOut <= 8'b0;
   // During WEP-TKIP encryption, encrypted output is
   // clocked from output of XOR block in the engine
   // In case of CCMP encryption, the output comes directly
   // from CCMP block
  else if (rxCsIsIdle == 1'b1) begin
         
`ifdef CCMP
       if(txCCMP && ccmpOutValidMux_p) 
          encryptDataOut <= ccmpOutDataMux;
`ifdef RW_WAPI_EN
       else if(~txCCMP && txWAPI && ~fcsBusy)
          encryptDataOut <= wpiDataOut;
       else if(~txCCMP && ~txWAPI && ((prnOutValid_p == 1'b1) || (icvEnableLat_p == 1'b1)))
`else
       else if(~txCCMP && ((prnOutValid_p == 1'b1) || (icvEnableLat_p == 1'b1)))
`endif //RW_WAPI_EN
          encryptDataOut <= dataFromXor;
`else
`ifdef RW_WAPI_EN
     if(~txCCMP && txWAPI && ~fcsBusy)
        encryptDataOut <= wpiDataOut;
     else if(~txWAPI && (prnOutValid_p == 1'b1) || (icvEnableLat_p == 1'b1))
`else
     else if((prnOutValid_p == 1'b1) || (icvEnableLat_p == 1'b1))
`endif //RW_WAPI_EN
       encryptDataOut <= dataFromXor;
`endif

  end
  // Disable output during reception
  else 
    encryptDataOut <= 8'b0;
end   

   // Flow control signal ensuring sampling only when input plain data is valid 
//assign plainText = plainTxDataValid ? plainTxData : 8'b0;

assign plainText = prnStrobe_p_txint ? txPlainDataOut : 8'h0;


   // Flow control signal - Indicating readiness of crypto engine
   // Valid only during transmission and FCS block is ready to accept
   // encrypted output data
always @(posedge macCoreClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    cryptoDataReady <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    cryptoDataReady <= 1'b0;
   // Will be set when the encrypted data is ready to be output to FCS block
   // and FCS block is ready to accept the same
  else if ((fcsBusy == 1'b0) && (rxCsIsIdle == 1'b1))
    cryptoDataReady <= 1'b1;
  else
    cryptoDataReady <= 1'b0;
end           

   // Validating internal signal for encrypted output data
   // Set when ICV & CRC check is successful & during transmission
   // Disabled once FCS block has started accepting data (when busy)
always @(posedge macCoreClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    encryptDataValidInt <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    encryptDataValidInt <= 1'b0;
`ifdef CCMP
  else if ((txCsIsIdle == 1'b0) && (txCCMP == 1'b1) && !fcsBusy)
    encryptDataValidInt <= ccmpOutValidMux_p;
`endif   
  else if ((prnOutValid_p == 1'b1) && (rxCsIsIdle == 1'b1))
    encryptDataValidInt <= 1'b1;
`ifdef RW_WAPI_EN
  else if( (txCsIsIdle == 1'b0) && (txWAPI == 1'b1) && !fcsBusy)
    encryptDataValidInt <= wpiDataOutValid_p;
`endif //RW_WAPI_EN
  else if (fcsBusy == 1'b0)
    encryptDataValidInt <= 1'b0;
end           

always @(posedge macCoreClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    icvEnableLat_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    icvEnableLat_p <= 1'b0;
  else if (icvEnable_p == 1'b1)
    icvEnableLat_p <= 1'b1;
  else
    icvEnableLat_p <= 1'b0;
end           

// Flow-control-cum-validating signal to FCS block for encrypted output data
assign encryptDataValid = (fcsBusy == 1'b0) ? encryptDataValidInt : 1'b0;


   // Write enable for encryption buffer in case of TX:
   // --> When CCMP header is written directly or CCMP data in encrypted form
   // Wherease RX controller write operation of received frame (possibly encrypted)
   // into encryption buffer to be handled outside this module
assign pushDataInBuffer = rxCsIsIdle ? 1'b0 : 
                                       pushRxDataInBuffer;

// Read enable for encryption buffer from two modules:
//    1. TX controller to read the encrypted frame stored in encryption buffer
//    2. Encryption RX Controller to read the frame received from PHY
`ifdef RW_WAPI_EN
assign encrRxFIFOReadEn = rxWAPI ? wpiRxPopData :popRxDataOutBuffer_p;
`else
assign encrRxFIFOReadEn = popRxDataOutBuffer_p;
`endif // RW_WAPI_EN

   
`ifdef CCMP
assign rxCCMP = ~(rxCsIsIdle) & (cipherType == 3'b011);

assign popRxDataOutBuffer_p = rxCsIsIdle ? 
                              1'b0 :
                              (rxPopDataOutBuffer_p && !rxPayloadEnd_p);

`endif

// ------------- Encrypted output with flow control logic ends ---------------


// ------------- Encryption Receive Buffer output starts --------------

// Validating signal for Received (encrypted) frame contents 
// read out from Encryption buffer
always @(posedge macCoreClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    latchEncrDataOutBuffer_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    latchEncrDataOutBuffer_p <= 1'b0;
  else if (encrRxFIFOReadEn == 1'b1)
    latchEncrDataOutBuffer_p <= 1'b1;
  else    
    latchEncrDataOutBuffer_p <= 1'b0;
end

// Latched frame contents (received in encrypted form)
// read out from Encryption buffer
always @(posedge macCoreClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    dataFromBufferReg <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    dataFromBufferReg <= 8'b0;
  else if (latchEncrDataOutBuffer_p == 1'b1)
    dataFromBufferReg <= encrRxFIFOReadData;
end

// ------------- Encryption Receive Buffer output ends --------------


// ------------------- Miscellaneous Glue logic start -----------------
`ifdef CCMP
   // Initialize pulse to CCMP engine - set after valid key is available
always @(posedge macCryptClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    initCCMP_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    initCCMP_p <= 1'b0;
  else 
    initCCMP_p <= (initEncrRxCntrl_p || txCCMPStart || txCCMPStart_p_ff1) & cryptoKeyValid &
                  ((rxCsIsIdle && txCCMP) || rxCCMP);
end

always @(posedge macCryptClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    ccmpPassed_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    ccmpPassed_p <= 1'b0;
  else
    ccmpPassed_p <= micPassed_p;
end

always @(posedge macCryptClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    ccmpFailed_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    ccmpFailed_p <= 1'b0;
  else
    ccmpFailed_p <= micFailed_p;
end

// Encrypted payload length = rxPayLoadLen - MIC - FCS
assign ccmpPayloadLen = rxPayLoadLen - 16'hc;
// Construct SFC from IV and Ext IV
assign ccmpSfc = {rxInitVector[7:0],
                  rxInitVector[15:8],
                  rxTkipSeqCntr[23:16],
                  rxTkipSeqCntr[31:24],
                  rxTkipSeqCntr[39:32],
                  rxTkipSeqCntr[47:40]};
// Mux for AAD build
assign rxCCMPDataWrEnMux_p      = rxCCMPDataWrEn_p || rxCCMPAADwrEn_p;
assign dataFromBufferRegCCMPMux = (rxCCMPAADwrEn_p) ? wrDataToEncrBufferCapt :
                                                      dataFromBufferRegCCMP;


always @(posedge macCoreClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    wrDataToEncrBufferCapt <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    wrDataToEncrBufferCapt <= 8'b0;
  else
    wrDataToEncrBufferCapt <= wrDataToEncrBuffer;
end



`endif

// Multiplexed signal for Initializing Pseudo Random No. Generator module
//assign                initPRNG_p = initPRNG_p_rx | initPRNG_p_tx | initEncrRxCntrl_p;
assign                initPRNG_p = initPRNG_p_rx | initPRNG_p_tx;

// Multiplexed signal for Strobe signal to PRNG module
assign                prnStrobe_p = prnStrobe_p_rx | prnStrobe_p_txint;

// Multiplexed signal to trigger ICV module
assign                icvStart_p = rxCsIsIdle ? icvStart_p_tx : icvStart_p_rx;

// Multiplexed signal to enable ICV module
//assign                icvEnable_p = rxCsIsIdle ? icvEnable_p_tx : icvEnable_p_rx;
assign                icvEnable_p = rxCsIsIdle ? icvEnable_p_txint : icvEnable_p_rx;

// Multiplexed signal for writing decrypted data to Rx FIFO
assign                wrFIFOEn_c = rxCCMP ? wrFIFOEn_p || ccmpOutValidMux_p || plainOutMIC || plainOutFCSValidCcmp : 
`ifdef RW_WAPI_EN
                                   rxWAPI ? wpiDataOutValidMux :
`endif //RW_WAPI_EN
                                   wrFIFOEn_p;
// Multiplexed signal for TKIP Sequence counters
assign                tkipSeqCntr = rxCsIsIdle ? txTkipSeqCntr : rxTkipSeqCntr;

`ifdef RW_WAPI_EN
assign plainOutFCSValid = rxWAPI ? plainOutFCSValidWapi : plainOutFCSValidCcmp;
`else
assign plainOutFCSValid = plainOutFCSValidCcmp;
`endif //RW_WAPI_EN

//`ifdef RW_WAPI_EN
//always @(posedge macCoreClk or negedge macCoreClkHardRst_n) 
//begin
//  if (macCoreClkHardRst_n == 1'b0)
//    plainOutFCSValid <= 1'b0;
//  else if (macCoreClkSoftRst_n == 1'b0)
//    plainOutFCSValid <= 1'b0;
//  else if (rxWAPI) 
//    plainOutFCSValid <= wpiFullByPass;
//  else
//    plainOutFCSValid <= plainOutFCSValidCcmp;
//end
//`else
//assign plainOutFCSValid = plainOutFCSValidCcmp;
//`endif //RW_WAPI_EN

// Validating signal for decrypted output data
// Set only when RX FIFO is ready to accept - as a flow control measure
`ifdef RW_WAPI_EN
assign                plainOutDataValid =  rxCsIsIdle ? 1'b0 : rxWAPI ? wpiDataOutValidMux : wrFIFOEn_c;
`else
assign                plainOutDataValid =  rxCsIsIdle ? 1'b0 : wrFIFOEn_c;
`endif //RW_WAPI_EN

//// Validating signal for decrypted output data
//// Set only when RX FIFO is ready to accept - as a flow control measure
//`ifdef RW_WAPI_EN
//always @(posedge macCoreClk or negedge macCoreClkHardRst_n) 
//begin
//  if (macCoreClkHardRst_n == 1'b0)
//    plainOutDataValid <= 1'b0;
//  else if (macCoreClkSoftRst_n == 1'b0)
//    plainOutDataValid <= 1'b0;
//  else if (!rxCsIsIdle) 
//    if(rxWAPI)
//      plainOutDataValid <= wpiDataOutValidMux;
//    else
//      plainOutDataValid <= wrFIFOEn_c;
//  else
//    plainOutDataValid <= 1'b0;  
//end
//`else
//assign                plainOutDataValid =  rxCsIsIdle ? 1'b0 : wrFIFOEn_c;
//`endif //RW_WAPI_EN

// Decrypted output data during reception of frames
`ifdef RW_WAPI_EN
assign                plainDataOut = rxWAPI ? wpiDataOutMux : dataToRxFIFO;
`else
assign                plainDataOut = dataToRxFIFO;
`endif //RW_WAPI_EN

//// Decrypted output data during reception of frames
//`ifdef RW_WAPI_EN
//always @(posedge macCoreClk or negedge macCoreClkHardRst_n) 
//begin
//  if (macCoreClkHardRst_n == 1'b0)
//    plainDataOut <= 1'b0;
//  else if (macCoreClkSoftRst_n == 1'b0)
//    plainDataOut <= 1'b0;
//  else if (rxWAPI) 
//    plainDataOut <= wpiDataOutMux;
//  else
//    plainDataOut <= dataToRxFIFO;
//end
//`else
//assign                plainDataOut = dataToRxFIFO;
//`endif //RW_WAPI_EN

// Decrypted output data during reception of frames
`ifdef RW_WAPI_EN
assign                plainOutDataEnd_p = rxWAPI ? wpiDataOutEnd_p : wepCCMPPlainOutDataEnd_p;
`else
assign                plainOutDataEnd_p = wepCCMPPlainOutDataEnd_p;
`endif //RW_WAPI_EN
   
//// Decrypted output data during reception of frames
//`ifdef RW_WAPI_EN
//always @(posedge macCoreClk or negedge macCoreClkHardRst_n) 
//begin
//  if (macCoreClkHardRst_n == 1'b0)
//    plainOutDataEnd_p <= 1'b0;
//  else if (macCoreClkSoftRst_n == 1'b0)
//    plainOutDataEnd_p <= 1'b0;
//  else if (rxWAPI) 
//    plainOutDataEnd_p <= wpiDataOutLast_p;
//  else
//    plainOutDataEnd_p <= wepCCMPPlainOutDataEnd_p;
//end
//`else
//assign                plainOutDataEnd_p = wepCCMPPlainOutDataEnd_p;
//`endif //RW_WAPI_EN

// ------------------- Miscellaneous Glue logic end -------------------


// --------------------- Module instantiations start -------------------
   
//////////////////////////////
// WEP / TKIP
//////////////////////////////

txBufferWepTkip u_txBufferWepTkip (
  //$port_g Clock and Reset
  .macCoreClk               (macCryptClk),
  .macCoreClkHardRst_n      (macCoreClkHardRst_n),
  .macCoreClkSoftRst_n      (macCoreClkSoftRst_n),

  //$port_g Tx Controller
  .txPlainData              (plainTxData),              
  .txPlainDataValid         (plainTxDataValid),
  .txPlainDataEnd           (txPayLoadEnd_p),
  .txBufferNextFull         (txBufferNextFull),
  
  //$port_g Wep Tkip interface
  .txCsIsIdle               (txCsIsIdle),
  .cipherType               (cipherType),
  .initDone_p               (initDone_p),
  .prnOutValid_p            (prnOutValid_p),
  .txFcsBusy                (fcsBusy),

  .txPlainDataOut           (txPlainDataOut),
  .prnStrobe_p              (prnStrobe_p_txint),
  .icvEnable_p_tx           (icvEnable_p_txint),
  .icvSDrain_p              (icvSDrain_p_int)
  );


wepTkip u_wepTkip (
    // Inputs
    .hardRstBbClk_n                 (macCoreClkHardRst_n),
`ifndef PRNG_FASTER_CLK
    .softRstBbClk_p                 (~macCoreClkSoftRst_n),
`else
    .macWTClk                       (macWTClk),
    .macWTClkHardRst_n              (macWTClkHardRst_n),
    .macWTClkSoftRst_p              (~macWTClkSoftRst_n),
`endif
    .macCoreClk                     (macCryptClk),
    .rxCsIsIdle                     (rxCsIsIdle),
    .cipherLen                      (cipherLen),
    .cipherType                     (cipherType),
    .initPRNG_p                     (initPRNGSynch_p),
    .initSBoxIndexDone_p            (initSBoxIndexDone_p),
    .prnStrobe_p                    (prnStrobe_p),
    .txWEPIV                        (txWEPIV),
    .txWEPIVValid                   (txWEPIVValid),
    .txRxAddress                    (rxAddr2),
    .cryptoKey                      (cryptoKey),
    .cryptoKeyValid                 (cryptoKeyValid),
    .icvStart_p                     (icvStart_p),
    .icvSDrain_p                    (icvSDrain_p_int),
    .icvEnable_p                    (icvEnable_p),
    .plainText                      (plainText),
    .dataFromBuffer                 (dataFromBufferReg),
    .rxInitVector                   (rxInitVector),
    .rxError_p                      (rxError_p),
    .sBoxAReadData                  (sBoxAReadData),
    .sBoxBReadData                  (sBoxBReadData),
    .txTKIP                         (txTKIP),
    .tkipSeqCntr                    (tkipSeqCntr),
    .macAddr                        (macAddress),
    // Outputs
    .initDone_p                     (initDone_p),
    .prnOutValid_p                  (prnOutValid_p),
    .dataFromXor                    (dataFromXor),
    .icvCRCOk                       (icvCRCOk),
    .sBoxAAddr                      (sBoxAAddr),
    .sBoxBAddr                      (sBoxBAddr),
    .sBoxAWriteData                 (sBoxAWriteData),
    .sBoxBWriteData                 (sBoxBWriteData),
    .sBoxAEn                        (sBoxAEn),
    .sBoxBEn                        (sBoxBEn),
    .sBoxAWriteEn                   (sBoxAWriteEn),
    .sBoxBWriteEn                   (sBoxBWriteEn),
    .prngCs                         (prngCs),
    .debug_initDonemacWTClk_p       (debug_initDonemacWTClk_p)
    );

//////////////////////////////
// Encryption RX Controller
//////////////////////////////
encryptRxCntrl u_encrRxCntrl (
    // Inputs
    .hardRstBbClk_n        (macCoreClkHardRst_n),
    .softRstBbClk_p        (~macCoreClkSoftRst_n),
    .pClk                  (macCoreClk),
    .initEncrRxCntrl_p     (initEncrRxCntrl_p),
    .rxDataEnd_p           (rxDataEnd_p),
    .rxError_p             (rxError_p),
    .bufferAlmostEmpty     (encrBufferAlmostEmpty),
    .bufferEmpty           (encrBufferEmpty),
`ifdef CCMP
    .dataFromBuffer        (encrRxFIFOReadData),
`else
    .dataFromBuffer        (dataFromBufferReg),
`endif
    .icvCRCOk              (icvCRCOk),
    .initDone_p            (initDone_p),
    .prnOutValid_p         (prnOutValid_p),
    .dataFromXor           (dataFromXor),
    .rxCsIsIdle            (rxCsIsIdle),
    .rxFifoReady           (rxFifoReady),
    .writeFCSEn            (writeFCSEn),
    .cipherType            (cipherType),
`ifdef CCMP
    .rxCCMP                (rxCCMP),
    .ccmpRegFull           (ccmpRegFull),
    .nextccmpRegFull       (nextccmpRegFull),
    .nullKeyFound          (nullKeyFound),
    .micFailed_p           (micFailed_p),
    .micPassed_p           (micPassed_p),
    .rxPayloadLen          (rxPayLoadLen),
    .stopPopFromBuffer     (stopPopFromBuffer),
    .ccmpOutLastMux_p      (ccmpOutLastMux_p),
    .ccmpOutDataMux        (ccmpOutDataMux),
`endif 
    // Outputs
    .initPRNG_p            (initPRNG_p_rx),
    .icvEnable_p           (icvEnable_p_rx),
    .icvStart_p            (icvStart_p_rx),
`ifdef CCMP
    .popDataOutBuffer_p    (rxPopDataOutBuffer_p),
`else
    .popDataOutBuffer_p    (popRxDataOutBuffer_p),
`endif
    .prnStrobe_p           (prnStrobe_p_rx),
    .wrFIFOEn_p            (wrFIFOEn_p),
    .wepPassed_p           (wepTkipPassed_p),
    .wepFailed_p           (wepTkipFailed_p),
    .encrRxCntrlCs         (encryptRxCntrlCs),
    .dataToFIFO            (dataToRxFIFO),

    .plainOutDataEnd_p     (wepCCMPPlainOutDataEnd_p),
    .plainOutICVEnd_p      (plainOutICVEnd_p),
    .plainOutFCSValid      (plainOutFCSValidCcmp),
    .plainOutMIC           (plainOutMIC)
`ifdef CCMP
    ,
    .rxpayloadEnd_p        (rxPayloadEnd_p),
    .rxCCMPDataWrEn_p      (rxCCMPDataWrEn_p),
    .micEnd                (micEnd),
    .dataFromBufferReg     (dataFromBufferRegCCMP)
`endif           
    );


//////////////////////////////
// Encryption Buffer Controller
//////////////////////////////

assign flush_rx_buffer_p = (encrRxBufFlush_p || txEnd_p || (txCsIsIdle && rxCsIsIdle));

encryptRxBufCntrl #(.RXBUFCNTRLRXBUFFERSIZE(`RX_BUFFER_SIZE)) u_encrRxBufCntrl (
    // Inputs
    .hardRstBbClk_n         (macCoreClkHardRst_n),
    .softRstBbClk_p         (~macCoreClkSoftRst_n),
    .bbClk                  (macCoreClk),
    .pushDataInBuffer       (pushDataInBuffer),
    .popDataOutBuffer_p     (encrRxFIFOReadEn),
    .rxPayloadLen           (rxPayLoadLen),
    .rxCCMP                 (rxCCMP),
`ifdef RW_WAPI_EN
    .rxWAPI                 (rxWAPI),
    .nextBufferEmptyFlag    (nextBufferEmptyFlag),
`endif //RW_WAPI_EN
    .encrRxBufFlush_p       (flush_rx_buffer_p),
    .encrRxFIFOReset        (encrRxFIFOReset),
    .encrRxFIFOResetIn      (encrRxFIFOResetIn),
    .encrRxFIFOResetInValid (encrRxFIFOResetInValid),
    // Outputs
    .writeEnEncrRxBuffer    (encrRxFIFOWriteEn),
    .bufferEmptyFlag        (encrBufferEmpty),
    .bufferAlmostEmptyFlag  (encrBufferAlmostEmpty),
    .writeAddrEncrRxBuffer  (encrRxFIFOWriteAddr),
    .readAddrEncrRxBuffer   (encrRxFIFOReadAddr),
    .bufferFullFlag         (encrBufferFull)
    );


`ifdef CCMP
assign txrxBufferFull = rxCsIsIdle ? fcsBusy : encrBufferFull;
//////////////////////////////
// CCMP
//////////////////////////////
ccmpTop u_ccmpTop (
    // Inputs
    .macCoreClk         (macCoreClk),
    .macCryptClk        (macCoreClk),
    .nPRst              (macCoreClkHardRst_n),
    .nSRst              (macCoreClkSoftRst_n),
    .rcRxCsIsIdle       (rxCsIsIdle),
    .tcTxCsIsIdle       (txCsIsIdle),
    .initCCMP_p         (initCCMP_p),
    .tcTxCCMPWrEnP      (txCCMPDataWrEn_p),
    .txAddress4Pres     (txAddress4Pres),
    .rxAddress4Pres     (rxAddress4Pres),
    .txQoSFrame         (txQoSFrame),
    .rxQoSFrame         (rxQoSFrame),
    .txTID              (txTID),
    .rxTID              (rxTID),
    .txQoS7             (txQoS7),
    .rxQoS7             (rxQoS7),
    .rxCCMPDataWrEn_p   (rxCCMPDataWrEnMux_p),
    .tcTxPayLdEndP      (txPayLoadEnd_p),
    .rxpayloadEnd_p     (rxPayloadEnd_p),
    .nullKeyFound       (nullKeyFound),
    .popDataOutBuffer_p (rxPopDataOutBuffer_p),

    .tcPlainText        (plainTxData),
    .dataFromBufferReg  (dataFromBufferRegCCMPMux),
    .tcTxErrorP         (txError_p),
    .rxError_p          (rxError_p),
    .tcPayloadLen       (tcPayLoadLen),
    .rcPayloadLen       (ccmpPayloadLen),
    .tcDestId           (macAddress),
    .tcSourceId         (txAddr1),
    .tcSfc              (tcSfc),
    .ccmpHTMode         (ccmpHTMode),
    .sppKSR             (sppKSR),
    
    .rcDestId           (rxAddr2),
    .rcSourceId         (rxAddr1),
    .rcSfc              (ccmpSfc),
    .temporalKey        (cryptoKey),
    .txRxBufferFull     (txrxBufferFull),
    .micEnd             (micEnd),
    // Outputs
    .ccmpOutDataMux     (ccmpOutDataMux),
    .ccmpOutValidMux_p  (ccmpOutValidMux_p),
    .ccmpOutLastMux_p   (ccmpOutLastMux_p),
    .stopPopFromBuffer  (stopPopFromBuffer),
    .ccmpRegFull        (ccmpRegFull),
    .nextccmpRegFull    (nextccmpRegFull),
    .ccmp_isIdle        (ccmp_isIdle),
    .micValid_p         (encrTxCCMPMicDone),
    .micPassed_p        (micPassed_p),
    .micFailed_p        (micFailed_p),
    .ccmp_cntlCS        (ccmp_cntlCS)
    );
`endif
   
   // --------------------- Module instantiations end -------------------

`ifdef RW_WAPI_EN
//////////////////////////////
// WAPI
//////////////////////////////

assign wpiMode = rxCsIsIdle ?  1'b0  : 1'b1;

assign wpiFrameControl = wpiMode ? rxFrameControl : txFrameControl;
assign wpiAddr1        = wpiMode ? rxAddr1 : txAddr1;
assign wpiAddr2        = wpiMode ? rxAddr2 : macAddress;
assign wpiAddr3        = wpiMode ? rxAddr3 : txAddr3;
assign wpiAddr4        = wpiMode ? rxAddr4 : txAddr4;
assign wpiAddress4Pres = wpiMode ? rxAddress4Pres : txAddress4Pres ;
assign wpiQosFrame     = wpiMode ? rxQoSFrame : txQoSFrame ;
assign wpiQosCF        = wpiMode ? rxQosCF : txQosCF;
assign wpiSeqControl   = wpiMode ? rxSeqControl : txSeqControl;
assign wpiKeyIdx       = wpiMode ? rxKeyIdx : txKeyIdx;
assign wpiPduLength    = wpiMode ? rxPayLoadLen - 16'd20 : tcPayLoadLen; // rxPayload_length - MIC(16bytes) - FCS (4 bytes)
assign wpiPN           = wpiMode ? rxPN : txPN;

assign encrTxWAPIBusy  = ( !wpiIsIdle && (!rxCsIsIdle || !txCsIsIdle) && (wpiRegFull || (wpiRegAlmostFull && plainTxDataValid)) ) ? 1'b1 : 1'b0;

assign wpiDataIn       = wpiMode ? wpiRxDataIn : plainTxData;
assign wpiDataInValid  = wpiMode ? wpiRxDataInValid : plainTxDataValid;

assign payloadEnd_p    = wpiMode ? wpiRxPayloadEnd_p : txPayLoadEnd_p ;

assign wpiDataOutReady = wpiMode ? rxFifoReady : ~fcsBusy;

// Initialize pulse to WAPI engine - set after valid key is available
always @(posedge macCryptClk or negedge macCoreClkHardRst_n) begin
  if (macCoreClkHardRst_n == 1'b0)
    initWPI_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    initWPI_p <= 1'b0;
  else 
    initWPI_p <= (initEncrRxCntrl_p || txWAPIStart ) && cryptoKeyValid && ((rxCsIsIdle && txWAPI) || rxWAPI);
end

encryptWAPIRxCntrl u_encryptWAPIRxCntrl (
  //$port_g Clocks and resets
  .macCoreClk           (macCoreClk),
  .macCoreHardRst_n     (macCoreClkHardRst_n),
  .macCoreSoftRst_n     (macCoreClkSoftRst_n),

  .initEncrRxCntrl_p    (initEncrRxCntrl_p),
  .rxWAPI               (rxWAPI),
  .cipherType           (cipherType),
  .rxPayloadLength      (rxPayLoadLen),

  .rxEnd_p              (rxDataEnd_p),
  .rxError_p            (rxError_p),

  .wpiRxPopData         (wpiRxPopData),
  .plainOutFCSValidWapi (plainOutFCSValidWapi),
  .encrFIFOReadData     (encrRxFIFOReadData),
  .bufferEmptyFlag      (encrBufferEmpty), //flag to indicate buffer empty
  .nextBufferEmptyFlag  (nextBufferEmptyFlag),

  .wpiRxPayloadEnd_p    (wpiRxPayloadEnd_p),
  .wpiRegFull           (wpiRegFull),
  .wpiRegAlmostFull     (wpiRegAlmostFull),
  .wpiRxDataInValid     (wpiRxDataInValid),
  .wpiRxDataIn          (wpiRxDataIn),
  .wpiDataOut           (wpiDataOut),
  .wpiDataOutValid_p    (wpiDataOutValid_p),
  .wpiDataOutLast_p     (wpiDataOutLast_p),
  .wpiDataOutEnd_p      (wpiDataOutEnd_p),
  .wpiDataOutMux        (wpiDataOutMux),
  .wpiDataOutValidMux   (wpiDataOutValidMux),
  .abortWPI_p           (abortWPI_p),
  .wpiIsIdle            (wpiIsIdle),
  .wpiDone_p            (wpiDone_p),
  .wpiMICPassed         (wpiMICPassed),
  .wapiPassed_p         (wapiPassed_p),
  .wapiFailed_p         (wapiFailed_p)
);

wpi u_wpi (
  // Clock and Resets
  .wpiClk           (macCryptClk),         
  .nPRst            (macCoreClkHardRst_n),
  .nSRst            (macCoreClkSoftRst_n),
  // Controls signals
  .initWPI_p        (initWPI_p),
  .nullKeyFound     (nullKeyFound),
  .wpiEncryptionKey (cryptoKey),
  .wpiIntegrityKey  (cryptoIntKey),
  .abortWPI_p       (abortWPI_p),
  .wpiDone_p        (wpiDone_p),
  .wpiMICPassed     (wpiMICPassed),
  .wpiMode          (wpiMode),
  .wpiIsIdle        (wpiIsIdle),
  .payloadEnd_p     (payloadEnd_p),
  // MAC Header parameters
  .frameControl     (wpiFrameControl),
  .addr1            (wpiAddr1),
  .addr2            (wpiAddr2),
  .addr3            (wpiAddr3),
  .addr4            (wpiAddr4),
  .address4Pres     (wpiAddress4Pres),
  .qosFrame         (wpiQosFrame),
  .qosCF            (wpiQosCF),
  .seqControl       (wpiSeqControl),
  .keyIdx           (wpiKeyIdx),
  .pduLength        (wpiPduLength),
  .pn               (wpiPN),
  // Data Interface
  .wpiDataIn        (wpiDataIn),
  .wpiDataInValid   (wpiDataInValid),
  .wpiRegFull       (wpiRegFull),
  .wpiRegAlmostFull (wpiRegAlmostFull),
  .wpiDataOut       (wpiDataOut),
  .wpiDataOutValid_p(wpiDataOutValid_p),
  .wpiDataOutLast_p (wpiDataOutLast_p),
  .wpiDataOutReady  (wpiDataOutReady),
  // Debug port
  .wpiDebug         (debugPortWapi)
);


`endif //RW_WAPI_EN


   // --------------------- Input signal synchronizations -----------------

toggleSynch1 U_initPRNGSynch_p (
    .genClk (macCryptClk),
`ifdef PRNG_FASTER_CLK
    .synClk (macWTClk),
    .hardReset_n (macWTClkHardRst_n),
`else
    .synClk (macCryptClk),
    .hardReset_n (macCoreClkHardRst_n),
`endif // PRNG_FASTER_CLK
    .dataIn (initPRNG_p),
    .dataOut (initPRNGSynch_p)
    );

   assign debugPortEncryptionEngine[31:29] = cipherType;
   assign debugPortEncryptionEngine[28]    = cipherLen;
   assign debugPortEncryptionEngine[27]    = debugUseDefaultKeyKSR;
   assign debugPortEncryptionEngine[26]    = cryptoKeyValid;
   assign debugPortEncryptionEngine[25]    = nullKeyFound;
   assign debugPortEncryptionEngine[24]    = wepTkipFailed_p || ccmpFailed_p || rxError_p ||txError_p ;
   assign debugPortEncryptionEngine[23]    = wepTkipPassed_p || ccmpPassed_p;
   assign debugPortEncryptionEngine[22:18] = {debug_valid,debug_lsh_reg[3:0]};
   assign debugPortEncryptionEngine[17]    = (!rxCsIsIdle) ? encrRxFIFOWriteEn : (!txCsIsIdle) ? encryptDataValid : 1'b0;
   assign debugPortEncryptionEngine[16]    = (!rxCsIsIdle) ? plainOutDataValid : (!txCsIsIdle) ? plainTxDataValid : 1'b0;
   assign debugPortEncryptionEngine[15:12] = encryptRxCntrlCs;
   assign debugPortEncryptionEngine[11:8]  = ccmp_cntlCS;
   assign debugPortEncryptionEngine[7:4]   = prngCs[3:0];
   assign debugPortEncryptionEngine[3]     = 1'b0;
   assign debugPortEncryptionEngine[2]     = initPRNG_p_tx || initEncrRxCntrl_p || initDone_p || initCCMP_p;
   assign debugPortEncryptionEngine[1]     = initPRNGSynch_p;
   assign debugPortEncryptionEngine[0]     = debug_initDonemacWTClk_p;

  always @(posedge macCoreClk, negedge macCoreClkHardRst_n)
  begin
    if(macCoreClkHardRst_n == 1'b0)
    begin
      debug_cnt                 <=   8'h0;
      debug_lsh_reg             <=  32'h0;
      debug_valid               <=   1'b0;
      debug_keyindex            <=   6'h0;
    end
    else
    begin
      if(debugKeyIndexTrig)
        debug_keyindex <= debugKeyIndexKSR;

      // Rx
      if(!rxCsIsIdle || !txCsIsIdle)
      begin
        // IV extIV Key  
        if((initDone_p && cipherType != 3'b011) || initEncrRxCntrl_p || (initCCMP_p && cipherType == 3'b011) || (debug_cnt != 8'h0))
        begin
          if(debug_cnt < 8'd57)
          begin
            debug_cnt <= debug_cnt + 8'h1;
          end
          else
          begin
            debug_cnt <= 8'h0;
          end

          case(debug_cnt)
            8'd1 :
            begin
                debug_lsh_reg[15:0] <= {8'hFF,debug_keyindex[3:0],2'h0,debug_keyindex[5:4]};
                debug_valid         <= 1'b1;
            end

            8'd3 :
            begin
                debug_valid         <= 1'b0;
            end

            8'd4 :
            begin
                debug_valid         <= 1'b1;
                if(!rxCsIsIdle)
                  debug_lsh_reg[31:0] <= {8'hFF,rxInitVector[23:0]};
                else
                  debug_lsh_reg[31:0] <= {8'hFF,txWEPIV[23:0]};
              end

            8'd10:
            begin
                debug_valid         <= 1'b0;
              end

            8'd11:
            begin
              if(cipherType > 3'd1)
              begin
                debug_valid         <= 1'b1;
                if(!rxCsIsIdle)
                  debug_lsh_reg[31:0] <= rxTkipSeqCntr[31:0];
                else
                  debug_lsh_reg[31:0] <= txTkipSeqCntr[31:0];
              end
            end

            8'd19:
            begin
              if(cipherType > 3'd1)
              begin
                debug_valid         <= 1'b1;
                if(!rxCsIsIdle)
                  debug_lsh_reg[31:0] <= {16'h0,rxTkipSeqCntr[47:32]};
                else
                  debug_lsh_reg[31:0] <= {16'h0,txTkipSeqCntr[47:32]};
              end
            end

            8'd23:
            begin
              debug_valid         <= 1'b0;
            end
 
            8'd24:
            begin
              debug_lsh_reg[31:0] <= {cryptoKey[31:0]};
              debug_valid         <= 1'b1;
            end

            8'd32:
            begin
              debug_lsh_reg[31:0] <= {cryptoKey[63:32]};
              debug_valid         <= 1'b1;
            end

            8'd40:
            begin
              if(cipherType > 3'd1)
              begin
                debug_lsh_reg[31:0] <= {cryptoKey[95:64]};
                debug_valid         <= 1'b1;
              end
            end

            8'd41:
            begin
              debug_lsh_reg        <= {4'h0,debug_lsh_reg[31:4]};
              debug_valid          <= cipherLen;
            end

            8'd48:
            begin
              if(cipherType > 3'd1)
              begin
                debug_lsh_reg[31:0] <= {cryptoKey[127:96]};
                debug_valid         <= cipherLen;
              end
            end

            8'd56:
            begin
              debug_valid          <= 1'b0;
            end

            default : 
            begin
              debug_lsh_reg <= {4'h0,debug_lsh_reg[31:4]};
              debug_valid   <= debug_valid;
            end
          endcase
        end
        else
        begin
          debug_lsh_reg                      <=  32'h0;
          debug_valid                        <=   1'b0;
        end
      end
      // Idle
      else
      begin
        debug_cnt                         <=   8'h0;
        debug_lsh_reg                     <=  32'h0;
        debug_valid                       <=   1'b0;
      end
    end
  end
endmodule
