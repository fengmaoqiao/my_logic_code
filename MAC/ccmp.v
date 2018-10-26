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
//   This block is the top level module for ccmp implementation. this module
//   instantiates  the ccm,ccmInReg and ccmOutReg blocks and also include
//   AAD and NONCE construction logic
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
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

module ccmp (

  //$port_g Inputs
  input  wire         macCoreClk,         // macCore clock signal (freerunning clock)
  input  wire         macCryptClk,        // macCrypt clock signal (gated clock for crypto engine)
  input  wire         nPRst,              // reset signal from hardware
  input  wire         nSRst,              // reset signal from software
  input  wire         rxCsIsIdle,         // Indicates that receive state machine is idle
  input  wire         txCsIsIdle,         // Indicates that transmit state machine is idle
  input  wire         initCCMP_p,         // initialization trigger pulse for CCMP
  input  wire         wrCCMPEn_p,         // write enable signal to CCMP input register
  input  wire         payloadEnd_p,       // pulse indicating end of payload
  input  wire         txRxBufferFull,     // indicates that CCMP transmit buffer/receive FIFO is full

  input  wire         rxError_p,          // pulse indicating an error has been encountered during reception
  
  input  wire         micEnd,             // Indicates MIC has been written during reception
  input  wire [127:0] temporalKey,        // temporal key to be used for encryption/decryption
  input  wire  [15:0] tcPayloadLen,       // Length of the payload in bytes in case of Transmit.
  input  wire  [15:0] rcPayloadLen,       // Length of the payload in bytes in case of Receive.
  input  wire   [7:0] plainText,          // plain text to be encrypted
  input  wire   [7:0] dataFromBuffer,     // received data to be decrypted
  input  wire         popDataOutBuffer_p, // Indicates Read of CCMP Buffer.

  input  wire  [47:0] tcDestId,           // Destination ID field of the MAC Header in case of Tx.
  input  wire  [47:0] tcSourceId,         // Source ID field of the MAC Header in case of Tx.
  input  wire  [47:0] tcSfc,              // SFC Tx field of the MAC Frame payload in case of Tx.
  input  wire         tcTxErrorP,         // tx Error

  input  wire  [47:0] rcDestId,           // Destination ID field of the MAC Header in case of Rx.
  input  wire  [47:0] rcSourceId,         // Source ID field of the MAC Header in case of Rx.
  input  wire  [47:0] rcSfc,              // SFC Rx field of the MAC Frame payload in case of Rx.

  input  wire         txAddress4Pres,     // Tx flag indicating address 4 is present
  input  wire         rxAddress4Pres,     // Rx flag indicating address 4 is present
  input  wire         txQoSFrame,         // Tx flag indicating the current frame is a QoS Frame
  input  wire         rxQoSFrame,         // Rx flag indicating the current frame is a QoS Frame
  input  wire [3:0]   txTID,              // Tx priority information for QoS frames
  input  wire [3:0]   rxTID,              // Rx priority information for QoS frames
  input  wire         txQoS7,             // HT spp Tx QoS bit 7
  input  wire         rxQoS7,             // HT spp Rx QoS bit 7
  input  wire         ccmpHTMode,         // HT Mode
  input  wire [1:0]   sppKSR,             // HT A MSDU Capability

  //$port_g Outputs
  output wire         stopPopFromBuffer,  // Stop reading data from buffer
  output wire [ 7:0]  ccmpOutData,        // output data from the CCMP block
  output wire         ccmpOutValid_p,     // pulse indicating valid data present on the ccmpOutData lines
  output wire         ccmpOutLast_p,      // Last data from CCMP
  output wire         ccmpRegFull,        // flag indicating CCMP input register is full
  output wire         nextccmpRegFull,    // flag indicating CCMP input register is full
  output wire         ccmp_isIdle,        // Indicate CCMP is IDLE
  output wire         micValid_p,         // pulse indicating Mic calculation done
  output wire         micPassed_p,        // pulse indicating MIC check successful
  output wire         micFailed_p,         // pulse indicating MIC check failed
  output wire [ 3:0]  ccmp_cntlCS         // ccmp current state
  );

// ------------------ Register declarations ------
  reg [127:0]       aadOne;
  reg [7:0]         aadLen;
  reg [15:0]        fcMuted;
  reg               micPass;
  reg               micFail;
  reg               nextmicPass;
  reg               nextmicFail;
  reg               rxMICPending;
  reg               qos_7;

// ------------------------ Wire Declarations ------------------------
  wire [255:0] aad;
  wire [127:0] aadTwo;
  wire [127:0] ccmInData;
  wire [127:0] ccmOutData;
  wire [127:0] maskReg;
  wire [3:0]   tid;
  wire [3:0]   maskedtid;
  wire [103:0] nonce;
  wire [63:0]  mic;
  wire [47:0]  sfc;            
  wire [47:0]  destId;
  wire [47:0]  sourceId;         
  wire [15:0]  payloadLen;       
  wire         ccmpOutValid;
  wire         outRegEmpty;
  wire         aadReady;
  wire         loadMsg_p;
  wire         ccmInValid;
  wire         aadValid;
  wire         payloadEndOut_p;
//  wire         micValid_p;  
  wire         micEndOut;  
  wire         loadAAD2_p;
  wire         imicPassed_p;
  wire         imicFailed_p;
  wire         address4Pres;
  wire         qosFrame;
  wire         fc_15;
  wire         qos_7saved;

//-------------------------Instantiation of ccmpInreg -----------------

  ccmpInReg U_ccmpInReg (

// Inputs
  .pClk               (macCoreClk),
  .nPRst              (nPRst),
  .nSRst              (nSRst),
  .rxCsIsIdle         (rxCsIsIdle),
  .txCsIsIdle         (txCsIsIdle),
  .wrCCMPEn_p         (wrCCMPEn_p),
  .address4Pres       (address4Pres),
  .rxError_p          (rxError_p),
  .tcTxErrorP         (tcTxErrorP),
  .payloadEnd_p       (payloadEnd_p),
  .micEnd             (micEnd),
  .dataFromBuffer     (dataFromBuffer),
  .plainText          (plainText),
  .loadMsg_p          (loadMsg_p),
  .loadAAD2_p         (loadAAD2_p),
  .rxMICPending       (rxMICPending),
  .popDataOutBuffer_p (popDataOutBuffer_p),

// Outputs
  .stopPopFromBuffer  (stopPopFromBuffer), 
  .ccmInData          (ccmInData),
  .ccmInValid         (ccmInValid),
  .aadValid           (aadValid),
  .payloadEndOut_p    (payloadEndOut_p),
  .micEndOut          (micEndOut),
  .ccmpRegFull        (ccmpRegFull),
  .nextccmpRegFull    (nextccmpRegFull),
  .maskReg            (maskReg),
  .aadReady           (aadReady)
  );

//-------------------------- Instantiation of ccm ---------------------

  ccm U_ccm (

// Inputs
  .pClk          (macCryptClk),
  .nPRst         (nPRst),
  .nSRst         (nSRst),
  .initCCM_p     (initCCMP_p),
  .payloadEnd_p  (payloadEndOut_p),
  .ccmInValid    (ccmInValid),
  .rxCsIsIdle    (rxCsIsIdle),
  .rxError_p     (rxError_p),
  .tcTxErrorP    (tcTxErrorP),
  .micEndOut     (micEndOut),
  .aad           (aad),
  .aadValid      (aadValid),
  .nonce         (nonce),
  .payloadLen    (payloadLen),
  .key           (temporalKey),
  .ccmInData     (ccmInData),
  .maskReg       (maskReg),
  .outRegEmpty   (outRegEmpty),

// Outputs
  .micValid_p    (micValid_p),
  .loadMsg_p     (loadMsg_p),
  .ccmp_isIdle   (ccmp_isIdle),
  .ccmOutData    (ccmOutData),
  .mic           (mic),
  .loadAAD2_p    (loadAAD2_p),
  .micPassed_p   (imicPassed_p),
  .micFailed_p   (imicFailed_p),
  .ccmp_cntlCS   (ccmp_cntlCS)
  );

// ---------------------- Instantiation of ccmpOutReg -----------------

  ccmpOutReg U_ccmpOutReg (

// Inputs

  .pClk(macCryptClk),
  .nPRst(nPRst),
  .nSRst(nSRst),
  .rxCsIsIdle(rxCsIsIdle),
  .payloadEnd_p(payloadEndOut_p),
  .payloadLen(payloadLen[3:0]),
  .micValid_p(micValid_p),
  .rxError_p(rxError_p),
  .tcTxErrorP(tcTxErrorP),
  .mic(mic),
  .ccmOutData(ccmOutData),
  .ccmOutValid_p(loadMsg_p),
  .txRxBufferFull(txRxBufferFull),

// Outputs

  .ccmpOutValid(ccmpOutValid),
  .ccmpOutData(ccmpOutData),
  .ccmpOutLast_p(ccmpOutLast_p)   
  );

// Logic for payloadLen. If rxControl is in IDLE state, the payloadLen takes 
// the value of tcPayloadLen, otherwise takes the value of rcPayLoadLen.
  assign payloadLen = rxCsIsIdle ? tcPayloadLen : rcPayloadLen;

// Constuct AAD/Nonce From Data 

// Logic for destId. If rxControl is in IDLE state, the destId takes the value 
// of tcDestId, otherwise takes the value of rcDestId.
  assign destId = rxCsIsIdle ? tcDestId : rcDestId;

// Logic for sourceId. If rxControl is in IDLE state, the sourceId takes 
// the value of tcSourceId, otherwise takes the value of rcSourceId.
  assign sourceId = rxCsIsIdle ? tcSourceId : rcSourceId;

// Logic for sfc. If rxControl is in IDLE state, the sfc takes the value of 
// tcSfc, otherwise takes the value of rcSfc.
  assign sfc = rxCsIsIdle ? tcSfc : rcSfc;

// Logic for address4Pres. If rxControl is in IDLE state, the address4Pres
// takes the value of txAddress4Pres, otherwise takes the value of rxAddress4Pres.
  assign address4Pres = rxCsIsIdle ? txAddress4Pres : rxAddress4Pres;

// Logic for qosFrame. If rxControl is in IDLE state, the qosFrame takes the
//  value of txQoSFrame, otherwise takes the value of rxQoSFrame.
  assign qosFrame = rxCsIsIdle ? txQoSFrame : rxQoSFrame;

// Logic for tid
// tid going to ccmp block is multiplexed between transmit tid 
// and received tid based on rxCsIsIdle 

  assign tid   = (rxCsIsIdle) ? txTID  : rxTID;

// Constuct AAD/Nonce From Data 

  assign  aadTwo = {destId, sourceId, fcMuted, aadLen, 8'h00};

  assign  aad    = {aadTwo, aadOne};

// HT QoS FC bit 15 masking
  assign  fc_15  = (ccmpHTMode && qosFrame) ? 1'b0 : ccmInData[15];

// HT SSP Capable QoS bit 7 Filter
  assign qos_7saved = (rxCsIsIdle) ? txQoS7 : rxQoS7;

  always @(posedge macCoreClk,negedge nPRst)
  begin
    if(nPRst == 1'b0)
    begin
      qos_7         <= 1'b0;
    end
    else if(nSRst == 1'b0)
    begin
      qos_7         <= 1'b0;
    end
    else
    begin
      if(initCCMP_p)
      begin
        if(ccmpHTMode && qosFrame && (sppKSR == 2'b10)) 
          qos_7 <= qos_7saved;
        else
          qos_7 <= 1'b0;
      end
      else if(!aadReady)
        qos_7 <= 1'b0;
    end
  end

  always @*
  begin
    fcMuted = {fc_15, 1'b1, 3'b000, ccmInData[10:7], 3'b000,ccmInData[3:0]};
    if (address4Pres && qosFrame)
    begin
      aadLen = 8'h1e;
      aadOne = {8'b0,{qos_7,3'b0}, maskedtid, ccmInData[127:80], {12'h00, ccmInData[67:64]},ccmInData[63:16]};
    end
    else if (address4Pres)
    begin
      aadLen = 8'h1c;
      aadOne = {16'b0,ccmInData[127:80],{12'h00, ccmInData[67:64]},ccmInData[63:16]};
    end
    else if (qosFrame)
    begin
      aadLen = 8'h18;
      aadOne = {56'b0,{qos_7,3'b0},maskedtid,{12'h00, ccmInData[67:64]},ccmInData[63:16]};
    end
    else
    begin
      aadLen = 8'h16;
      aadOne = {64'b0,{12'h00, ccmInData[67:64]},ccmInData[63:16]};
    end
  end


  assign maskedtid = tid & {qosFrame,qosFrame,qosFrame,qosFrame};

//nonce
  assign nonce     = {sfc,destId,4'h0,maskedtid};

// outRegEmpty
  assign outRegEmpty = ~ccmpOutValid;

// Combinational logic for Mic generation
  always @*
  begin
    if (micValid_p)
    begin
      nextmicPass = imicPassed_p;
      nextmicFail = imicFailed_p;
    end
    else if ((ccmpOutValid == 1'b0) || rxError_p || tcTxErrorP )
    begin
      nextmicPass = 1'b0;
      nextmicFail = 1'b0;
    end
    else
    begin
      nextmicPass = micPass;
      nextmicFail = micFail;
    end
  end

//micPassed_p 
  assign micPassed_p = imicPassed_p & !ccmpOutValid; 
//micFailed_p
  assign micFailed_p = imicFailed_p & !ccmpOutValid; 

// Sequential logic for MIC generation
  always@(posedge macCryptClk or negedge nPRst)
  begin
    if (nPRst == 1'b0)
    begin
      micPass  <= 1'b0;
      micFail  <= 1'b0;
    end
    else if(nSRst == 1'b0)
    begin
      micPass  <= 1'b0;
      micFail  <= 1'b0;
    end
    else
    begin
      micPass  <= nextmicPass;
      micFail  <= nextmicFail;
    end
  end

  always @(posedge macCryptClk or negedge nPRst)
  begin
    if (nPRst == 1'b0)
      rxMICPending <= 1'b0;
    else if(nSRst == 1'b0)
      rxMICPending <= 1'b0;
    else if (tcTxErrorP || rxError_p || micPassed_p || micFailed_p)
      rxMICPending <= 1'b0;
    else if (payloadEndOut_p && ~(rxCsIsIdle))
      rxMICPending <= 1'b1;
    else
      rxMICPending <= rxMICPending;
  end

// Mask the ccmpOutValid if the ccmp transmit buffer / receive FIFO is full
  assign ccmpOutValid_p  = ccmpOutValid & ~(txRxBufferFull); 

endmodule

//---- END OF FILE  ------//
