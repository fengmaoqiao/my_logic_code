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

module ccmpTop (

  //$port_g Inputs
  input wire macCoreClk,          // macCore clock signal (freerunning clock)
  input wire macCryptClk,         // macCrypt clock signal (gated clock for crypto engine)
  input wire nPRst,               // Hard Reset input synchronised to MAC clock
  input wire nSRst,               // Soft Reset input synchronised to MAC clock  

  input wire rcRxCsIsIdle,        // Indicates that the rxController is IDLE 
  input wire tcTxCsIsIdle,        // Indicates that the txController is IDLE 
  input wire initCCMP_p,          // Initialization trigger pulse for CCMP
  input wire tcTxCCMPWrEnP,       // Write enable signal from TX Controller
  input wire rxCCMPDataWrEn_p,    // Write enable signal from Encr RX Controller

  input wire tcTxPayLdEndP,       // Pulse indicating end of TX payload
  input wire rxpayloadEnd_p,      // Indicates that last byte of RX payload

  input wire nullKeyFound,        // Signal indicating key not found 

  input wire popDataOutBuffer_p,  // pulse to pop data from buffer in case of Rx.

  input wire [7:0] tcPlainText,   // Data to be written into buffer in case of Tx

  input wire tcTxErrorP,          // Pulse to indicate error in transmission.
  input wire [7:0] dataFromBufferReg, // The data being Read from the CCMP buffer 

  input wire rxError_p,           // Signal to flush the Encr. Rx Buffer 

  input wire [15:0] tcPayloadLen, // Length of the payload in bytes in case of TX.
  input wire [15:0] rcPayloadLen, // Length of the payload in bytes in case of RX.

  input wire [47:0] tcDestId,      // Destination ID field of the MAC Header in case of Tx.
  input wire [47:0] tcSourceId,    // Source ID field of the MAC Header in case of Tx.
  input wire [47:0] tcSfc,         // SFC Tx field of the MAC Frame payload in case of Tx.

  input wire [47:0] rcDestId,      // Destination ID field of the MAC Header in case of Rx.
  input wire [47:0] rcSourceId,    // Source ID field of the MAC Header in case of Rx.
  input wire [47:0] rcSfc,         // SFC Rx field of the MAC Frame payload in case of Rx.

  input wire txAddress4Pres,       // Tx flag indicating address 4 is present
  input wire rxAddress4Pres,       // Rx flag indicating address 4 is present
  input wire txQoSFrame,           // Tx flag indicating the current frame is a QoS Frame
  input wire rxQoSFrame,           // Rx flag indicating the current frame is a QoS Frame
  input wire [3:0]  txTID,         // Tx priority information for QoS frames
  input wire [3:0]  rxTID,         // Rx priority information for QoS frames
  input wire        txQoS7,        // HT spp Tx QoS bit 7
  input wire        rxQoS7,        // HT spp Rx QoS bit 7

  input wire        ccmpHTMode,    // HT Mode
  input wire [1:0]  sppKSR,        // HT A MSDU Capability

  input wire [127:0] temporalKey,  // CCMP key to be used for encryption/decryption

  input wire txRxBufferFull,       // flag to indicate encryption buffer full
  input wire micEnd,               // Indication of MIC write completion

  //$port_g Outputs
  output wire [7:0] ccmpOutDataMux, // Output data bus from CCMP engine
  output wire ccmpOutValidMux_p,    // Valid signal for the output CCMP data 
  output wire ccmpOutLastMux_p,     // Last data from CCMP

  output wire stopPopFromBuffer,    // Flow control signal to stop reading
  output wire ccmpRegFull,     // flag indicating CCMP input register is full
  output wire nextccmpRegFull, // flag indicating CCMP input register is almost full
  output wire ccmp_isIdle,     // Indicate CCMP is IDLE
  output wire micValid_p,      // pulse indicating Mic calculation done
  output wire micPassed_p,     // pulse indicating MIC check successful
  output wire micFailed_p,     // pulse indicating MIC check failed
  output wire [3:0] ccmp_cntlCS// FSM
  );


//------------------------------ Internal Wire declarations ----------------------
  wire [7:0]   ccmpOutData;     
  wire         ccmpOutValid_p;
  wire         ccmpOutLast_p;
  wire         wrCCMPEnP;
  wire         payloadEnd_p;

//---------------------INTERNAL-----------------------
//  wire [15:0]  encryptOff;
//  wire         eoZero;

//------------------- Sub-module Instantiations starts here --------------------

  ccmpMux u_ccmpMux (
  .rxCsIsIdle        (rcRxCsIsIdle),        
  .tcTxCCMPWrEnP     (tcTxCCMPWrEnP),
  .rxCCMPDataWrEn_p  (rxCCMPDataWrEn_p),
  .tcTxPayLdEndP     (tcTxPayLdEndP),
  .rxpayloadEnd_p    (rxpayloadEnd_p),
  .nullKeyFound      (nullKeyFound),
  .ccmpOutData       (ccmpOutData),     
  .ccmpOutValid_p    (ccmpOutValid_p),  
  .ccmpOutLast_p     (ccmpOutLast_p),  
  .cbReadData        (dataFromBufferReg),

  .wrCCMPEnP         (wrCCMPEnP),
  .payloadEnd_p      (payloadEnd_p),
  .ccmpOutDataMux    (ccmpOutDataMux),    
  .ccmpOutValidMux_p (ccmpOutValidMux_p),
  .ccmpOutLastMux_p  (ccmpOutLastMux_p)  
  );                  

  ccmp u_ccmp (
  .macCoreClk         (macCoreClk),
  .macCryptClk        (macCryptClk),
  .nPRst              (nPRst),
  .nSRst              (nSRst),
  .rxCsIsIdle         (rcRxCsIsIdle),
  .txCsIsIdle         (tcTxCsIsIdle),
  .initCCMP_p         (initCCMP_p),
  .wrCCMPEn_p         (wrCCMPEnP),
  .payloadEnd_p       (payloadEnd_p),
  .txRxBufferFull     (txRxBufferFull),     
  .rxError_p          (rxError_p),          
  .micEnd             (micEnd),             
  .temporalKey        (temporalKey),        
  .tcPayloadLen       (tcPayloadLen),         
  .rcPayloadLen       (rcPayloadLen),         
  .plainText          (tcPlainText),          
  .dataFromBuffer     (dataFromBufferReg),     
  .popDataOutBuffer_p (popDataOutBuffer_p), 
  .tcDestId           (tcDestId),           
  .tcSourceId         (tcSourceId),         
  .tcSfc              (tcSfc),              
  .tcTxErrorP         (tcTxErrorP),
  .rcDestId           (rcDestId),           
  .rcSourceId         (rcSourceId),         
  .rcSfc              (rcSfc),
  .txAddress4Pres     (txAddress4Pres),
  .rxAddress4Pres     (rxAddress4Pres),
  .txQoSFrame         (txQoSFrame),
  .rxQoSFrame         (rxQoSFrame),
  .txTID              (txTID),
  .rxTID              (rxTID),
  .txQoS7             (txQoS7),
  .rxQoS7             (rxQoS7),
  .ccmpHTMode         (ccmpHTMode),
  .sppKSR             (sppKSR),
  .stopPopFromBuffer  (stopPopFromBuffer),
  .ccmpOutData        (ccmpOutData),     
  .ccmpOutValid_p     (ccmpOutValid_p),
  .ccmpOutLast_p      (ccmpOutLast_p),
  .ccmpRegFull        (ccmpRegFull),      
  .nextccmpRegFull    (nextccmpRegFull),  
  .ccmp_isIdle        (ccmp_isIdle),
  .micValid_p         (micValid_p),
  .micPassed_p        (micPassed_p),    
  .micFailed_p        (micFailed_p),
  .ccmp_cntlCS        (ccmp_cntlCS)
  );

endmodule
//---- END OF FILE  ------//
