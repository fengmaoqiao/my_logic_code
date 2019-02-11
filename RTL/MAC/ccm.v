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
// Dependencies     : 
// Description      : 
//   This block is the top level module for ccm implementation. this module 
//   instantiates  the ccmCntl and aesCore blocks
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


module ccm (

  //$port_g Inputs
  input  wire         pClk,        // baseband clock signal
  input  wire         nPRst,       // reset signal from hardware
  input  wire         nSRst,       // reset signal from software
  input  wire         initCCM_p,   // initialization trigger
  input  wire         payloadEnd_p,// Indicates that pay load End
  input  wire         ccmInValid,  // Data input is valid in input reg
  input  wire [127:0] maskReg,     // Data to CCM block
  input  wire         rxCsIsIdle,  // Encrypt/Decrypt flag
  input  wire         rxError_p,   // Indicates that Rx error has occured
  input  wire         tcTxErrorP,  // tx Error
  input  wire         micEndOut,   // Indicate MIC End
  input  wire [255:0] aad,         // AAD Input to the CCM block
  input  wire         aadValid,    // Indicates that AAD is valid
  input  wire [103:0] nonce,       // nonce input to the CCM block
  input  wire [15:0]  payloadLen,  // length of the pay load in bytes
  input  wire [127:0] key,         // Key to CCM
  input  wire [127:0] ccmInData,   // Data to CCM block
  input  wire         outRegEmpty, // Indicates buffer is full

  //$port_g Outputs
  output wire         micValid_p,     // Indicates that MIC is valid
  output wire         loadMsg_p,      // Read to CCMP in register
  output wire [127:0] ccmOutData,     // CCM output data to output reg
  output wire  [63:0] mic,            // MIC output
  output wire         loadAAD2_p,     // AAD read
  output wire         ccmp_isIdle,    // Indicate CCMP is IDLE
  output wire         micPassed_p,    // Mic pass pulse
  output wire         micFailed_p,     // Mic fail pulse
  output wire  [3:0]  ccmp_cntlCS     // CCMP Current State
  );

  wire         aes_crt_in_valid;
  wire [127:0] aes_crt_in;
  wire         aes_crt_out_valid;
  wire [127:0] aes_crt_out;
  wire         aes_mic_in_valid;
  wire [127:0] aes_mic_in;
  wire         aes_mic_out_valid;
  wire [127:0] aes_mic_out;

  wire         alwaysZero;
//  wire         alwaysOne;

  assign alwaysZero = 1'b0;
//  assign alwaysOne  = 1'b1;

  aesCore u_aes_crt ( 
  .pClk(pClk),
  .nPRst(nPRst),
  .nSRst(nSRst),
  .rxError_p(rxError_p),
  .tcTxErrorP(tcTxErrorP),
  .aesKey(key),
  .loadFlag(alwaysZero),

  .aesInValid(aes_crt_in_valid),
  .aesInData(aes_crt_in),

  .aesOutValid_p(aes_crt_out_valid),
  .aesOutData(aes_crt_out)
  ); 

  `ifdef RW_AES_AC
  aesCore u_aes_mic (
  `else
  aesCore_mic u_aes_mic (
  `endif 
  .pClk(pClk),
  .nPRst(nPRst),
  .nSRst(nSRst),
  .rxError_p(rxError_p),
  .tcTxErrorP(tcTxErrorP),
  .aesKey(key),
  .loadFlag(alwaysZero),

  .aesInValid(aes_mic_in_valid),
  .aesInData(aes_mic_in),

  .aesOutValid_p(aes_mic_out_valid),
  .aesOutData(aes_mic_out)
  ); 

  ccmCntl  u_ccmp_cntl (
  .ccmp_clk          (pClk),
  .ccmp_hardrst_n    (nPRst),
  .ccmp_softrst_n    (nSRst),

  .aes_mic_out_valid (aes_mic_out_valid),
  .aes_mic_out       (aes_mic_out),

  .aes_mic_in_valid  (aes_mic_in_valid),
  .aes_mic_in        (aes_mic_in),

  .aes_crt_out_valid (aes_crt_out_valid),
  .aes_crt_out       (aes_crt_out),

  .aes_crt_in_valid  (aes_crt_in_valid),
  .aes_crt_in        (aes_crt_in),

  .ccmp_tx_nrx       (rxCsIsIdle),
  .ccmp_init_p       (initCCM_p),
  .ccmp_aadValid     (aadValid),
  .ccmp_outRegEmpty  (outRegEmpty),
  .ccmp_rxError_p    (rxError_p),
  .ccmp_txError_p    (tcTxErrorP),
  .ccmp_lastpayload  (payloadEnd_p),
  .ccmp_micend       (micEndOut),

  .ccmp_aad          (aad),
  .ccmp_nonce        (nonce),
  .ccmp_payloadLen   (payloadLen),
  .ccmp_data_out_mask(maskReg),

  .ccmp_loadAAD2     (loadAAD2_p),
  .ccmp_loadMSG      (loadMsg_p),
  .ccmp_isIdle       (ccmp_isIdle),

  .ccmp_data_in_valid(ccmInValid),

  .ccmp_data_in      (ccmInData),
  .ccmp_data_out     (ccmOutData),

  .ccmp_mic_failed   (micFailed_p),
  .ccmp_mic_passed   (micPassed_p),
  .ccmp_mic_valid    (micValid_p),
  .ccmp_mic          (mic),
  .ccmp_cntlCS       (ccmp_cntlCS)
  );

endmodule

//------------------- END OF FILE ----------------//
