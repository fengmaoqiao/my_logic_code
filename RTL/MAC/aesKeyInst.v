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
//   Implements the XOR logic for Key generation .
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

module aesKeyInst (

  //$port_g Clocks Resets
  input  wire         pClk,           // baseband clock signal
  input  wire         nPRst,          // reset
  input  wire         nSRst,          // reset software
  
  //$port_g aesKeyGenTop
  input  wire         enable,
  input  wire [31:0]  muxedKey,       // Input key
  input  wire [31:0]  xorIn,          // From KeyGenTop After SBOX,ROTWORD,Rcon

  output wire [31:0] nexttempKeyReg,  // To Key Gen block for next instance
  output reg  [31:0] tempKeyReg       // Final Key to be used
 );


// ------------------------ Logic Begins ----------------------------

// Input Xor Logic for Muxed OutPut 
assign nexttempKeyReg = xorIn ^ muxedKey;

// Sequntial logic for The tempKeyReg 
always@(posedge pClk or negedge nPRst)
begin
  if(nPRst == 1'b0) 
    tempKeyReg <= 32'h0000_0000;
  else if (nSRst == 1'b0)
    tempKeyReg <= 32'h0000_0000;
  else if(enable == 1'b1) 
    tempKeyReg <= nexttempKeyReg;
end
endmodule 

//------------------- END OF FILE ----------------//
