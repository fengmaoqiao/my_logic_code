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
//   This block is implements the mix column operation for Aes core
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


module aesMixColumn (

    //$port_g aesCore
    input  wire [31:0]   wordin, // Mix Colunm input

    output reg  [31:0]   wordout // Mix Colunm input

 );

//------------------------ Reg Declarations ------------------------
reg  [7:0]  BYTE0M3;
reg  [7:0]  BYTE1M3;
reg  [7:0]  BYTE2M3;
reg  [7:0]  BYTE3M3;
reg  [7:0]  BYTE0M2;
reg  [7:0]  BYTE1M2;
reg  [7:0]  BYTE2M2;
reg  [7:0]  BYTE3M2;
    
// Function for Multiply By 2 
function [7:0] BYTEVAL;
  input [7:0] wordin;
   BYTEVAL   = {wordin[6:4], wordin[3] ^ wordin[7], wordin[2] ^ wordin[7],
             wordin[1], wordin[0] ^ wordin[7], wordin[7]};
endfunction

// ----------------------- Logic Begins ----------------------------

// Multiply all the bytes by  2
always@(wordin)
begin
  BYTE0M2 = BYTEVAL(wordin[7:0]);
  BYTE1M2 = BYTEVAL(wordin[15:8]);
  BYTE2M2 = BYTEVAL(wordin[23:16]);
  BYTE3M2 = BYTEVAL(wordin[31:24]);
end
  
// Multiply all the bytes by  3
always @(BYTE0M2 or BYTE1M2 or BYTE2M2 or BYTE3M2 or wordin)
begin
  BYTE0M3   = BYTE0M2 ^ wordin[7:0];
  BYTE1M3   = BYTE1M2 ^ wordin[15:8];
  BYTE2M3   = BYTE2M2 ^ wordin[23:16];
  BYTE3M3   = BYTE3M2 ^ wordin[31:24];
end

// byte transformation
always@(BYTE0M2 or BYTE1M2 or BYTE2M2 or BYTE3M2 or BYTE1M3 or BYTE2M3 or
        BYTE3M3 or BYTE0M3 or wordin)
begin
  wordout[7:0]   = BYTE0M2 ^ BYTE1M3 ^ wordin[23:16] ^ wordin[31:24];
  wordout[15:8]  = BYTE1M2 ^ BYTE2M3 ^ wordin[7:0]^ wordin[31:24];
  wordout[23:16] = BYTE2M2 ^ BYTE3M3 ^ wordin[15:8] ^ wordin[7:0];
  wordout[31:24] = BYTE3M2 ^ BYTE0M3 ^ wordin[15:8] ^ wordin[23:16];
end

endmodule

//------------------- END OF FILE ----------------//
