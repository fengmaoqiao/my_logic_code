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
//   This block implements the sBox table for TKIP phase I and phase II key
//   mixing functions.
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


module sBoxTKIP (
      //$port_g Inputs
      bbClk,          // baseband clock
      hardRstBbClk_n, // reset signal from hardware
      sBoxAddressA,   // index for sBox table A
      sBoxAddressB,   // index for sBox table B

      //$port_g Outputs
      sBoxDataA,      // sBox table A value
      sBoxDataB       // sBox table B value
    );

  //------------------Inputs------------------------------------------
  input                                       bbClk;
  input                                       hardRstBbClk_n;
  input [7:0]                                 sBoxAddressA;
  input [7:0]                                 sBoxAddressB;

  //-----------------Outputs------------------------------------------
  output [15:0]                               sBoxDataA;
  output [15:0]                               sBoxDataB;

  //------------------reg---------------------------------------------

  reg    [15:0]                               sBoxDataA;
  reg    [15:0]                               sBoxDataB;

  //------------------wire--------------------------------------------
  
  wire                                        bbClk;
  wire                                        hardRstBbClk_n;
  wire   [7:0]                                sBoxAddressA;
  wire   [7:0]                                sBoxAddressB;
  wire   [15:0]                               nxtsBoxDataA;
  wire   [15:0]                               nxtsBoxDataB;
  wire   [7:0]                                sBox8bitDataA;
  wire   [7:0]                                sBox8bitDataB;
  wire   [7:0]                                tmpk2A;
  wire   [7:0]                                k2A;
  wire   [7:0]                                k3A;
  wire   [7:0]                                tmpk2B;
  wire   [7:0]                                k2B;
  wire   [7:0]                                k3B;


   
  //--------------Logic Begins----------------------------------------

// Logic for sBox A
aesSBox U1_aesSBox (
                    .inData (sBoxAddressA),
                    .outData (sBox8bitDataA)
                   );

aesSBox U2_aesSBox (
                    .inData (sBoxAddressB),
                    .outData (sBox8bitDataB)
                   );

// Logic to generate 16 bit data from 8-bit sbox output for sBox A
assign tmpk2A = (sBox8bitDataA[7] == 1'b1) ? 8'h1B : 8'h00;

assign k2A = {sBox8bitDataA[6:0], 1'b0} ^ tmpk2A;

assign k3A = sBox8bitDataA ^ k2A;

assign nxtsBoxDataA = {k2A,k3A};

// Logic to generate 16 bit data from 8-bit sbox output for sBox B
assign tmpk2B = (sBox8bitDataB[7] == 1'b1) ? 8'h1B : 8'h00;

assign k2B = {sBox8bitDataB[6:0], 1'b0} ^ tmpk2B;

assign k3B = sBox8bitDataB ^ k2B;

assign nxtsBoxDataB = {k3B,k2B};


// Sequential logic for sBox values
always @(posedge bbClk or negedge hardRstBbClk_n)
begin
  if (!hardRstBbClk_n)
    begin
      sBoxDataA <= 16'h0000;
      sBoxDataB <= 16'h0000;
    end
  else
    begin
      sBoxDataA   <= nxtsBoxDataA;
      sBoxDataB   <= nxtsBoxDataB;
    end
end

endmodule

//------------------- END OF FILE ----------------//
      
