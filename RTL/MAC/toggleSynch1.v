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
//   This module is used when any signal generated in one clock domain has to be
//   shifted to any other clock domain. The input signal should be a pulse.
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

module toggleSynch1 (

  //$port_g Inputs
  input  wire genClk,            // generating clock
  input  wire synClk,            // synchronizing clock
  input  wire hardReset_n,       // reset input
  input  wire dataIn,            // input to be synchronized
  
  //$port_g Outputs
  output wire dataOut            // synchronized output
  );


  wire input_D1;
  reg  output_Q1;

  reg  output_Q2;
  reg  output_Q3;
  reg  output_Q4;

  assign input_D1 = dataIn ^ output_Q1; 

  always @(posedge genClk or negedge hardReset_n) begin
    if(!hardReset_n)
      output_Q1<= 1'b0;
    else
      output_Q1 <= input_D1; 
  end

  always @(posedge synClk or negedge hardReset_n) begin
    if(!hardReset_n)
      output_Q2 <= 1'b0;
    else
      output_Q2 <= output_Q1;
  end


  always @(posedge synClk or negedge hardReset_n) begin
    if(!hardReset_n)
      output_Q3 <= 1'b0;
    else
      output_Q3 <= output_Q2;
  end


  always @(posedge synClk or negedge hardReset_n) begin
    if(!hardReset_n)
      output_Q4 <= 1'b0;
    else
      output_Q4 <= output_Q3;
  end

  assign dataOut = output_Q4 ^ output_Q3;

endmodule
