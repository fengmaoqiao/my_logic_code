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
//   This module asynchronously XORes the two inputs and places it on the output
//   lines.
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

module asyncXor(

    //$port_g Inputs
    data1ToXor,   // first input
    data2ToXor,   // second input

    //$port_g Outputs
    dataFromXor   // output

    );

//--------------------- inputs declared ------------------

input [7:0] data1ToXor;
input [7:0] data2ToXor;

//--------------------- outputs declared ------------------

output [7:0] dataFromXor;

//--------------------- inputs declared as wires ------------------

wire [7:0] data1ToXor;
wire [7:0] data2ToXor;

//--------------------- outputs declared as registers -------------------

reg [7:0] dataFromXor;

always @(data1ToXor or data2ToXor)
  dataFromXor = data1ToXor ^ data2ToXor;

endmodule
//------------------- END OF FILE ----------------//
