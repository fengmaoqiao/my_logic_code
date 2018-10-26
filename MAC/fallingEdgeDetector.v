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


module fallingEdgeDetector( 
         input  wire      dstclk,
         input  wire      dstresetn,
         input  wire      srcdata,
         //  
         output wire      dstdata

                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
reg src_resync;
reg dst_ff1;
reg dst_ff2;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign   dstdata  = (dst_ff2 == 1'b1 && dst_ff1 == 1'b0) ? 1'b1 : 1'b0;

// resynchronize data
always @ (posedge dstclk or negedge dstresetn) 
begin
  if ( dstresetn == 1'b0)  // Asynchronous Reset
  begin
    src_resync <= 1'b0;
    dst_ff1    <= 1'b0;
    dst_ff2    <= 1'b0;
  end
  else
  begin
    src_resync <= srcdata;
    dst_ff1    <= src_resync;
    dst_ff2    <= dst_ff1;
  end
end






endmodule
                 
