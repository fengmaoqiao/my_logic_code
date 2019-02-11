//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author          : $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : synchronize a  from src clock domain to dst clock domain
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


module simpleSynchro( 
         input  wire     dstclk,
         input  wire     dstresetn,
         input  wire     srcdata,

         output wire     dstdata
);

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

reg  srcdata_resync;       // data resyncrhonisation
reg  dstdata_sampled;      // data sampled into destination clock domain

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign  dstdata = dstdata_sampled;


// resynchronize data source 
always @ (posedge dstclk or negedge dstresetn) 
begin
  if ( dstresetn == 1'b0)  // Asynchronous Reset
  begin
    srcdata_resync  <= 1'b0;
    dstdata_sampled <= 1'b0;
  end
  else
  begin
    srcdata_resync  <= srcdata;
    dstdata_sampled <= srcdata_resync;
  end
end

endmodule
                 
