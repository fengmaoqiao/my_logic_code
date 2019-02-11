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

module pulse2PulseSynchro( 
         input  wire      srcclk,
         input  wire      srcresetn,
         input  wire      dstclk,
         input  wire      dstresetn,
         input  wire      srcdata,
         
         output wire      dstdata
);


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
reg         srcdataLatch;
reg         dstdata_ff1;      
reg         dstdata_ff2;      
reg         dstdata_resync;       // resynchronization into source clock domain
reg         srcdataLatchReset;    // reset the srcdataLatch


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign dstdata = ((dstdata_ff1 == 1'b1) && (dstdata_ff2 == 1'b0)) ? 1'b1 : 1'b0;

// Latch the input
always @ (posedge srcclk or negedge srcresetn) 
begin
  if ( srcresetn == 1'b0)  // Asynchronous Reset
    srcdataLatch <= 1'b0;
  else
    if ( srcdata == 1'b1 )
      srcdataLatch <= 1'b1;
    else if (srcdataLatchReset == 1'b1)
      srcdataLatch <= 1'b0;
end

// resynchronize dst data
always @ (posedge srcclk or negedge srcresetn) 
begin
  if ( srcresetn == 1'b0)  // Asynchronous Reset
  begin
    dstdata_resync    <= 1'b0;
    srcdataLatchReset <= 1'b0;
  end
  else
  begin
    dstdata_resync    <= dstdata_ff1;
    srcdataLatchReset <= dstdata_resync;
  end
end

reg  srcdata_resync;       // data resyncrhonisation

// resynchronize latched data
always @ (posedge dstclk or negedge dstresetn) 
begin
  if ( dstresetn == 1'b0)  // Asynchronous Reset
  begin
    srcdata_resync  <= 1'b0;
    dstdata_ff1     <= 1'b0;
    dstdata_ff2     <= 1'b0;
  end
  else
  begin
    srcdata_resync  <= srcdataLatch;
    dstdata_ff1     <= srcdata_resync;
    dstdata_ff2     <= dstdata_ff1;
  end
end




endmodule
