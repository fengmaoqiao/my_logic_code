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
// Description      : Assumes that the level input remains for at least two cloks of 
//                    syncClk
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
module syncLevel(
    //$port_g clock and Reset 
    input  wire      syncClk ,   // Resynchronization clock
    input  wire      nSyncRst ,  // Asynchronous reset

    //$port_g Data 
    input  wire      dataIn ,    // Data to be resynchronized

    output reg       dataOut     // Resynchronized Data on syncClk clock
    );






// Declare the internal variables of the module
reg         dataIn_resync ;

// logic begins here ..

// logic for the first flip-flop
always @(posedge syncClk or negedge nSyncRst) 
begin
  if(nSyncRst == 1'b0)  
    dataIn_resync <= 1'b0 ;
  else  
    dataIn_resync <= dataIn ;
end

// logic for the second flip-flop
always @(posedge syncClk or negedge nSyncRst) 
begin
  if(nSyncRst == 1'b0)  
    dataOut <= 1'b0 ;
  else  
    dataOut <= dataIn_resync ;
end

endmodule

//---------- END OF FILE ----------
