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
// Description      : 
//       This module synchrises the bus signals. The width of the signal being 
//       synchronized can be defined during instantiation there by over riding
//       the SYNC_WIDTH parameter
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
module syncBus #(parameter SYNC_WIDTH = 1)(
        
        //$port_g clock and Reset 
        input  wire                        syncClk ,        // Resynchronization clock
        input  wire                        syncHardRst_n ,  // Asynchronous reset

        //$port_g Data 
        input  wire         [SYNC_WIDTH:0] dataIn ,         // Data to be resynchronized
        
        output reg          [SYNC_WIDTH:0] dataOut          // Resynchronized Data on syncClk clock

) ;

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
localparam [SYNC_WIDTH-1:0] ZERO_CT = {(SYNC_WIDTH){1'b0}};

// The internal variables of the module are defined here ..
reg  [SYNC_WIDTH:0] dataIn_resync ;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Logic for the first level of register.
always @(posedge syncClk or negedge syncHardRst_n) 
begin
  if(syncHardRst_n == 1'b0) 
    dataIn_resync <= ZERO_CT ;
  else 
    dataIn_resync <= dataIn ;
end

// Logic for second level of register. 
always @(posedge syncClk or negedge syncHardRst_n) 
begin
  if(syncHardRst_n == 1'b0) 
    dataOut <= ZERO_CT ;
  else 
    dataOut <= dataIn_resync ;
end
endmodule

