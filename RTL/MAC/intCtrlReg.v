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


module intCtrlReg( 
      
      //$port_g clocks and reset
      input wire                         macPIClk              ,// Platform clock                     
      input wire                         macPIClkHardRst_n     ,// Platfrom Reset
      
      // inputs
      input wire                         interrupt             ,// internal interruption
      input wire                         set                   ,// set interrupt
      input wire                         clear                 ,// clear interruption
      input wire                         mask                  ,// mask interruption
      // outputs
      output wire                        statusset             //,// interruption status
 //     output wire                        interruptOut           // interrutpion output (masked)
        
 );

reg statussetInt; // internal status before mask

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    statussetInt <= 1'b0;
  end
  else 
  begin
    if ( clear == 1'b1) begin
      statussetInt <= 1'b0;
    end
    else if ((interrupt == 1'b1) || (set == 1'b1))begin
      statussetInt <= 1'b1;
    end
  end
end


assign statusset = statussetInt && mask;

endmodule
                 
