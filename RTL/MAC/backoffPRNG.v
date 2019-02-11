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

module backoffPRNG( 

            //$port_g Clock and Reset
            input wire            macCoreClk,              // MAC core clock      
            input wire            macCoreClkHardRst_n,     // MAC core clock reset
            
            input  wire           macCoreClkSoftRst_n,     // MAC core clock soft reset
            
            //$port_g back off control interface
            input wire            backOffDone_p,           // Enable the random value generation

            //$port_g Backoff Counters interface
            output wire [18:0]    pseudoRandomNumber       // generated pseudo random number

                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
localparam SEED0  =  10'b1001110100;
localparam SEED1  =   9'b101001101;



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
reg  [18:0]                 randomValue;  //pseudo randomly generated value

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////
assign pseudoRandomNumber = randomValue;


always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    randomValue[ 9: 0] <= SEED0;
    randomValue[18:10] <= SEED1;
  end
  else if (macCoreClkSoftRst_n == 1'b0)
  begin
    randomValue[ 9: 0] <= SEED0;
    randomValue[18:10] <= SEED1;
  end
  else 
  begin
    // If enable start to shift the LFSR
    if (backOffDone_p)
    begin
      randomValue[18:1] <= randomValue[17:0];
      randomValue[0]    <= randomValue[16] ^ randomValue[13];
    end
  end
end



endmodule
                 
