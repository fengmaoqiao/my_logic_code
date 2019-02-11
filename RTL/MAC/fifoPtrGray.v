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
// Description      : converts the binary code into gray code
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

module fifoPtrGray #(parameter ADDRWIDTH = 6)(
         //$port_g clock and Reset                                                                
         input  wire                    clk,              // clock
         input  wire                    hardReset_n,      // reset
         
         //$port_g counter handler                                                          
         input  wire                    flush,            // reset
         input  wire                    rdWrEn,           // counter increment
         input  wire                    rdWrDisable,      // disable increment

         //$port_g counter data                                                      
         input  wire    [ADDRWIDTH:0]  fifoAddr ,         // input address
         //
         output reg     [ADDRWIDTH:0]  fifoAddrGray       // output gray address

);

function automatic [ADDRWIDTH:0] binary2Gray ;
input   [ADDRWIDTH:0] binary ;
integer i ;
begin
  binary2Gray[ADDRWIDTH] = binary[ADDRWIDTH] ;
  for(i = 0; i < ADDRWIDTH; i = i + 1) 
  begin
     binary2Gray[i] = binary[i] ^ binary[i+1] ;
  end
end
endfunction

// The fifoAddr is incrmented on every rdWrEn. Also the
// Gray encoding corresponding to incremented address
// is found here

always @(posedge clk or negedge hardReset_n) 
begin
  if(hardReset_n == 1'b0) 
    fifoAddrGray <= {(ADDRWIDTH+1){1'b0}}; 
  else if (flush) 
    fifoAddrGray <= {(ADDRWIDTH+1){1'b0}};  
  else if (rdWrEn && (rdWrDisable == 1'b0)) 
    fifoAddrGray <= binary2Gray(fifoAddr + {{(ADDRWIDTH){1'b0}},1'b1}); 
end

// This function converts Binary Code into Gray Code

endmodule

//---------- END OF FILE ----------

