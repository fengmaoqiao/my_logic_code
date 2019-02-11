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
//   This module is a 32 bit polynomial generator/checker.
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

module crcGenChk (

   //$port_g Inputs
   input  wire         clk ,       // input clock
   input  wire         reset_N ,   // hard reset
   input  wire         start,      // start accumalation in CRC register
   input  wire         enable ,    // Enable pin for all operation, Active high
   input  wire         drain ,     // Drains the CRC register
   input  wire   [7:0] d_in ,      // Input data

  //$port_g Outputs
   output reg    [7:0] d_out ,     // Output data
   output reg          crc_ok      // Indicates a correct CRC value

);

//------------------reg---------------------------------------------

   reg  [31:0] C ;
   reg  [31:0] Q ;
   reg         accumalating;
   reg  [1:0]  count;
   reg         draining;   // Indicates that CRC register is draining

//-----------------wire----------------------------------------------
   wire [31:0] P ;
   wire        crc_enable;
   wire [7:0]  tempC;

//----------------integer--------------------------------------------
   integer     i ;
   integer     j ;

   parameter CRC_POLYNOMIAL    = 32'h04C1_1DB7,
             CRC_PRELOAD_VALUE = 32'hFFFF_FFFF,
             CRC_RESULT       =  32'hC704_DD7B;

// The combinational logic that is used to calculate the value of the CRC
// register for each 32 bit quantity that is latched in. The logic is as
// follows C <= F ( D, C, P ) where P is the crc polynomial, C is the
// current value of the crc_register, and D is the word of data that
// has just been received.
   
// The equations are generic and no reduction is done. The reduction of 
// the levels of equations required to generate/check crc is best left to
// synthesis tool.

// Assign the value of the crc polynomial to a wire P

   assign P = CRC_POLYNOMIAL; 

// if (C == CRC_RESULT) it indicates correct CRC value   

//   assign crc_ok = (C == CRC_RESULT);  
  always @ ( posedge clk or negedge reset_N)
  begin
    if (! reset_N)
      crc_ok <= 1'b0;
    else if (enable)
      crc_ok <= (Q == CRC_RESULT);
    else
      crc_ok <= crc_ok;
  end 

// temporarily assigning C[31:24] to tempC[7:0]

   assign tempC = ~C[31:24];

// when crc_enable signal is high contents of Q are assigned
// to C.

   assign crc_enable = enable & (draining | accumalating );

// This count is used while draing out CRC register 

  always @ (posedge clk or negedge reset_N) begin
    if(!reset_N)
      count <= 2'b00;
    else if (draining && enable)
      count <= count + 2'b01;
    else
      count <= count;
  end


  always @(C or P or  accumalating or d_in) begin
    Q = C ;
    for(i = 0; i < 8; i = i + 1) 
      Q = ({Q[30:0],1'b0}) ^ (P[31:0] & ({32{((d_in[i]^Q[31]) & accumalating)}})) ;
  end

// Latching the calculated/generated CRC into the CRC register
// whem crc_enable is high. On start CRC_PRELOAD_VALUE (32'hFFFF_FFFF)
// is assigned to C register. 

  always @(posedge clk or negedge reset_N) begin
    if(!reset_N)
      C <= 32'h0000_0000 ;
    else if(start)
      C <= CRC_PRELOAD_VALUE ;
    else if (crc_enable)
      C <= Q;
  end

// Indicates that CRC register is accumalating
// This signal goes high on start and is pulled
// down when drain is set.  

  always @(posedge clk or negedge reset_N) begin
    if(!reset_N)
      accumalating <= 1'b0;
    else if(enable)
      accumalating <= start | ((!drain) & accumalating); 
    else 
      accumalating <= accumalating;
  end

// generation of draining signal
// This signal remains high until all 4 bytes of CRC
// are driven out. Intially when drain and enable is 
// high first byte of CRC is driven and on subsequent 
// enables pending three bytes of CRC is driven out. 

  always @(posedge clk or negedge reset_N) begin
    if(!reset_N)
      draining <= 1'b0;
    else if (enable)
      draining <= (accumalating & drain) | (draining & ~&count );
    else
      draining <= draining;
  end 

// Multiplexer to select between the incoming data and the generated CRC.
// When draining is high the contents of tempC is driven to d_out else
// if draining is low d_in is drive out

  always @ ( draining or d_in or tempC ) begin
    if (draining)begin
      for ( j=0; j<8; j=j+1) begin
        d_out[j] = tempC[7-j];
      end
    end
    else
      d_out = d_in;
  end 


endmodule
