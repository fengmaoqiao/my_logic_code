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
// Description      : downstream request module
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
// $HeadURL: $
//
//////////////////////////////////////////////////////////////////////////////

`define  RW_SIMU
module downstream_req
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire           clk,
  input  wire           rst_n,

  /*****************************************************************************
  * channel request
  *****************************************************************************/
  input  wire           channel_sel,
  input  wire           channel_req,
  input  wire [31:0]    channel_saddr,
  
  input  wire [31:0]    channel_daddr,  //add by fengmaoqiao
  
  input  wire [15:0]    channel_length,
  input  wire [ 3:0]    channel_tag,
  output wire           channel_busy,

  /*****************************************************************************
  * Dini tohost interface
  *****************************************************************************/
  input  wire           tohost_almost_full,
  output reg  [63:0]    tohost_data,
  output reg  [ 7:0]    tohost_ctrl,
  output reg            tohost_valid
);

  /*******************************************************************************
  * declaration
  *******************************************************************************/
  /* flops */
  localparam  S_IDLE=2'b00,
              S_INIT=2'b01,
              S_DESC=2'b10;
              
  reg  [ 1:0] state;
  reg  [31:0] src_addr;
  reg  [15:0] byte_length;
  reg  [ 3:0] tag;

  /* wires */
  wire [15:0] nbr_dwordsx4;
  wire [ 1:0] dword_reliquat;
  
  reg  [31:0] dst_daddr;    //add by fengmaoqiao

  /*****************************************************************************
  * assignment
  *****************************************************************************/
  assign channel_busy = state!=S_IDLE;

  /*****************************************************************************
  * computes the number of dwords involved in the transfer
  *****************************************************************************/
  assign dword_reliquat = byte_length[1:0] + 
                          src_addr[1:0];
                          
  assign nbr_dwordsx4   = byte_length           +
                          {14'b0,src_addr[1:0]} +
                          {13'b0,|dword_reliquat,2'b0};

  /*****************************************************************************
  * FSM
  *****************************************************************************/
  always @(posedge clk, negedge rst_n)
  begin
  
    if(rst_n==1'b0)
    begin

      tohost_data  <= 64'b0;
      tohost_ctrl  <=  8'b0;
      tohost_valid <=  1'b0;
    
      src_addr     <= 32'b0;
      
      dst_daddr    <= 32'b0;//add by fengmaoqiao
      
      byte_length  <= 16'b0;
      tag          <= 4'b0;
      state        <= S_IDLE;
    
    end
    else
    begin
    
      case(state)
      
        S_IDLE:
        begin
        
          tohost_valid <= 1'b0;
          
          if(channel_sel & channel_req)
          begin
          
            src_addr    <= channel_saddr;
            
            dst_daddr   <= channel_daddr;       //add by fengmaoqiao
            
            byte_length <= channel_length;
            tag         <= channel_tag;
            state       <= S_INIT;
          
          end
        
        end
        
        S_INIT:
        begin
        
          /* ensure that there is enough room in the tohost fifo before sending data */
          if(~tohost_almost_full)
          begin
          
            /* descriptor 0 */
            tohost_data[63:32]  <= {24'b0,tag,1'b0,src_addr[2],2'b0};   // tag + dini fix 20120326
            tohost_data[31]     <= 1'b1;               // valid
            tohost_data[30]     <= 1'b0;               // direction
            
            //tohost_data[29:27]  <= 3'b0;               // reserved
            tohost_data[29:27]  <= dst_daddr[3:1];               // reserved --edit by fengmaoqiao
            
            tohost_data[26]     <= 1'b0;               // byte enables enabled
            tohost_data[25:24]  <= 2'b0;               // reserved
            tohost_data[23:20]  <= 4'b0000;            // first 32bits word byte enable
            tohost_data[19:16]  <= 4'b0000;            // last 32bits word byte enable
            tohost_data[15: 0]  <= nbr_dwordsx4[15:2]; // number of 32 bits words involved in the transaction
          
            /* descriptor control */
            tohost_ctrl[7:5]    <= 3'b0; // not documented
            tohost_ctrl[4]      <= 1'b1; // descriptor enable
            tohost_ctrl[3]      <= 1'b0; // is last
            tohost_ctrl[2]      <= 1'b1; // demand-mode
            tohost_ctrl[1:0]    <= 2'b11; // validity of the 32bits parts of the 64bits word
            tohost_valid        <= 1'b1;
            state               <= S_DESC;
            
          end
        
        end
        
        default:
        begin
        
          tohost_data      <= {dst_daddr,src_addr[31:2],2'b0};
          tohost_ctrl[3]   <= 1'b1; // is last
         
          tohost_valid     <= 1'b1;
          state            <= S_IDLE;
        
        end
      
      endcase
    
    end
  
  end
 
  `ifdef RW_SIMU
  
    reg [16*8-1:0] state_str;
  
    always @(*)
    
      case (state)
      
        S_IDLE:   state_str = "S_IDLE";
        S_INIT:   state_str = "S_INIT";
        S_DESC:   state_str = "S_DESC";   
        default:  state_str = "UNDEF";
      endcase    
      
  `endif

endmodule
