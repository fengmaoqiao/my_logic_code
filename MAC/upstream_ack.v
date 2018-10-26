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
// Description      : upstream ack module
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

`define RW_SIMU
module upstream_ack
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire          clk,
  input  wire          rst_n,

  /*****************************************************************************
  * Dini fromhost interface
  *****************************************************************************/
  input  wire [63:0]   fromhost_data,
  input  wire [7: 0]   fromhost_ctrl,
  input  wire          fromhost_valid,
  output reg           fromhost_accept,

  /*****************************************************************************
  * Dini fromhost interface
  *****************************************************************************/
  output wire          upstream_ack,
  output reg  [ 3: 0]  upstream_ack_tag,
  output reg  [15: 0]  upstream_ack_length,
  (* syn_keep = "true" , mark_debug = "true" *)input  wire          upstream_ack_ack
);
  /*****************************************************************************
  * declarations
  *****************************************************************************/
  localparam  S_IDLE=1'b0,
              S_WAIT_ACK=1'b1;

  reg         state;

  assign upstream_ack = state==S_WAIT_ACK;

  /*****************************************************************************
  * FSM
  *****************************************************************************/
  always @(posedge clk, negedge rst_n)
  begin
  
    if(rst_n==1'b0)
    begin
    
      upstream_ack_tag    <= 4'b0;
      upstream_ack_length <= 24'b0;
      fromhost_accept     <= 1'b0;
      state               <= S_IDLE;
    
    end
    else
    begin
    
      case(state)
      
        S_IDLE:
        begin
        
          fromhost_accept <= 1'b1;
          
          if(fromhost_valid)
          begin
           
            /* a data fromhost is avaialble */
            if(fromhost_ctrl[4])
            begin
            
              /* it's a tohost ack descriptor */
              if(fromhost_ctrl[0]) 
              begin
              
                upstream_ack_tag  <= fromhost_data[7:4];
              
              end
              
              if(fromhost_ctrl[5]) 
              begin
              
                fromhost_accept     <= 1'b0;
                upstream_ack_length <= fromhost_data[23:0];
                state               <= S_WAIT_ACK;
            
              end
            
            end
          
          end
        
        end
        
        default:
        begin
        
          if(upstream_ack_ack)
          begin
          
            fromhost_accept <= 1'b0;
            state           <= S_IDLE;
          
          end
        
        end
      
      endcase

    end
  
  end
  
  `ifdef RW_SIMU
  
    reg [16*8-1:0] state_str;
  
    always @(*)
    
      case (state)
      
        S_IDLE:     state_str = "S_IDLE";
        S_WAIT_ACK: state_str = "S_WAIT_ACK";
        default:    state_str = "UNDEF";
      
      endcase    
      
  `endif

endmodule
