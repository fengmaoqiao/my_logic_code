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
// Description      : downstream data and acknowledge block
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
module downstream_data_n_ack
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
  input  wire [ 7:0]   fromhost_ctrl,
  input  wire          fromhost_valid,
  output wire          fromhost_accept,

  /*****************************************************************************
  * DMA controller interface (ACK)
  *****************************************************************************/
  /* end of fragment acknowledge */
  output reg           downstream_ack,
  output reg  [ 3:0]   downstream_ack_tag,
  output reg  [15:0]   downstream_ack_length,
  input  wire          downstream_ack_ack,

  /*****************************************************************************
  * bus interface
  *****************************************************************************/
  output reg           busif_start,
  input  wire          busif_done,
  input  wire          busif_stall,

  /*****************************************************************************
  * Aligner interface
  *****************************************************************************/
  output wire [63:0]   aligner_data,
  output wire          aligner_data_en,
  output wire          aligner_data_last
);

  /*****************************************************************************
  * declarations
  *****************************************************************************/
  localparam  S_IDLE=2'b00,
              S_DATA=2'b01,
              S_WAIT_DONE=2'b10;
  
  /* flops */
  reg  [ 1:0] state;
  reg  [23:0] count;
  
  reg  [63:0] fromhost_data_1t;
  reg  [ 7:0] fromhost_ctrl_1t;
  reg         fromhost_valid_1t;
  
  /* wires */
  wire [23:0] new_count;
  
  /*****************************************************************************
  * assignment
  *****************************************************************************/
  /* from host fifo read enable */
  assign fromhost_accept = state==S_IDLE |
                           state==S_DATA & ~busif_stall;
  
  /* new dword count */
  assign new_count = count + {{23{1'b1}}, fromhost_ctrl_1t[2]^ fromhost_ctrl_1t[3]};

  /* data to aligner */
  assign aligner_data      = fromhost_data_1t;
  
  /* data enable */
  assign aligner_data_en   = state==S_DATA & fromhost_accept & fromhost_valid_1t |
                             state==S_WAIT_DONE;
                           
  /* data is last */
  assign aligner_data_last = state==S_DATA & fromhost_accept & fromhost_valid_1t & new_count==0 |
                             state==S_WAIT_DONE;                    

  /*****************************************************************************
  * FSM
  *****************************************************************************/
  always @(posedge clk, negedge rst_n)
  begin
  
    if(rst_n==0)
    begin
    
      fromhost_data_1t      <= 64'b0;
      fromhost_ctrl_1t      <=  8'b0;
      fromhost_valid_1t     <=  1'b0;
      
      count                 <= 24'b0;
      
      downstream_ack        <=  1'b0;
      downstream_ack_tag    <=  4'b0;  
      downstream_ack_length <= 16'b0;
      
      busif_start           <=  1'b0; 
      
      state                 <= S_IDLE; 
  
    end
    else
    begin
    
      /* re-register data from fifo */
      if(fromhost_accept)
      begin
        
        fromhost_data_1t  <= fromhost_data;
        fromhost_ctrl_1t  <= fromhost_ctrl;
        fromhost_valid_1t <= fromhost_valid;
        
      end
      
      /* FSM */                                                   
      case(state)                                                 
      
        S_IDLE:                                                   
        begin                                                     
                                                                  
          if(fromhost_valid_1t)                                   
          begin                                                   
                                                                  
            if(~fromhost_ctrl_1t[4])                              
            begin                                                 
                                                                  
              /* it's a fromhost ack descriptor */                
              if(fromhost_ctrl_1t[0])                             
              begin                                               
                                                                  
                /* first ack-descriptor word */
                downstream_ack_tag    <= fromhost_data_1t[7:4];   
                                                                  
              end                                                 
                                                                  
              if(fromhost_ctrl_1t[5])                             
              begin                                               
                                                                  
                /* second ack-descriptor word */                  
                downstream_ack_length <= fromhost_data_1t[15:0];  
                count                 <= fromhost_data_1t[23:0];  
                busif_start           <= 1'b1;                    
                state                 <= S_DATA;                  
                                                                  
              end                                                 
                                                                  
            end                                                   
                                                                  
          end                                                     
                                                                  
        end                                                       
                                                                  
        S_DATA:                                                   
        begin                                                     
                                                                  
          if(fromhost_valid_1t & fromhost_accept)                                   
          begin                                                   
                                                                  
            count <= new_count;                                 
                                                                  
            if(new_count==0)                                    
            begin                                                 
                                                                  
              /* all related entries from the host are read,
               * wait the bus interface to be done
               */
              state <= S_WAIT_DONE;                               
                                                                  
            end                                                   
                                                                  
          end                                                     
                                                                  
        end                                                       
                                                                  
        default:                                                   
        begin                                                     
                                                                  
          if(busif_done)                                          
          begin                                                   
            
            /* bus interface has finished its work
             * meaning that all bytes are written to memory
             * then we can ack the fragment to generate irq if 
             * required 
             */
             
            downstream_ack <= 1'b1;
            
            if(downstream_ack_ack)
            begin
            
              downstream_ack <= 1'b0;
              busif_start    <= 0;  
              state          <= S_IDLE;                                
          
            end
                                                                  
          end                                                     
                                                                  
        end                                                       
      
      endcase                                                     
        
    end
  
  end

  `ifdef RW_SIMU
  
    reg [16*8-1:0] state_str;
  
    always @(*)
    
      case (state)
      
        S_IDLE:      state_str = "S_IDLE";
        S_DATA:      state_str = "S_DATA";
        S_WAIT_DONE: state_str = "S_WAIT_DONE";   
        default:     state_str = "UNDEF";
      endcase    
      
  `endif

endmodule
