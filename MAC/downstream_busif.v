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
// Description      : downstream bus interface module
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
module downstream_busif
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input wire            clk,
  input wire            rst_n,
  
  /*****************************************************************************
  * control/state
  *****************************************************************************/
  input  wire           start,
  output wire           stall,
  output wire           done,

  /*****************************************************************************
  * Static parameters
  *****************************************************************************/
  input  wire [31:0]    dst_addr,
  input  wire [15:0]    dst_length,
 
  /*****************************************************************************
  * aligner interface
  *****************************************************************************/
  input  wire [63:0]    data,
  input  wire           data_en,
  
  /*****************************************************************************
  * bus interface
  *****************************************************************************/
  input  wire           bus_ready,
    
  output reg  [31:0]    bus_addr,
  output reg            bus_trans,
  
  output reg  [ 7:0]    bus_we,   
  output reg  [63:0]    bus_data
);

  /*****************************************************************************
  * declarations
  *****************************************************************************/
  localparam  S_IDLE=3'b000,
              S_PAUSE=3'b001,
              S_A=3'b010,
              S_AD=3'b011,
              S_D=3'b100,
              S_DONE=3'b101;
  
  /* flops */
  reg  [ 2:0] state;
  reg  [12:0] count;
  
  reg  [63:0] buffer_data;
  reg         buffer_state;
  reg         is_first;
  
  /* wires */
  reg  [ 7:0] first_be;
  reg  [ 7:0] last_be;
  wire [31:0] next_addr;
  wire [12:0] next_count;
  wire [ 2:0] qword_reliquat;
  wire [15:0] nbr_qwordsx8;
  wire        buffer_rden;
  
  /*****************************************************************************
  * assignments
  *****************************************************************************/
  assign done  = state==S_DONE;

  assign stall = (state==S_IDLE) ||    // hold on if bus if not started yet
                 (buffer_state==1'b1 && buffer_rden==1'b0);

  assign next_addr  = {bus_addr[31:3] + 29'b1,3'b0};
  assign next_count = count - 13'b1;

  /*****************************************************************************
  * computes the number of qwords involved in the transfer
  *****************************************************************************/
  assign qword_reliquat = dst_length[2:0] + 
                          dst_addr[2:0];
                          
  assign nbr_qwordsx8   = dst_length            +
                          {13'b0,dst_addr[2:0]} +
                          {12'b0,|qword_reliquat,3'b0};
  
  always @(*)
  begin:b_byte_enables
  
    case(dst_addr[2:0])
    
      3'b000:  first_be = 8'b11111111;
      3'b001:  first_be = 8'b11111110;
      3'b010:  first_be = 8'b11111100;
      3'b011:  first_be = 8'b11111000;
      3'b100:  first_be = 8'b11110000;
      3'b101:  first_be = 8'b11100000;
      3'b110:  first_be = 8'b11000000;
      default: first_be = 8'b10000000;
    
    endcase

    case(qword_reliquat)
    
      3'b000:  last_be = 8'b11111111;
      3'b001:  last_be = 8'b00000001;
      3'b010:  last_be = 8'b00000011;
      3'b011:  last_be = 8'b00000111;
      3'b100:  last_be = 8'b00001111;
      3'b101:  last_be = 8'b00011111;
      3'b110:  last_be = 8'b00111111;
      default: last_be = 8'b01111111;
    
    endcase
    
  end

  /*****************************************************************************
  * stall buffer
  *****************************************************************************/
  assign buffer_rden = (bus_ready==1'b1 && (state==S_A || state==S_AD)) |
                       state==S_PAUSE;
  
  always @(posedge clk, negedge rst_n)
  begin
  
    if(rst_n==1'b0)
    begin
    
      buffer_data  <= 64'b0;
      buffer_state <= 1'b0;
    
    end
    else
    begin
    
      if(start==0)
      begin
      
        buffer_state <= 1'b0;
      
      end
      else
      begin
      
        if(buffer_state==0)
        begin
          
          if(data_en==1'b1)
          begin
          
            buffer_data  <= data;
            buffer_state <= 1'b1;
            
          end
          
        end
        else
        begin
      
          if(buffer_rden==1'b1)
          begin
          
            if(data_en==1'b1)
            
              buffer_data <= data;
              
            else
            
              buffer_state <= 1'b0;
            
          end
      
        end
        
      end
      
    end
  
  end

  /*****************************************************************************
  * bus interface control
  *****************************************************************************/
  always @(posedge clk, negedge rst_n)
  begin
  
    if(rst_n==0)
    begin
    
      count      <= 13'b0;
      
      bus_addr   <= 32'b0;
      bus_trans  <= 1'b0;
      bus_data   <= 63'b0;
      bus_we     <= 8'b0;
      
      
      is_first   <= 1'b0;
      
      state      <= S_IDLE;
    
    end
    else
    begin
    
      case(state)
      
        S_IDLE:
        begin
        
          if(start)
          begin
          
            bus_addr   <= dst_addr;
            count      <= nbr_qwordsx8[15:3];
            is_first   <= 1'b1;
            state      <= S_PAUSE;
          
          end
        
        end
        
        S_PAUSE:
        begin
        
          if(data_en)
          begin
          
            bus_trans <= 1'b1;
            state     <= S_A;
          
          end
          
        end
        
        S_A:
        begin
        
          if(bus_ready)
          begin
          
            is_first <= 1'b0;
            count    <= next_count;
            bus_addr <= next_addr;
            bus_data <= buffer_data;
            
            if(count==1)
            begin
            
              if(is_first)
              
                bus_we <= first_be & last_be;
                
              else
              
                bus_we <= last_be;
              
              bus_trans <= 1'b0;
              state     <= S_D;
              
            end
            else
            begin
            
              if(is_first)
              
                bus_we <= first_be;
                
              else
              
                bus_we <= {8{1'b1}};
              
              if(data_en)
              begin
              
                bus_trans <= 1'b1;
                state     <= S_AD;
                
              end  
              else
              begin
              
                bus_trans <= 1'b0;
                state     <= S_D;
                
              end
            
            end
            
          end
        
        end
        
        S_AD:
        begin
        
          if(bus_ready)
          begin
          
            count    <= next_count;
            bus_addr <= next_addr;
            bus_data <= buffer_data;
            
            if(count==1)
            begin
            
              bus_trans <= 1'b0;
              bus_we    <= last_be;
              state     <= S_D;
              
            end
            else
            begin
            
              bus_we <= {8{1'b1}};
            
              if(data_en)
              begin
              
                bus_trans <= 1'b1;
                state     <= S_AD;
                
              end
              else
              begin
              
                bus_trans <= 1'b0;
                state     <= S_D;
                
              end
            
            end
            
          end
        
        end
        
        S_D:
        begin
        
          if(bus_ready)
          begin
          
            if(count==0)
            begin
            
              state <= S_DONE;
              
            end
            else
            begin
            
              if(data_en==1)
              begin
              
                bus_trans <= 1'b1;
                state     <= S_A;
                
              end
              else
              begin
              
                state <= S_PAUSE;
              
              end
              
            end
            
          end
          else
          begin
          
            if(count!=0)
            begin
            
              if(data_en==1)
              begin
              
                bus_trans <= 1'b1;
                state     <= S_A;
                
              end
              
            end
            
          end
          
        end
        
        default:
        begin
        
          if(start==1'b0)
          begin
          
            state <= S_IDLE;
          
          end
        
        end
        
      endcase
      
    end
    
  end
 
  `ifdef RW_SIMU
  
    reg [16*8-1:0] state_str;
  
    always @(*)
    
      case (state)
      
        S_IDLE:       state_str = "S_IDLE";       
        S_PAUSE:      state_str = "S_PAUSE";       
        S_A:          state_str = "S_A";   
        S_AD:         state_str = "S_AD";   
        S_D:          state_str = "S_D";   
        S_DONE:       state_str = "S_DONE";   
        default:      state_str = "UNDEF";    
      endcase    
      
  `endif

endmodule
