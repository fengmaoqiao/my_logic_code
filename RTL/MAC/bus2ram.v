/////////////////////////////////////////////////////////////////////////////
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
// Description      : bus2ram module
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
module bus2ram
#(
  /*****************************************************************************
  * Default number of interrupt sources
  *****************************************************************************/
  parameter                      g_addr_width=15
)
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire                    clk,
  input  wire                    rst_n,
  
  /*****************************************************************************
  * Arbitration signaling
  *****************************************************************************/
  output wire                    req,
  input  wire                    gnt,
  
  /*****************************************************************************
  * bus interface
  *****************************************************************************/
  
  input  wire [g_addr_width-1:0] bus_addr,
  input  wire                    bus_trans,
  input  wire                    bus_write,
  input  wire [1:0]              bus_size,
  output reg                     bus_ready,
 
  /*****************************************************************************
  * sram interface
  *****************************************************************************/
  output wire                    ram_cs,   
  output wire                    ram_asel, 
  output wire [g_addr_width-4:0] ram_a0,   
  output wire [g_addr_width-4:0] ram_a1,   
  output wire [ 7: 0]            ram_we0,  
  output wire [ 7: 0]            ram_we1,  
  output reg  [ 1: 0]            ram_lane  
);
  /*****************************************************************************
  * declaration
  *****************************************************************************/
  /* flops */
  reg  [g_addr_width-3:0] addr; // keep 32bits address
  reg  [7:0]              we;
  reg                     hold;
  reg                     gnt_1t;
  reg                     hold_ack;
  
  /* wires */
  reg  [7:0]              bus_we;
  reg                     load;
  reg                     n_hold;
  reg                     n_bus_ready;
  wire [1:0]              ram_a_lane;
  wire                    bus_pending;

  /*****************************************************************************
  * compute byte enable from size
  *****************************************************************************/
  always @(*)
  begin
  
    casez({bus_write,bus_size,bus_addr[2:0]})  
    
      6'b1_00_000: bus_we = 8'b00000001;         
      6'b1_00_001: bus_we = 8'b00000010;         
      6'b1_00_010: bus_we = 8'b00000100;         
      6'b1_00_011: bus_we = 8'b00001000;         
      6'b1_00_100: bus_we = 8'b00010000;         
      6'b1_00_101: bus_we = 8'b00100000;         
      6'b1_00_110: bus_we = 8'b01000000;         
      6'b1_00_111: bus_we = 8'b10000000;         
      6'b1_01_00?: bus_we = 8'b00000011;         
      6'b1_01_01?: bus_we = 8'b00001100;         
      6'b1_01_10?: bus_we = 8'b00110000;         
      6'b1_01_11?: bus_we = 8'b11000000;         
      6'b1_10_0??: bus_we = 8'b00001111;         
      6'b1_10_1??: bus_we = 8'b11110000;         
      6'b1_11_???: bus_we = 8'b11111111;
      default:     bus_we = 8'b00000000;         
    
    endcase                                      
    
  end
  
  /*****************************************************************************
  * fsm
  *****************************************************************************/
  always @(posedge clk,negedge rst_n)
  begin
  
    if(rst_n==0) 
    begin
    
      bus_ready <= 1'b1;
      hold      <= 1'b0;
      addr      <= 'b0;
      we        <= 8'b0;
      ram_lane  <= 2'b0;
      gnt_1t    <= 1'b0;
      hold_ack  <= 1'b0;
    
    end 
    else 
    begin
    
      hold      <= n_hold;
      bus_ready <= n_bus_ready;
      gnt_1t    <= gnt;
      
      if(load)
      begin
      
        addr <= bus_addr[g_addr_width-1:2];
        we   <= bus_we;
      
      end
      
      /* indicates which data lane is valid */
      ram_lane <= ram_a_lane;
      
      /* */
      hold_ack <= hold & gnt & ~bus_trans ;
      
    end
    
  end
  
  assign bus_pending = bus_trans & bus_ready;
  
  always @(*)
  begin
    
    if(hold)
    begin
    
      /* there is an address pending */
      if(gnt_1t)
      begin
      
        /* but access is done in the cycle */
        if(bus_pending)            
        begin                              
        
          load        = 1;                 
          n_hold      = 1;
          
          if(bus_write)
          
            n_bus_ready = gnt;
            
          else
          
            n_bus_ready = 1'b0;
                                           
        end                                
        else // ~bus_trans                      
        begin                              
                                           
          load        = 0;                 
          n_hold      = 1'b0; 
          n_bus_ready = 1'b1;
                                           
        end                                
          
      end              
      else  // ~gnt        
      begin 
      
        load        = 1'b0;
        n_hold      = 1'b1;
        
        if(bus_pending)
        
          n_bus_ready = gnt & |we;
        
        else
        
          n_bus_ready = 1'b0;
             
      end              
      
    end
    else  // ~hold
    begin
    
      if(gnt_1t)
      begin
        
        if(bus_pending & bus_write)
        begin
      
          load        = 1;
          n_hold      = 1;
          n_bus_ready = gnt;
      
        end
        else
        begin
        
          load        = 0;
          n_hold      = 0;
          n_bus_ready = 1;
        
        end
        
      end
      else  // ~gnt_1t
      begin
      
        if(bus_pending)
        begin
      
          load        = 1;
          n_hold      = 1;
          n_bus_ready = 0;
          
        end
        else
        begin
        
          load        = 0;
          n_hold      = 0;
          n_bus_ready = 1;
        
        end
      
      end
    
    end
    
  end
  
  /*****************************************************************************
  * arbitration
  *****************************************************************************/
  assign req = (hold & ~hold_ack) | bus_trans;
  
  /*****************************************************************************
  * ram interface
  *****************************************************************************/
  assign ram_cs   = hold | bus_trans & ~bus_write;
  
  assign ram_asel = hold;
  
  assign ram_a0   = bus_addr[g_addr_width-1:3]; 
  assign ram_a1   = addr[g_addr_width-3:1]; 
  
  assign ram_we0  = bus_we;
  assign ram_we1  = we; 
  
  assign ram_a_lane = {2{ hold}} & {addr[0],~addr[0]} |
                      {2{~hold}} & {bus_addr[2],~bus_addr[2]};


  `ifdef RW_SIMU
  
  wire [17:0] ram_a0_32,ram_a1_32,addr_32;
  
  assign ram_a0_32 = {ram_a0,3'b0};
  assign ram_a1_32 = {ram_a1,3'b0};
  assign addr_32   = {addr,2'b0};
  
  `endif

endmodule
