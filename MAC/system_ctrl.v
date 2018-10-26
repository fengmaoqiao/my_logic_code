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
// Description      : system controller module
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

module system_ctrl
( 
  /*****************************************************************************
  * Ssytem
  *****************************************************************************/
  input  wire                  clk,
  input  wire                  rst_n,
  
  /***************************************************************************
  * AHB slave interface
  ***************************************************************************/
  input  wire                  hready_in,
  input  wire                  hsel,
  input  wire [ 9:0]           haddr,
  input  wire [ 1:0]           htrans,
  input  wire                  hwrite,
  input  wire [31:0]           hwdata,
  output reg  [31:0]           hrdata,
  output wire [ 1:0]           hresp,
  output wire                  hready,

  /***************************************************************************
  * regsiters
  ***************************************************************************/
  input  wire                  nmb_io_busy,
  
  output reg                   reg_bootrom_enable,
  output reg                   reg_diag_sel_en,
  output reg  [15:0]           reg_diag_sel,
  output reg                   reg_diag_trigger,
  input  wire [31:0]           diag_value,
  output reg                   reg_fpgaa_reset_req,
  output reg                   reg_fpgab_reset_req,

  /***************************************************************************
  * Clock Controller
  ***************************************************************************/
  output reg                   reg_mac_pi_clk_gating_en,   // mac_pi_clk Interface gating enable 
  output reg                   reg_mac_pi_tx_clk_gating_en,   // mac_pi_clk Interface gating enable 
  output reg                   reg_mac_pi_rx_clk_gating_en,   // mac_pi_clk Interface gating enable 
  output reg                   reg_mac_core_clk_gating_en, // mac_core_clk Interface gating enable 
  output reg                   reg_mac_crypt_clk_gating_en, // mac_core_clk Interface gating enable 
  output reg                   reg_mac_core_rx_clk_gating_en, // mac_core_clk Interface gating enable 
  output reg                   reg_mac_core_tx_clk_gating_en, // mac_core_clk Interface gating enable 
  output reg                   reg_mac_wt_clk_gating_en,   // mac_wt_clk Interface gating enable 
  output reg                   reg_mpif_clk_gating_en     // mpif_clk Interface gating enable 
);

  /*****************************************************************************
  * Declarations
  *****************************************************************************/
  reg                          pending_write;
  reg   [5:0]                  pending_addr;
  reg   [31:0]                 reserved0;
  reg   [31:0]                 reserved1;
  reg   [31:0]                 current_cycle;
  

`ifndef RW_FPGA_SIGNATURE
  `define RW_FPGA_SIGNATURE 32'hc0ffee00
`endif
`ifndef RW_FPGA_DATE
  `define RW_FPGA_DATE 32'h20000101
`endif
`ifndef RW_FPGA_TIME
  `define RW_FPGA_TIME 32'h00000000
`endif
`ifndef RW_FPGA_SVNREV
  `define RW_FPGA_SVNREV 32'h00000000
`endif
`ifndef RW_MAC_SVNREV
  `define RW_MAC_SVNREV 32'h00000000
`endif



  assign hresp  = 2'b00;
  assign hready = 1'b1;
  
  /*****************************************************************************
  * Permanently clocked registers
  *****************************************************************************/
  always @(posedge clk, negedge rst_n)
  begin
  
    if(rst_n==0)
    begin
      hrdata                    <= 0;
      //
      pending_write             <= 0;
      pending_addr              <= 0;
      //
      reserved0                 <= 0;
      reserved1                 <= 0;
      //
      current_cycle             <= 0; 
      
      reg_diag_sel_en           <= 1'b0;
      reg_diag_sel              <= 16'b0;
      reg_diag_trigger          <= 1'b0;
      //
      reg_fpgaa_reset_req       <= 1'b0;
      reg_fpgab_reset_req       <= 1'b1;
      reg_bootrom_enable        <= 1'b0;

      reg_mac_pi_clk_gating_en       <= 1'b0; 
      reg_mac_pi_tx_clk_gating_en    <= 1'b0; 
      reg_mac_pi_rx_clk_gating_en    <= 1'b0; 
      reg_mac_core_clk_gating_en     <= 1'b0; 
      reg_mac_crypt_clk_gating_en    <= 1'b0; 
      reg_mac_core_tx_clk_gating_en  <= 1'b0; 
      reg_mac_core_rx_clk_gating_en  <= 1'b0; 
      reg_mac_wt_clk_gating_en       <= 1'b0; 
      reg_mpif_clk_gating_en         <= 1'b0;  

    end
    else
    begin
    
      // current cycle
      current_cycle <= current_cycle + 1;
      
      if(hready_in==1)
      begin
      
        if(pending_write==1)
        begin
        
          pending_write <= 0;
        
          case(pending_addr)
        
            /*******************************************************************
            * current cycle
            *******************************************************************/
            6'b010000: current_cycle    <= hwdata;
                     
            /*******************************************************************
            * Diagport selection
            *******************************************************************/
            6'b011010: {reg_diag_sel_en,reg_diag_sel} <= {hwdata[31],hwdata[15:0]};
            6'b011100: reg_diag_trigger               <= hwdata[0];
            

            /*********************************************************************
            * Misc control
            *********************************************************************/
            6'b111000: 
            begin
              
              reg_bootrom_enable            <= hwdata[4];
              reg_fpgab_reset_req           <= hwdata[1];
              reg_fpgaa_reset_req           <= hwdata[0];

              reg_mac_pi_clk_gating_en      <= hwdata[16]; 
              reg_mac_pi_tx_clk_gating_en   <= hwdata[15]; 
              reg_mac_pi_rx_clk_gating_en   <= hwdata[14]; 
              reg_mac_core_clk_gating_en    <= hwdata[13];
              reg_mac_crypt_clk_gating_en   <= hwdata[12];
              reg_mac_core_tx_clk_gating_en <= hwdata[11];
              reg_mac_core_rx_clk_gating_en <= hwdata[10];
              reg_mac_wt_clk_gating_en      <= hwdata[9];
              reg_mpif_clk_gating_en        <= hwdata[8];

             end
           
            /*******************************************************************
            * Reserved
            *******************************************************************/
            6'b111100: reserved0 <= hwdata;
            6'b111101: reserved1 <= hwdata;
            
            default  : ;
            
          endcase
          
        end
      
      end
      
      if(hready_in==1 && hsel==1 && htrans[1]==1)
      begin
      
        if(hwrite==1)
        begin
        
          pending_addr  <= haddr[7:2];
          pending_write <= 1;
          
        end
        else
        begin
        
          hrdata <= 0;
          
          case(haddr[7:2])                                                        
                                                                                  
            /*******************************************************************
            * FPGA signature
            *******************************************************************/
            6'b000000: hrdata    <= `RW_FPGA_SIGNATURE;

            /*******************************************************************
            * FPGA date
            *******************************************************************/
            6'b000001: hrdata    <= `RW_FPGA_DATE;

            /*******************************************************************
            * FPGA time
            *******************************************************************/
            6'b000010: hrdata    <= `RW_FPGA_TIME;

            /*******************************************************************
            * FPGA svnrev
            *******************************************************************/
            6'b000011: hrdata    <= `RW_FPGA_SVNREV;

            /*******************************************************************
            * MAC fpgarev
            *******************************************************************/
            6'b000100: hrdata    <= `RW_MAC_SVNREV;

            /*********************************************************************
            * Memory protection                                                   
            *********************************************************************/
                         
            /*********************************************************************
            * MPA arbitration mode                                                
            *********************************************************************/
                                                                                  
            /*******************************************************************
            * current cycle
            ********************************************************************/
            6'b010000: hrdata <= current_cycle;
           
            /*********************************************************************
            * Diagport selection                                                  
            *********************************************************************/
            6'b011010: {hrdata[31],hrdata[15:0]}  <= {reg_diag_sel_en,reg_diag_sel};               
            6'b011011: hrdata                     <= diag_value;
            6'b011100: hrdata[0]                  <= reg_diag_trigger;
                                                                                  
            /*********************************************************************
            * Clock control
            *********************************************************************/
            6'b111000:
            begin
               
               hrdata[31] <= nmb_io_busy;
               hrdata[4]  <= reg_bootrom_enable;
               hrdata[1]  <= reg_fpgab_reset_req;
               hrdata[0]  <= reg_fpgaa_reset_req;

               hrdata[16] <= reg_mac_pi_clk_gating_en; 
               hrdata[15] <= reg_mac_pi_tx_clk_gating_en; 
               hrdata[14] <= reg_mac_pi_rx_clk_gating_en; 
               hrdata[13] <= reg_mac_core_clk_gating_en; 
               hrdata[12] <= reg_mac_crypt_clk_gating_en; 
               hrdata[11] <= reg_mac_core_tx_clk_gating_en; 
               hrdata[10] <= reg_mac_core_rx_clk_gating_en;
               hrdata[9]  <= reg_mac_wt_clk_gating_en;
               hrdata[8]  <= reg_mpif_clk_gating_en;

            end
            
            /*********************************************************************
            * Reserved0
            *
            * For simulation only
            * [0]  : end of simulation
            * [1]  : enable concurrent NMB accesses from Host
            * [2]  : enable concurrent JTAG accesses
            * [4]  : load frame buffers
            * [8]  : ADC A playback enable
            * [9]  : ADC B playback enable
            * [10] : ADC C playback enable
            *
            *********************************************************************/
            6'b111100: hrdata <= reserved0;
           
            /*********************************************************************
            * Reserved1
            *********************************************************************/
            6'b111101: hrdata <= reserved1;
            
            default:   ;                                                          
                                                                                  
          endcase                                                                 
        
        end
      
      end
    
    end
  
  end

endmodule


