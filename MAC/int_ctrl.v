//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author: jvanthou $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: 16264 $
// $Date: 2014-09-29 15:10:24 +0200 (Mon, 29 Sep 2014) $
// ---------------------------------------------------------------------------
// Dependencies     : None
// Description      : Top level of int_cntl module
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
// $HeadURL: https://svn.frso.rivierawaves.com/svn/rw_wlan_nx/trunk/Projects/WLAN_NX_REF_IP/HW/SB/int_cntl/verilog/rtl/int_cntl.v $
//
//////////////////////////////////////////////////////////////////////////////

module int_cntl
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire                   rst_n,
  input  wire                   clk,

  /*****************************************************************************
  * AHB slave interface
  *****************************************************************************/
  input  wire                   hsel,
  input  wire                   hready_in,
  input  wire [7:0]             haddr,
  input  wire [1:0]             htrans,
  input  wire                   hwrite,
  input  wire [31:0]            hwdata,
  output reg  [31:0]            hrdata,
  output wire [1:0]             hresp,
  output wire                   hready,

  /*****************************************************************************
  * Interrupt sources
  *****************************************************************************/
  input  wire [63:0]            irq_source,
  
  /*****************************************************************************
  * Processor interrupt lines
  *****************************************************************************/
  output reg                    irq_n
);
 

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
  // wires 
  wire [63:0]   irq_status_comb;
  reg  [63:0]   irq_status;
  wire [63:0]   irq_raw_status_comb;
  reg  [63:0]   irq_raw_status;
  reg  [ 5:0]   irq_index;
  
  // registers 
  reg  [63:0]   irq_mask;
  reg  [63:0]   irq_polarity;
  reg           write_pending;
  reg  [ 5:0]   addr_pending;




//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

  ////////////////////////////////////////////////////////////////////////////
  // assignments  
  ////////////////////////////////////////////////////////////////////////////
  assign hready = 1'b1;
  assign hresp  = 2'b00;

  ////////////////////////////////////////////////////////////////////////////
  // Register Map
  //
  // 0      0x00 RO irq_status[31:0]
  // 1      0x04 RO irq_status[63:32]
  // 2      0x08 RO irq_raw_status[31:0]
  // 3      0x0C RO irq_raw_status[63:32]
  // 4      0x10 RW irq_unmask_set[31:0]
  // 5      0x14 RW irq_unmask_set[63:32]
  // 6      0x18 RW irq_unmask_clear[31:0]
  // 7      0x1C RW irq_unmask_clear[63:32]
  // 8      0x20 RW irq_polarity[31:0]     (1=active high / 0=active low)
  // 9      0x24 RW irq_polarity[63:32]    (1=active high / 0=active low)
  // 10-15          reserved
  // 16     0x40 RO irq_index
  // 17-31          reserved
  ////////////////////////////////////////////////////////////////////////////

  always @(posedge clk, negedge rst_n)
  begin
    if(rst_n==1'b0)
    begin
      irq_polarity  <= {64{1'b1}};
      irq_mask      <= 64'b0;
       
      hrdata       <= 32'b0;
      
      write_pending <= 1'b0;
      addr_pending  <= 6'b0;
    end
    else
    begin
     if(write_pending==1'b1)
      begin
        write_pending <= 1'b0;
        
        case(addr_pending)
          6'd4    :  irq_mask[31:0]      <= irq_mask[31:0]  | hwdata;
          6'd5    :  irq_mask[63:32]     <= irq_mask[63:32] | hwdata;
          6'd6    :  irq_mask[31:0]      <= irq_mask[31:0]  & (~hwdata);
          6'd7    :  irq_mask[63:32]     <= irq_mask[63:32] & (~hwdata);
          6'd8    :  irq_polarity[31:0]  <= hwdata;
          6'd9    :  irq_polarity[63:32] <= hwdata;
          default : ;
        endcase
      end
     
      if(hready_in==1'b1 && hsel==1'b1 && htrans[1]==1'b1)
      begin
        if(hwrite==1'b1)
        begin
          addr_pending  <= haddr[7:2];
          write_pending <= 1'b1;                  
        end
        else
        begin
          write_pending <= 1'b0;

          case(haddr[7:2])
             6'd0   :  hrdata <= irq_status[31:0];
             6'd1   :  hrdata <= irq_status[63:32];
             6'd2   :  hrdata <= irq_raw_status[31:0];
             6'd3   :  hrdata <= irq_raw_status[63:32];
             6'd4   :  hrdata <= irq_mask[31:0];
             6'd5   :  hrdata <= irq_mask[63:32];
             6'd6   :  hrdata <= irq_mask[31:0];
             6'd7   :  hrdata <= irq_mask[63:32];
             6'd8   :  hrdata <= irq_polarity[31:0];
             6'd9   :  hrdata <= irq_polarity[63:32];
            6'd16   :  hrdata <= {26'b0,irq_index};
            default :  hrdata <= 32'b0;
          endcase
        end
      end
    end
  end
  
  ////////////////////////////////////////////////////////////////////////////
  // Interrution line generation 
  ////////////////////////////////////////////////////////////////////////////
  assign irq_raw_status_comb  = irq_source^(~irq_polarity);
  assign irq_status_comb     = irq_raw_status_comb&irq_mask;

  always @(posedge clk, negedge rst_n)
  begin
    if(rst_n==1'b0)
    begin
      irq_n        <= 1'b1;
      irq_status    <= 64'b0;
      irq_raw_status <= 64'b0;
    end
    else
    begin
      irq_n        <= ~(|irq_status_comb);
      irq_status    <= irq_status_comb;
      irq_raw_status <= irq_raw_status_comb;
    end
  end

  ////////////////////////////////////////////////////////////////////////////
  // IRQ_index priority decoders
  ////////////////////////////////////////////////////////////////////////////
  always @(*)
  begin:priority_decoders
  
    integer i;
   
    irq_index = 6'd0;
    
    for(i=0;i<64;i=i+1)
    begin
      if(irq_status[i]==1'b1) 
        irq_index = i;
    end
  end

endmodule

//////////////////////////////////////////////////////////////////////////////
// End of file
//////////////////////////////////////////////////////////////////////////////
