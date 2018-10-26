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
// Description      : Top level of ipc module
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
module ipc
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire        rst_n,
  input  wire        clk,

  /*****************************************************************************
  * AHB interface
  *****************************************************************************/
  input  wire        hready_in,
  input  wire        hsel,
  input  wire [8:0]  haddr,
  input  wire [1:0]  htrans, 
  input  wire        hwrite,
  output reg  [31:0] hrdata,
  input  wire [31:0] hwdata,
  output wire        hready,
  output wire [1:0]  hresp,

  /*****************************************************************************
  * Interrupt lines
  *****************************************************************************/
  output wire [3:0]  app2emb_irq,
  output wire        emb2app_irq

);
  /*****************************************************************************
  * declarations
  *****************************************************************************/
  /* host dedicated register */
  reg [15:0] app2emb_rawstatus;
  reg [15:0] emb2app_enable;
  
  /* firmware dedicated register */
  reg [15:0] emb2app_rawstatus;
  reg [15:0] app2emb_enable;
  reg [31:0] app2emb_linesel;

  /* write control */
  reg [ 6:0] addr;
  reg        write_pending;

  /* */
  wire [15:0] app2emb_irq0;
  wire [15:0] app2emb_irq1;
  wire [15:0] app2emb_irq2;
  wire [15:0] app2emb_irq3;

  /*****************************************************************************
  * assignment
  *****************************************************************************/
  assign hready = 1'b1;
  assign hresp  = 2'b00;

  /*****************************************************************************
  * AHB FSM
  ******************************************************************************
  * IPC application side 
  *
  * Offset   Register                   Access
  *
  * 0x000    app2emb_trigger[15:0]      R/WTS
  * 0x004    emb2app_rawstatus[15:0]     R
  * 0x008    emb2app_ack[15:0]           WTC
  * 0x00C    emb2app_unmaskset[15:0]     R/WTS
  * 0x010    emb2app_unmaskclear[15:0]   R/WTC
  * 0x014    emb2app_status[15:0]        R
  *
  ******************************************************************************
  * IPC embedded side
  *
  * Offset   Register                    Access
  *
  * 0x100    emb2app_trigger[15:0]        R/WTS
  * 0x104    app2emb_rawstatus[15:0]     R
  * 0x108    app2emb_ack[15:0]           WTC
  * 0x10C    app2emb_unmaskset[15:0]     R/WTS
  * 0x110    app2emb_unmaskclear[15:0]   R/WTC
  * 0x114    app2emb_linesel[31:0]       R/W
  * 0x118    app2emb_status[15:0]        R
  *
  *****************************************************************************/
  always @(posedge clk, negedge rst_n)
  begin
  
    if(rst_n==1'b0)
    begin
    
      /* firmware dedicated registers */
      app2emb_rawstatus <= 16'b0;
      emb2app_enable    <= 16'b0;
        
      /* host dedicated registers */
      emb2app_rawstatus <= 16'b0;
      app2emb_enable    <= 16'b0;
      app2emb_linesel   <= 32'b0;
      
      /* state */
      write_pending     <= 1'b0;
      addr              <= 7'b0;
      
      hrdata            <= 32'b0;
   
    end
    else
    begin
    
      if(hready_in==1'b1)
      begin
      
        if(write_pending==1'b1)
        begin
       
          write_pending <= 1'b0;
        
          case(addr)                                                                 
                                                                                           
            /* host dedicated registers */                                                   
            7'b0_0000_00: app2emb_rawstatus <= app2emb_rawstatus | hwdata[15:0];
            7'b0_0000_10: emb2app_rawstatus <= emb2app_rawstatus & ~hwdata[15:0];
            7'b0_0000_11: emb2app_enable    <= emb2app_enable    | hwdata[15:0];
            7'b0_0001_00: emb2app_enable    <= emb2app_enable    & ~hwdata[15:0];
            /* embedded dedicated registers */
            7'b1_0000_00: emb2app_rawstatus <= emb2app_rawstatus | hwdata[15:0];                     
            7'b1_0000_10: app2emb_rawstatus <= app2emb_rawstatus & ~hwdata[15:0]; 
            7'b1_0000_11: app2emb_enable    <= app2emb_enable    | hwdata[15:0]; 
            7'b1_0001_00: app2emb_enable    <= app2emb_enable    & ~hwdata[15:0]; 
            7'b1_0001_01: app2emb_linesel   <= hwdata; 
            default:      ;                                      
                                                                                           
          endcase                                                                          
          
        end
        
        if(hsel==1'b1 && htrans[1]==1'b1)
        begin
        
          if(hwrite==1'b0)
          begin
          
            case(haddr[8:2])
            
              /* host dedicated registers */
              7'b0_0000_00: hrdata <= {16'b0,app2emb_rawstatus[15:0]};
              7'b0_0000_01: hrdata <= {16'b0,emb2app_rawstatus[15:0]}; 
              7'b0_0000_11,
              7'b0_0001_00: hrdata <= {16'b0,emb2app_enable[15:0]};
              7'b0_0001_01: hrdata <= {16'b0,emb2app_rawstatus[15:0] & emb2app_enable[15:0]};
              /* embedded dedicated registers */
              7'b1_0000_00: hrdata <= {16'b0,emb2app_rawstatus[15:0]};
              7'b1_0000_01: hrdata <= {16'b0,app2emb_rawstatus[15:0]};
              7'b1_0000_11,
              7'b1_0001_00: hrdata <= {16'b0,app2emb_enable[15:0]};
              7'b1_0001_01: hrdata <= app2emb_linesel;
              7'b1_0001_10: hrdata <= {16'b0,app2emb_enable[15:0]&app2emb_rawstatus[15:0]};
              default:      hrdata <= 32'b00000000;
              
            endcase
          
          end
          else
          begin
          
            write_pending <= 1'b1;
            addr          <= haddr[8:2];
          
          end
        
        end
      
      end
    
    end
  
  end

  /******************************************************************************
  * embedded interrupt lines
  ******************************************************************************/
  generate
  begin:g_app2emb_lines
    
    genvar i;
    
    for(i=0;i<16;i=i+1)
    begin
    
      assign app2emb_irq0[i] = app2emb_rawstatus[i] & app2emb_enable[i] & app2emb_linesel[2*i+1:2*i]==2'b00;
      assign app2emb_irq1[i] = app2emb_rawstatus[i] & app2emb_enable[i] & app2emb_linesel[2*i+1:2*i]==2'b01;
      assign app2emb_irq2[i] = app2emb_rawstatus[i] & app2emb_enable[i] & app2emb_linesel[2*i+1:2*i]==2'b10;
      assign app2emb_irq3[i] = app2emb_rawstatus[i] & app2emb_enable[i] & app2emb_linesel[2*i+1:2*i]==2'b11;
    
    end
  
  end
  endgenerate

  assign app2emb_irq[0] = |app2emb_irq0;
  assign app2emb_irq[1] = |app2emb_irq1;
  assign app2emb_irq[2] = |app2emb_irq2;
  assign app2emb_irq[3] = |app2emb_irq3;

  /******************************************************************************
  * embedded interrupt lines
  ******************************************************************************/
  assign emb2app_irq = |(emb2app_rawstatus & emb2app_enable);

endmodule
