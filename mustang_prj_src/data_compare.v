//**********************************************************
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
//
// ProjectName :
// target      :
// FileName    : 
// Author      :fengmaoqiao 
// E_mail      :fengmaoqiao@outwitcom.com 
// Date        :
// Version     :
//
// Modification history
//--------------------------------------------------------
// $Log:$
//
//
//**********************************************************
module data_rate_compute
(
  /* clock and reset */
  input             plf_clk                               ,
  input             mac_pi_clk                            ,  
  input             rst_n                                 ,
  /* user port */
  input     wire    s1_axis_fromhost_tvalid               ,               
  input     wire    s1_axis_fromhost_tkeep                ,
  input     wire    s1_axis_fromhost_tready               ,


  input     wire    [1:0]   mac_hmtrans                   ,
  input     wire            mac_hmwrite                   ,

  output    wire    [31:0]          dwords_mac_rdata      ,
  output    wire    [31:0]          dwords_fifo_wdata           
);

  /**********************************************************
  * Signal Declation
  **********************************************************/
  reg       [  31:0]           cn_data_fifo               ;
  reg       [  31:0]           cn_data_mac                ;

  wire                         fifo_wdata_valid           ;
  wire                         cn_data_fifo_end           ;

  wire                         mac_rdata_valid            ;
  wire                         cn_data_mac_end            ;
  /***********************************************************
  * Combination logic declation
  ***********************************************************/
  assign    dwords_fifo_wdata = cn_data_fifo;
  assign    dwords_mac_rdata  = cn_data_mac;
  /**********************************************************
  * Main Code
  **********************************************************/

  /***********************************************************
  * compute the dword which dinidma reads from AXI_FIFO
  ***********************************************************/

  /* Combination Logic */
  assign fifo_wdata_valid = s1_axis_fromhost_tvalid && (s1_axis_fromhost_tkeep != 8'hffff) && s1_axis_fromhost_tready; 
  assign cn_data_fifo_end = (cn_data_fifo == 32'hffff_ffff);

  /* Counter for mac data */
  always @(posedge plf_clk or negedge rst_n)
  begin
    if(!rst_n)begin  
      cn_data_fifo  <= 32'd0;
    end
    else begin
      if(fifo_wdata_valid)
      begin
        if(~cn_data_fifo_end)
          cn_data_fifo  <= cn_data_fifo + 1;
        else
          cn_data_fifo  <= 32'd0;
      end
      else
        ;  
    end
  end

  /***********************************************************
  * compute the dwords which machw reads from SRAM
  ***********************************************************/
 
  /* Combination Logic */
  assign cn_data_mac_end = (cn_data_mac == 32'hffff_ffff);
  assign mac_rdata_valid = (mac_hmtrans == 2'b10 & ~mac_hmwrite)

  /* Counter for mac data */
  always @(posedge mac_pi_clk or negedge rst_n)
  begin
    if(!rst_n)begin
      cn_data_mac <= 32'd0;
    end
    else begin
      if(mac_rdata_valid)
      begin
        if(~cn_data_mac_end)
          cn_data_mac <= cn_data_mac + 1;
        else
          cn_data_mac <= 32'd0;
      end
      else
        ;
    end
  end


endmodule



