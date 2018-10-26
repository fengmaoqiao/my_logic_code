
//**********************************************************
//
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
//
// ProjectName :
// Target      :
// FileName    : rw_nx_platform.v
// Author      : qiupeng
// E_mail      : qiupeng@outwitcom.com
// Date        :
// Version     :
// Description :
// Modification history
//--------------------------------------------------------
// $Log:$
//
//
//**********************************************************
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"

`default_nettype wire


  module rw_nx_platform #
    (
    parameter G_DATA_WIDTH = 64,
    parameter MAC_ENABLE = 1'b0,
    parameter PHY_ENABLE = 1'b0
    ) 
    (
        //clock and reset
        input                       por_rst_n                       ,
        
        
        input                         clk_32k                       ,
        
        input                         clk_30m                       ,
        
        input                         clk_80m                       ,        
        input                         clk_200m                      ,
        //interrupt sources
        output                      host_irq                        ,
        //modified by fengmaoqiao begin
        output  [95:20]             proc_irq                        ,
        output  [29:0]             mb_irq                           ,
        
        output  [3:0]               ipc_irq_tomb                    ,
        output  [13:0]              lli_irq_tomb                    ,
        output  [3:0]               dma_channle_irq_tomb            ,
        output  [5:0]               mac_irq_tomb                    ,
        output  [1:0]               reserve_irq_tomb                ,
        //modified by fengmaoqiao end
        output                      cpu_single_irq                  ,
        //proc_ahb
        (*syn_keep = "true" , mark_debug = "true" *)
        output                      proc_hready                     ,
        (*syn_keep = "true" , mark_debug = "true" *)
        input   [31:0]              proc_haddr                      ,
        (*syn_keep = "true" , mark_debug = "true" *)
        input   [ 1:0]              proc_htrans                     ,
        (*syn_keep = "true" , mark_debug = "true" *)                
        input                       proc_hwrite                     ,
        (*syn_keep = "true" , mark_debug = "true" *)                
        input   [ 1:0]              proc_hsize                      ,   
        (*syn_keep = "true" , mark_debug = "true" *)                
        output  [31:0]              proc_hrdata                     ,
        (*syn_keep = "true" , mark_debug = "true" *)
        input   [31:0]              proc_hwdata                     ,
        output  [ 1:0]              proc_hresp                      ,
        
        //add by fengmaoqiao
        //ahb signal no use
        input       proc_ready_in           ,
        input       proc_sel                ,
        input       proc_hprot              ,
        input       proc_hburst             ,                
        
        //axis Interface to dinidma Interface
        //upstream
        input               s0_axis_fromhost_tvalid     ,
        output              s0_axis_fromhost_tready     ,
        input  [63:0]       s0_axis_fromhost_tdata      , 
        input  [7:0]        s0_axis_fromhost_tkeep      ,
        input               s0_axis_fromhost_tlast      ,
         
        output              m0_axis_tohost_tvalid       ,
        input               m0_axis_tohost_tready       ,
        output [63:0]       m0_axis_tohost_tdata        ,
        output [7:0]        m0_axis_tohost_tkeep        ,
        output              m0_axis_tohost_tlast        ,
        //downstream 
        input               s1_axis_fromhost_tvalid     ,
        output              s1_axis_fromhost_tready     ,
        input  [63:0]       s1_axis_fromhost_tdata      ,
        input  [7:0]        s1_axis_fromhost_tkeep      ,
        input               s1_axis_fromhost_tlast      ,
  
        output                  m1_axis_tohost_tvalid  ,
        input                   m1_axis_tohost_tready  ,
        output [63:0]           m1_axis_tohost_tdata  ,
        output [7:0]            m1_axis_tohost_tkeep  ,
        output                  m1_axis_tohost_tlast  ,
      
        //   phy if    
        output                  test_1018_1508,
        output    [7:0]         error_count
        
        );

//**********************************************************
//Signal declarations
//**********************************************************
//proc_ahb
wire                        proc_hsel_default                   ;
wire                        proc_hsel_ipc                       ;
wire [31:0]                 proc_hrdata_ipc                     ;
wire [ 1:0]                 proc_hresp_ipc                      ;
wire                        proc_hready_ipc                     ;
wire                        proc_hsel_systctrl                  ;
wire [31:0]                 proc_hrdata_systctrl                ;
wire [ 1:0]                 proc_hresp_systctrl                 ;
wire                        proc_hready_systctrl                ;
wire                        proc_hsel_intctrl                   ;
wire [31:0]                 proc_hrdata_intctrl                 ;
wire [ 1:0]                 proc_hresp_intctrl                  ;
wire                        proc_hready_intctrl                 ;
wire                        proc_hsel_ram                       ;
wire [31:0]                 proc_hrdata_ram                     ;
wire [ 1:0]                 proc_hresp_ram                      ;
wire                        proc_hready_ram                     ;
wire                        proc_hsel_dma                       ;
wire [31:0]                 proc_hrdata_dma                     ;
wire [ 1:0]                 proc_hresp_dma                      ;
wire                        proc_hready_dma                     ;
wire                        proc_hsel_mac                       ;
wire [31:0]                 proc_hrdata_mac                     ;
wire [ 1:0]                 proc_hresp_mac                      ;
wire                        proc_hready_mac                     ;
wire                        proc_hsel_phy                       ;
wire [31:0]                 proc_hrdata_phy                     ;
wire [ 1:0]                 proc_hresp_phy                      ;
wire                        proc_hready_phy                     ;
reg                         proc_hsel_ram_1t                    ;
reg                         proc_hsel_dma_1t                    ;
reg                         proc_hsel_ipc_1t                    ;
reg                         proc_hsel_mac_1t                    ;
reg                         proc_hsel_phy_1t                    ;
reg                         proc_hsel_la_1t                     ;
reg                         proc_hsel_systctrl_1t               ;
reg                         proc_hsel_intctrl_1t                ;
reg                         proc_hsel_default_1t                ;
//interrupts
wire                        phy_irq_n                           ;//Interrupt from PHY
wire                        rc_irq_n                            ;//Interrupt from Radio Controller
wire    [ 3:0]              ipc_irq                             ;
wire    [15:0]              dma_lli_irq                         ;
wire    [ 3:0]              dma_channel_irq                     ;
wire                        dma_error_irq                       ;

(* syn_keep="true" *)wire                        mac_int_gen_n                       ;
(* syn_keep="true" *)wire                        mac_int_prot_trigger_n              ;
(* syn_keep="true" *)wire                        mac_int_tx_trigger_n                ;
(* syn_keep="true" *)wire                        mac_int_rx_trigger_n                ;
(* syn_keep="true" *)wire                        mac_int_tx_rx_misc_n                ;
(* syn_keep="true" *)wire                        mac_int_tx_rx_timer_n               ;

wire    [63:0]              irq_source                          ;
//
wire                        reg_fpgaa_reset_req                 ;
wire                        reg_bootrom_enable                  ;
wire                        reg_fpgab_reset_req                 ;
wire                        plf_rst_n                           ;
wire                        mac_core_rst_n                      ;
wire                        mac_wt_rst_n                        ;
wire                        mpif_rst_n                          ;
wire                        jtag_clk                            ;
wire                        tap_drck                            ;
wire                        plf_clk                             ;
wire                        mac_pi_free_clk                     ;
wire                        mac_pi_clk                          ;
wire                        mac_pi_tx_clk                       ;
wire                        mac_pi_rx_clk                       ;
wire                        mac_core_free_clk                   ;
wire                        mac_core_clk                        ;
wire                        mac_core_tx_clk                     ;
wire                        mac_core_rx_clk                     ;
wire                        mac_crypt_clk                       ;
wire                        mac_lp_clk                          ;
wire                        mac_wt_free_clk                     ;
wire                        mac_wt_clk                          ;
wire                        mpif_free_clk                       ;
wire                        mpif_clk                            ;
wire                        reg_mac_pi_clk_gating_en            ;
wire                        reg_mac_pi_tx_clk_gating_en         ;
wire                        reg_mac_pi_rx_clk_gating_en         ;
wire                        reg_mac_crypt_clk_gating_en         ;
wire                        reg_mac_core_clk_gating_en          ;
wire                        reg_mac_core_tx_clk_gating_en       ;
wire                        reg_mac_core_rx_clk_gating_en       ;
wire                        reg_mac_wt_clk_gating_en            ;
wire                        reg_mpif_clk_gating_en              ;
wire                        mac_pri_clken                       ;
wire                        platform_wake_up                    ;
wire                        mac_pi_tx_clken                     ;
wire                        mac_pi_rx_clken                     ;
wire                        mac_core_tx_clken                   ;
wire                        mac_core_rx_clken                   ;
wire                        mac_crypt_clken                     ;
wire                        mac_lp_clkswitch                    ;
wire                        mac_wt_clken                        ;
wire                        mpif_clken                          ;
//dma0_ahb
wire                        dma0_ready                          ;
wire [31:0]                 dma0_addr                           ;
wire                        dma0_trans                          ;
wire [63:0]                 dma0_rdata                          ;
//dma1_ahb
wire                        dma1_ready                          ;
wire [31:0]                 dma1_addr                           ;
wire                        dma1_trans                          ;
wire [ 7:0]                 dma1_we                             ;
wire [63:0]                 dma1_wdata                          ;
//dma2_ahb
wire                        dma2_hready                         ;
wire    [31:0]              dma2_haddr                          ;
wire    [1:0]               dma2_htrans                         ;
wire    [31:0]              dma2_hrdata                         ;
wire    [ 1:0]              dma2_hresp                          ;
wire                        dma2_hsel_default                   ;
wire                        dma2_hsel_phy                       ;
wire    [31:0]              dma2_hrdata_phy                     ;
wire    [ 1:0]              dma2_hresp_phy                      ;
wire                        dma2_hready_phy                     ;
reg                         dma2_hsel_phy_1t                    ;
reg                         dma2_hsel_default_1t                ;

//lli_ahb
wire                        lli_hready                          ;
wire    [31:0]              lli_haddr                           ;
wire    [1:0]               lli_htrans                          ;
wire    [31:0]              lli_hrdata                          ;
//mac_ahb
wire                        mac_hmsel                           ;
wire    [31:0]              mac_hmaddr                          ;
wire    [ 1:0]              mac_hmtrans                         ;
wire                        mac_hmwrite                         ;
wire    [ 2:0]              mac_hmsize                          ;
wire    [31:0]              mac_hmrdata                         ;
wire    [31:0]              mac_hmwdata                         ;
wire    [ 1:0]              mac_hmresp                          ;
wire                        mac_hmready                         ;
//phy_ahb
wire                        phy_hready_in                       ;
wire                        phy_hsel                            ;
wire    [27:0]              phy_haddr                           ;
wire    [ 1:0]              phy_htrans                          ;
wire                        phy_hwrite                          ;
wire    [ 1:0]              phy_hsize                           ;
wire    [31:0]              phy_hwdata                          ;
wire    [31:0]              phy_hrdata                          ;
wire    [ 1:0]              phy_hresp                           ;
wire                        phy_hready                          ;
//mpif
wire                        phyRdy                              ;        
wire                        txEnd_p                             ;
wire    [ 7:0]              rxData                              ;
wire                        phy_cca_ind_medium                  ;
wire                        CCAPrimary20                        ;
wire                        CCASecondary20                      ;               
wire                        CCASecondary40                      ;               
wire                        CCASecondary80                      ;               
wire                        rxEndForTiming_p                    ;
wire                        rxErr_p                             ;
wire                        rxEnd_p                             ;
wire                        phyErr_p                            ;
wire                        rifsRxDetected                      ;
wire                        txReq                               ; 
wire                        rxReq                               ;         
wire    [ 7:0]              txData                              ;                        
wire                        macDataValid                        ;
wire                        mimoCmdValid                        ; 
wire                        keepRFOn                            ;                     
//memory
wire                        shared_ram_en                       ;
wire    [14:0]              shared_ram_addr                     ;
wire    [ 7:0]              shared_ram_wr_en                    ;
wire    [63:0]              shared_ram_wr_data                  ;
wire    [63:0]              shared_ram_rd_data                  ;
wire                        tx_fifo_rd_en                       ;
wire    [ 5:0]              tx_fifo_rd_addr                     ;
wire    [37:0]              tx_fifo_rd_data                     ;
wire                        tx_fifo_wr_en                       ;
wire    [ 5:0]              tx_fifo_wr_addr                     ;
wire    [37:0]              tx_fifo_wr_data                     ;
wire                        rx_fifo_rd_en                       ; 
wire    [ 5:0]              rx_fifo_rd_addr                     ;
wire    [35:0]              rx_fifo_rd_data                     ;
wire                        rx_fifo_wr_en                       ;
wire    [ 5:0]              rx_fifo_wr_addr                     ;
wire    [35:0]              rx_fifo_wr_data                     ;
wire                        keystorage_en                       ;
wire                        keystorage_wr_en                    ;
wire    [ 5:0]              keystorage_addr                     ;
`ifdef RW_WAPI_EN
wire    [314:0]             keystorage_rd_data                  ;
wire    [314:0]             keystorage_wr_data                  ;
`else
wire    [186:0]             keystorage_rd_data                  ;
wire    [186:0]             keystorage_wr_data                  ;
`endif
wire                        sboxa_en                            ;
wire                        sboxa_wr_en                         ;
wire    [ 7:0]              sboxa_addr                          ;
wire    [ 7:0]              sboxa_rd_data                       ;
wire    [ 7:0]              sboxa_wr_data                       ; 
wire                        sboxb_en                            ;
wire                        sboxb_wr_en                         ;
wire    [ 7:0]              sboxb_addr                          ;
wire    [ 7:0]              sboxb_rd_data                       ;
wire    [ 7:0]              sboxb_wr_data                       ;
wire                        mpif_tx_fifo_rd_en                  ;
wire    [ 6:0]              mpif_tx_fifo_rd_addr                ;
wire    [ 7:0]              mpif_tx_fifo_rd_data                ;
wire                        mpif_tx_fifo_wr_en                  ;
wire    [ 6:0]              mpif_tx_fifo_wr_addr                ;
wire    [ 7:0]              mpif_tx_fifo_wr_data                ;
wire                        mpif_rx_fifo_rd_en                  ;
wire    [ 6:0]              mpif_rx_fifo_rd_addr                ;
wire    [ 7:0]              mpif_rx_fifo_rd_data                ;
wire                        mpif_rx_fifo_wr_en                  ;
wire    [ 6:0]              mpif_rx_fifo_wr_addr                ;
wire    [ 7:0]              mpif_rx_fifo_wr_data                ;
wire                        encrypt_rx_fifo_rd_en               ;
wire    [ 6:0]              encrypt_rx_fifo_rd_addr             ;
wire    [ 7:0]              encrypt_rx_fifo_rd_data             ;
wire                        encrypt_rx_fifo_wr_en               ;
wire    [ 6:0]              encrypt_rx_fifo_wr_addr             ;
wire    [ 7:0]              encrypt_rx_fifo_wr_data             ;
wire                        ps_bitmap_en                        ;
wire    [ 1:0]              ps_bitmap_addr                      ;
wire    [87:0]              ps_bitmap_rd_data                   ;
wire                        ps_bitmap_wr_en                     ;
wire    [87:0]              ps_bitmap_wr_data                   ;
wire                        mib_table_en                        ;
wire                        mib_table_wr_en                     ;
wire    [ 7:0]              mib_table_addr                      ;
wire    [31:0]              mib_table_rd_data                   ;
wire    [31:0]              mib_table_wr_data                   ;

//---------------- phy --------------------------------------------
wire    [31:0]              phy_prdata_if                       ;
wire    [31:0]              phy_prdata_radio                    ;             
wire    [31:0]              phy_prdata_frontend                 ;               
wire    [31:0]              phy_prdata_modema                   ;
wire    [31:0]              phy_prdata_modemg                   ;

wire    [31:0]              phy_pwdata;
wire                        phy_penable;
wire    [31:0]              phy_paddr;
wire                        phy_pwrite;
wire                        phy_psel_modema;
wire                        phy_psel_modemg;
wire                        phy_psel_radio;
wire                        phy_psel_frontend;
wire                        phy_psel_macphy_if;

//interruption sources mapping
assign proc_irq[95:80]      = 'b0;//reserved                                
assign proc_irq[79:72]      = 'b0;
assign proc_irq[71]         = ~rc_irq_n;
assign proc_irq[70]         = ~phy_irq_n;
assign proc_irq[69:64]      = 'b0;                                     
assign proc_irq[63:60]      = ipc_irq[3:0];                                       
assign proc_irq[59:56]      = 'b0;                                     
assign proc_irq[55]         = ~mac_int_prot_trigger_n;                                     
assign proc_irq[54]         = ~mac_int_gen_n;                                             
assign proc_irq[53]         = ~mac_int_tx_trigger_n;                                       
assign proc_irq[52]         = ~mac_int_rx_trigger_n;                                       
assign proc_irq[51]         = ~mac_int_tx_rx_misc_n;                                        
assign proc_irq[50]         = ~mac_int_tx_rx_timer_n;                                       
assign proc_irq[49:41]      = 'b0;
assign proc_irq[40]         = dma_error_irq;
assign proc_irq[39:24]      = dma_lli_irq[15:0];
assign proc_irq[23:20]      = dma_channel_irq[3:0];

assign irq_source[9:0]      = 10'b0;
assign irq_source[10]       = ~phy_irq_n;
assign irq_source[11]       = ~rc_irq_n;
assign irq_source[19:12]    = 8'b0;
assign irq_source[63:20]    = proc_irq[63:20];


//assign mb_irq[32]          = ~rc_irq_n;

assign mb_irq[29]          = ~phy_irq_n;
assign mb_irq[28:25]          = ipc_irq[3:0];

assign mb_irq[24]          = ~mac_int_prot_trigger_n;
assign mb_irq[23]          = ~mac_int_gen_n;
assign mb_irq[22]          = ~mac_int_tx_trigger_n;
assign mb_irq[21]          = ~mac_int_rx_trigger_n;
assign mb_irq[20]          = ~mac_int_tx_rx_misc_n;
assign mb_irq[19]          = ~mac_int_tx_rx_timer_n;

assign mb_irq[18]          = dma_error_irq;
assign mb_irq[17:4]          = dma_lli_irq[13:0];
assign mb_irq[3:0]          = dma_channel_irq[3:0];


assign ipc_irq_tomb[3:0]            =ipc_irq[3:0];
assign lli_irq_tomb[13:0]           = dma_lli_irq[13:0];
assign dma_channle_irq_tomb[3:0]    = dma_channel_irq[3:0];

(* syn_keep = "true" *)assign mac_irq_tomb[5]            = (~mac_int_prot_trigger_n);
(* syn_keep = "true" *)assign mac_irq_tomb[4]            = (~mac_int_gen_n);
(* syn_keep = "true" *)assign mac_irq_tomb[3]            = (~mac_int_tx_trigger_n);
(* syn_keep = "true" *)assign mac_irq_tomb[2]            = (~mac_int_rx_trigger_n);
(* syn_keep = "true" *)assign mac_irq_tomb[1]            = (~mac_int_tx_rx_misc_n);
(* syn_keep = "true" *)assign mac_irq_tomb[0]            = (~mac_int_tx_rx_timer_n);
//**********************************************************
// processor ahb infrastructure
// 0x.00000000 : shared ram
// 0x.00800000 : IPC 
// 0x.00900000 : system controller
// 0x.00910000 : interrupt controller
// 0x.00A00000 : dma
// 0x.00B00000 : MAC
// 0x.00C00000 : PHY
// 0x.00D00000 : reserved
// 0x.00F00000 : reserved
//**********************************************************
assign proc_hsel_ram        = (proc_haddr>=32'h60000000) && (proc_haddr<=32'h607fffff);
assign proc_hsel_ipc        = (proc_haddr>=32'h60800000) && (proc_haddr<=32'h608fffff);
assign proc_hsel_systctrl   = (proc_haddr>=32'h60900000) && (proc_haddr<=32'h6090ffff);
assign proc_hsel_intctrl    = (proc_haddr>=32'h60910000) && (proc_haddr<=32'h6091ffff);
assign proc_hsel_dma        = (proc_haddr>=32'h60a00000) && (proc_haddr<=32'h60afffff);
assign proc_hsel_mac        = (proc_haddr>=32'h60b00000) && (proc_haddr<=32'h60bfffff);
assign proc_hsel_phy        = (proc_haddr>=32'h60c00000) && (proc_haddr<=32'h60cfffff);
//assign proc_hsel_ram        = proc_haddr[24:23]==2'b00;
//assign proc_hsel_ipc        = proc_haddr[24:23]==2'b01 && proc_haddr[22:20]==3'b000;
//assign proc_hsel_systctrl   = proc_haddr[24:23]==2'b01 && proc_haddr[22:20]==3'b001 && proc_haddr[19:16]==4'b0000;
//assign proc_hsel_intctrl    = proc_haddr[24:23]==2'b01 && proc_haddr[22:20]==3'b001 && proc_haddr[19:16]==4'b0001;
//assign proc_hsel_dma        = proc_haddr[24:23]==2'b01 && proc_haddr[22:20]==3'b010;
//assign proc_hsel_mac        = proc_haddr[24:23]==2'b01 && proc_haddr[22:20]==3'b011;
//assign proc_hsel_phy        = proc_haddr[24:23]==2'b01 && proc_haddr[22:20]==3'b100;
  
assign proc_hsel_default    = ~(proc_hsel_ram      | proc_hsel_ipc     |  
                                proc_hsel_systctrl | proc_hsel_intctrl | 
                                proc_hsel_dma      | proc_hsel_mac     | proc_hsel_phy);

assign proc_hready          =  proc_hready_ram       & proc_hready_ipc     &
                               proc_hready_systctrl  & proc_hready_intctrl &
                               proc_hready_dma       & proc_hready_mac & proc_hready_phy;

always @(posedge plf_clk or negedge plf_rst_n)
begin
    if(plf_rst_n==0)
    begin
        proc_hsel_ram_1t      <= 1'b0; 
        proc_hsel_ipc_1t      <= 1'b0; 
        proc_hsel_systctrl_1t <= 1'b0;   
        proc_hsel_intctrl_1t  <= 1'b0;   
        proc_hsel_dma_1t      <= 1'b0; 
        proc_hsel_mac_1t      <= 1'b0; 
        proc_hsel_phy_1t      <= 1'b0; 
        proc_hsel_default_1t  <= 1'b0;   
    end
    else if(proc_hready==1'b1 && proc_htrans[1]==1'b1)
    begin
        proc_hsel_ram_1t      <= proc_hsel_ram; 
        proc_hsel_ipc_1t      <= proc_hsel_ipc; 
        proc_hsel_systctrl_1t <= proc_hsel_systctrl;   
        proc_hsel_intctrl_1t  <= proc_hsel_intctrl;   
        proc_hsel_dma_1t      <= proc_hsel_dma; 
        proc_hsel_mac_1t      <= proc_hsel_mac; 
        proc_hsel_phy_1t      <= proc_hsel_phy; 
        proc_hsel_default_1t  <= proc_hsel_default;   
    end  
end
  
assign {proc_hresp,proc_hrdata} = {proc_hresp_ram,proc_hrdata_ram}           & {34{proc_hsel_ram_1t}}      |
                                  {proc_hresp_ipc,proc_hrdata_ipc}           & {34{proc_hsel_ipc_1t}}      |
                                  {proc_hresp_dma,proc_hrdata_dma}           & {34{proc_hsel_dma_1t}}      |
                                  {proc_hresp_mac,proc_hrdata_mac}           & {34{proc_hsel_mac_1t}}      |
                                  {proc_hresp_phy,proc_hrdata_phy}           & {34{proc_hsel_phy_1t}}      |
                                  {proc_hresp_systctrl,proc_hrdata_systctrl} & {34{proc_hsel_systctrl_1t}} |
                                  {proc_hresp_intctrl,proc_hrdata_intctrl}   & {34{proc_hsel_intctrl_1t}}  |
                                  {2'b00,32'hdead5555}                       & {34{proc_hsel_default_1t}};
   
//**********************************************************
//DMA Host ahb infrastructure
//0x.00C00000 : PHY
//**********************************************************
assign dma2_hsel_phy      = dma2_haddr[24:23]==2'b01 && dma2_haddr[22:20]==3'b100;
assign dma2_hsel_default  = ~(dma2_hsel_phy);
assign dma2_hready        = dma2_hready_phy;
  
always @(posedge plf_clk or negedge plf_rst_n)
begin
    if(plf_rst_n==0)
    begin
        dma2_hsel_phy_1t      <= 1'b0; 
        dma2_hsel_default_1t  <= 1'b0;
    end
    else if(dma2_hready==1'b1 && dma2_htrans[1]==1'b1)
    begin
        dma2_hsel_phy_1t      <= dma2_hsel_phy; 
        dma2_hsel_default_1t  <= dma2_hsel_default;   
    end  
    else
    begin
        dma2_hsel_phy_1t      <= dma2_hsel_phy_1t;
        dma2_hsel_default_1t  <= dma2_hsel_default_1t;
    end  
end
  
assign {dma2_hresp,dma2_hrdata} = {dma2_hresp_phy,dma2_hrdata_phy} & {34{dma2_hsel_phy_1t}}    |
                                  {2'b00,32'hdead5555}             & {34{dma2_hsel_default_1t}};

clock_ctrl  u_clock_ctrl (
                          //input
                          .por_rst_n                      (por_rst_n                      ),
                          .soft_reset_req_n               (~reg_fpgaa_reset_req           ),
                          .clk_32k                        (clk_80m                        ),
                          .clk_30m                        (clk_30m                        ),
                          .clk_80m                        (clk_80m                        ),
                          .clk_200m                       (clk_200m                        ),
                          //  
                          .modem_force20                  (1'b0                           ),
                          .platform_wake_up               (platform_wake_up               ),
                          .mac_pri_clken                  (mac_pri_clken                  ),
                          .mac_pi_tx_clken                (mac_pi_tx_clken                ),
                          .mac_pi_rx_clken                (mac_pi_rx_clken                ),
                          .mac_core_tx_clken              (mac_core_tx_clken              ),
                          .mac_core_rx_clken              (mac_core_rx_clken              ),
                          .mac_crypt_clken                (mac_crypt_clken                ),
                          .mac_wt_clken                   (mac_wt_clken                   ),
                          .mpif_clken                     (mpif_clken                     ),
                          .mac_lp_clkswitch               (mac_lp_clkswitch               ),        
                          .reg_mac_pi_clk_gating_en       (reg_mac_pi_clk_gating_en       ),
                          .reg_mac_pi_tx_clk_gating_en    (reg_mac_pi_tx_clk_gating_en    ),
                          .reg_mac_pi_rx_clk_gating_en    (reg_mac_pi_rx_clk_gating_en    ),
                          .reg_mac_core_clk_gating_en     (reg_mac_core_clk_gating_en     ),
                          .reg_mac_crypt_clk_gating_en    (reg_mac_crypt_clk_gating_en    ),
                          .reg_mac_core_rx_clk_gating_en  (reg_mac_core_rx_clk_gating_en  ),
                          .reg_mac_core_tx_clk_gating_en  (reg_mac_core_tx_clk_gating_en  ),
                          .reg_mac_wt_clk_gating_en       (reg_mac_wt_clk_gating_en       ),
                          .reg_mpif_clk_gating_en         (reg_mpif_clk_gating_en         ),
                          //output
                          .plf_rst_n                      (plf_rst_n                      ),
                          .mac_core_rst_n                 (mac_core_rst_n                 ),
                          .mac_wt_rst_n                   (mac_wt_rst_n                   ),
                          .mpif_rst_n                     (mpif_rst_n                     ),
                          .plf_clk                        (plf_clk                        ),
                          .mac_pi_free_clk                (mac_pi_free_clk                ),
                          .mac_pi_clk                     (mac_pi_clk                     ),
                          .mac_pi_tx_clk                  (mac_pi_tx_clk                  ),
                          .mac_pi_rx_clk                  (mac_pi_rx_clk                  ),
                          .mac_core_free_clk              (mac_core_free_clk              ),
                          .mac_core_clk                   (mac_core_clk                   ),
                          .mac_core_tx_clk                (mac_core_tx_clk                ),
                          .mac_core_rx_clk                (mac_core_rx_clk                ),
                          .mac_crypt_clk                  (mac_crypt_clk                  ),
                          .mac_lp_clk                     (mac_lp_clk                     ),
                          .mac_wt_free_clk                (mac_wt_free_clk                ),
                          .mac_wt_clk                     (mac_wt_clk                     ),
                          .mpif_free_clk                  (mpif_free_clk                  ),
                          .mpif_clk                       (mpif_clk                       )
                          );


//system controller
system_ctrl u_system_ctrl(
        //clock and reset
        .clk                            (plf_clk                        ),
        .rst_n                          (plf_rst_n                      ),
        //AHB interface
        .hready_in                      (proc_hready                    ),
        .hsel                           (proc_hsel_systctrl             ),
        .haddr                          (proc_haddr[9:0]                ),
        .htrans                         (proc_htrans                    ), 
        .hwrite                         (proc_hwrite                    ),
        .hrdata                         (proc_hrdata_systctrl           ),
        .hwdata                         (proc_hwdata                    ),
        .hready                         (proc_hready_systctrl           ),
        .hresp                          (proc_hresp_systctrl            ),
        //clock ctrl
        .reg_fpgaa_reset_req            (reg_fpgaa_reset_req            ),
        .reg_bootrom_enable             (reg_bootrom_enable             ),
        .reg_fpgab_reset_req            (reg_fpgab_reset_req            ),
        .reg_mac_pi_clk_gating_en       (reg_mac_pi_clk_gating_en       ), 
        .reg_mac_pi_tx_clk_gating_en    (reg_mac_pi_tx_clk_gating_en    ), 
        .reg_mac_pi_rx_clk_gating_en    (reg_mac_pi_rx_clk_gating_en    ), 
        .reg_mac_crypt_clk_gating_en    (reg_mac_crypt_clk_gating_en    ), 
        .reg_mac_core_clk_gating_en     (reg_mac_core_clk_gating_en     ), 
        .reg_mac_core_tx_clk_gating_en  (reg_mac_core_tx_clk_gating_en  ), 
        .reg_mac_core_rx_clk_gating_en  (reg_mac_core_rx_clk_gating_en  ), 
        .reg_mac_wt_clk_gating_en       (reg_mac_wt_clk_gating_en       ), 
        .reg_mpif_clk_gating_en         (reg_mpif_clk_gating_en         )
        );

//interrupt controller
int_cntl u_int_cntl(
        //clock and reset
        .clk                            (plf_clk                        ),
        .rst_n                          (plf_rst_n                      ),
        //AHB
        .hready_in                      (proc_hready                    ),
        .hsel                           (proc_hsel_intctrl              ),
        .haddr                          (proc_haddr[7:0]                ),
        .htrans                         (proc_htrans                    ), 
        .hwrite                         (proc_hwrite                    ),
        .hrdata                         (proc_hrdata_intctrl            ),
        .hwdata                         (proc_hwdata                    ),
        .hready                         (proc_hready_intctrl            ),
        .hresp                          (proc_hresp_intctrl             ),
        //Interrupt interface
        .irq_source                     (irq_source                     ),
        .irq_n                          (cpu_single_irq                 )
        );

//ipc
ipc u_ipc(
        //clock and reset
        .clk                            (plf_clk                        ),
        .rst_n                          (plf_rst_n                      ),
        //AHB interface
        .hready_in                      (proc_hready                    ),
        .hsel                           (proc_hsel_ipc                  ),
        .haddr                          (proc_haddr[8:0]                ),
        .htrans                         (proc_htrans                    ), 
        .hwrite                         (proc_hwrite                    ),
        .hrdata                         (proc_hrdata_ipc                ),
        .hwdata                         (proc_hwdata                    ),
        .hready                         (proc_hready_ipc                ),
        .hresp                          (proc_hresp_ipc                 ),
        //Interrupt lines
        .app2emb_irq                    (ipc_irq                        ),
        .emb2app_irq                    (host_irq                       )
        );


//dini_dma
rw_dini_dma u_rw_dini_dma(
        //clock and reset
        .clk                            (plf_clk                        ),
        .rst_n                          (plf_rst_n                      ),
        //interrupts
        .lli_irq                        (dma_lli_irq                    ),
        .channel_irq                    (dma_channel_irq                ),
        .error_irq                      (dma_error_irq                  ),
        //AHB slave (control registers)
        .hready_in_regb                 (proc_hready                    ),
        .hsel_regb                      (proc_hsel_dma                  ),
        .haddr_regb                     (proc_haddr[7:0]                ),
        .htrans_regb                    (proc_htrans                    ),
        .hwrite_regb                    (proc_hwrite                    ),
        .hrdata_regb                    (proc_hrdata_dma                ),
        .hwdata_regb                    (proc_hwdata                    ),
        .hresp_regb                     (proc_hresp_dma                 ),
        .hready_regb                    (proc_hready_dma                ),
        //AHB master (embeded sram)
        .hready_lli                     (lli_hready                     ),
        .haddr_lli                      (lli_haddr                      ),
        .htrans_lli                     (lli_htrans                     ),
        .hwrite_lli                     (                               ),
        .hrdata_lli                     (lli_hrdata                     ),
        .hresp_lli                      (2'b00                          ),
        //
        //Dinidma data bus
        .s0_axis_fromhost_tvalid    (s0_axis_fromhost_tvalid),
        .s0_axis_fromhost_tready    (s0_axis_fromhost_tready),
        .s0_axis_fromhost_tdata     (s0_axis_fromhost_tdata),
        .s0_axis_fromhost_tkeep     (s0_axis_fromhost_tkeep),
        .s0_axis_fromhost_tlast     (s0_axis_fromhost_tlast),
         
        .m0_axis_tohost_tvalid      (m0_axis_tohost_tvalid),
        .m0_axis_tohost_tready      (m0_axis_tohost_tready),
        .m0_axis_tohost_tdata       (m0_axis_tohost_tdata),
        .m0_axis_tohost_tkeep       (m0_axis_tohost_tkeep),
        .m0_axis_tohost_tlast       (m0_axis_tohost_tlast),
         
        .s1_axis_fromhost_tvalid    (s1_axis_fromhost_tvalid),
        .s1_axis_fromhost_tready    (s1_axis_fromhost_tready),
        .s1_axis_fromhost_tdata     (s1_axis_fromhost_tdata),
        .s1_axis_fromhost_tkeep     (s1_axis_fromhost_tkeep),
        .s1_axis_fromhost_tlast     (s1_axis_fromhost_tlast),
   
    
        .m1_axis_tohost_tvalid      (m1_axis_tohost_tvalid),
        .m1_axis_tohost_tready      (m1_axis_tohost_tready),
        .m1_axis_tohost_tdata       (m1_axis_tohost_tdata),
        .m1_axis_tohost_tkeep       (m1_axis_tohost_tkeep),
        .m1_axis_tohost_tlast       (m1_axis_tohost_tlast),       
        
        //ABH memory map 
        .hready_upstream                (dma2_hready                    ),
        .haddr_upstream                 (dma2_haddr                     ),
        .htrans_upstream                (dma2_htrans                    ),
        .hrdata_upstream                (dma2_hrdata                    ),
        //Bus interfaces : upstream
        .dma0_ready                     (dma0_ready                     ),
        .dma0_addr                      (dma0_addr                      ),
        .dma0_trans                     (dma0_trans                     ),
        .dma0_rdata                     (dma0_rdata                     ),
        //Bus interfaces : downstream
        .dma1_ready                     (dma1_ready                     ),
        .dma1_addr                      (dma1_addr                      ),
        .dma1_trans                     (dma1_trans                     ),
        .dma1_we                        (dma1_we                        ),
        .dma1_wdata                     (dma1_wdata                     )
        );

//sram_mpa
sram_mpa #(
        .g_addr_width                   (18                             )
        ) u_sram_mpa (
        //clock and reset
        .clk                            (plf_clk                        ),
        .rst_n                          (plf_rst_n                      ),
        //AHB
        .proc_hready_in                 (proc_hready                    ),
        .proc_hsel                      (proc_hsel_ram                  ),
        .proc_haddr                     (proc_haddr[17:0]               ),
        .proc_htrans                    (proc_htrans                    ),
        .proc_hwrite                    (proc_hwrite                    ),
        .proc_hsize                     (proc_hsize                     ),      
        .proc_hrdata                    (proc_hrdata_ram                ),
        .proc_hwdata                    (proc_hwdata                    ),
        .proc_hresp                     (proc_hresp_ram                 ),
        .proc_hready                    (proc_hready_ram                ),
        //MAC AHB bus 
        .mac_hready_in                  (mac_hmready                    ),
        .mac_hsel                       (1'b1                           ),
        .mac_haddr                      (mac_hmaddr[17:0]               ),
        .mac_htrans                     (mac_hmtrans                    ),
        .mac_hwrite                     (mac_hmwrite                    ),
        .mac_hsize                      (mac_hmsize[1:0]                ),     
        .mac_hrdata                     (mac_hmrdata                    ),
        .mac_hwdata                     (mac_hmwdata                    ),
        .mac_hresp                      (mac_hmresp                     ),
        .mac_hready                     (mac_hmready                    ),
        //LLI AHB bus interface
        .lli_haddr                      (lli_haddr[17:0]                ),
        .lli_htrans                     (lli_htrans                     ),
        .lli_hrdata                     (lli_hrdata                     ),
        .lli_hready                     (lli_hready                     ),
        //UPSTREAM bus interface        
        .dma0_addr                      (dma0_addr[17:0]                ),
        .dma0_trans                     (dma0_trans                     ),
        .dma0_write                     (1'b0                           ),
        .dma0_rdata                     (dma0_rdata                     ),
        .dma0_wdata                     (64'b0                          ),
        .dma0_we                        (8'b0                           ),
        .dma0_ready                     (dma0_ready                     ),
        //DOWN bus interface
        .dma1_addr                      (dma1_addr[17:0]                ),
        .dma1_trans                     (dma1_trans                     ),
        .dma1_write                     (1'b1                           ),
        .dma1_rdata                     (                               ),
        .dma1_we                        (dma1_we                        ),
        .dma1_wdata                     (dma1_wdata                     ),
        .dma1_ready                     (dma1_ready                     ),
        //shared ram
        .ram_cs                         (shared_ram_en                  ),
        .ram_a                          (shared_ram_addr                ),
        .ram_we                         (shared_ram_wr_en               ),
        .ram_d                          (shared_ram_wr_data             ),
        .ram_q                          (shared_ram_rd_data             )
        );


sram_sp_32768x64 u_shared_ram(
        .clka                           (plf_clk                        ),
        .ena                            (shared_ram_en                  ),
        .addra                          (shared_ram_addr                ),
        .wea                            (shared_ram_wr_en               ),
        .dina                           (shared_ram_wr_data             ),
        .douta                          (shared_ram_rd_data             )
        );

//rwWlanNxMACHW

rwWlanNxMACHW u_rwWlanNxMACHW (
        //Reset Interfaces
        .macPIClkHardRst_n              (plf_rst_n                      ),
        .macCoreClkHardRst_n            (mac_core_rst_n                 ),
        .macWTClkHardRst_n              (mac_wt_rst_n                   ),
        .mpIFClkHardRst_n               (mpif_rst_n                     ),
        //Clock Interfaces
        .macPIClk                       (mac_pi_clk                     ),
        .macPITxClk                     (mac_pi_tx_clk                  ),
        .macPIRxClk                     (mac_pi_rx_clk                  ),
        .macPISlaveClk                  (plf_clk                        ),
        .macCoreClk                     (mac_core_clk                   ),
        .macCoreTxClk                   (mac_core_tx_clk                ),
        .macCoreRxClk                   (mac_core_rx_clk                ),
        .macCryptClk                    (mac_crypt_clk                  ),
        .macLPClk                       (mac_lp_clk                     ),
        .macWTClk                       (mac_wt_clk                     ),
        .mpIFClk                        (mpif_clk                       ),
        //Clock Enable Interfaces
        .macPriClkEn                    (mac_pri_clken                  ),
        .platformWakeUp                 (platform_wake_up               ),
        .macPITxClkEn                   (mac_pi_tx_clken                ),
        .macPIRxClkEn                   (mac_pi_rx_clken                ),
        .macCoreTxClkEn                 (mac_core_tx_clken              ),
        .macCoreRxClkEn                 (mac_core_rx_clken              ),
        .macCryptClkEn                  (mac_crypt_clken                ),
        .macLPClkSwitch                 (mac_lp_clkswitch               ),
        .macWTClkEn                     (mac_wt_clken                   ),
        .mpIFClkEn                      (mpif_clken                     ),
        //Interrupts Interfaces
        .intGen_n                       (mac_int_gen_n                  ),
        .intProtTrigger_n               (mac_int_prot_trigger_n         ),
        .intTxTrigger_n                 (mac_int_tx_trigger_n           ),
        .intRxTrigger_n                 (mac_int_rx_trigger_n           ),
        .intTxRxMisc_n                  (mac_int_tx_rx_misc_n           ),
        .intTxRxTimer_n                 (mac_int_tx_rx_timer_n          ),
        .internalError                  (                               ),
        //AHB Slave interface
        .hSAddr                         (proc_haddr[15:0]               ),
        .hSTrans                        (proc_htrans                    ),
        .hSWrite                        (proc_hwrite                    ),
        .hSSize                         ({1'b0,proc_hsize}              ),
        .hSBurst                        (3'b0                           ),
        .hSProt                         (4'b0                           ),
        .hSWData                        (proc_hwdata                    ),
        .hSSel                          (proc_hsel_mac                  ),
        .hSReadyIn                      (proc_hready                    ),
        .hSRData                        (proc_hrdata_mac                ),
        .hSReadyOut                     (proc_hready_mac                ),
        .hSResp                         (proc_hresp_mac                 ),
         //AHB Master interface
        .hMBusReq                       (                               ),
        .hMLock                         (                               ),
        .hMGrant                        (1'b1                           ),
        .hMAddr                         (mac_hmaddr                     ),
        .hMTrans                        (mac_hmtrans                    ),
        .hMWrite                        (mac_hmwrite                    ),
        .hMSize                         (mac_hmsize                     ),
        .hMBurst                        (                               ),
        .hMProt                         (                               ),
        .hMWData                        (mac_hmwdata                    ),
        .hMRData                        (mac_hmrdata                    ),
        .hMReady                        (mac_hmready                    ),
        .hMResp                         (mac_hmresp                     ),
        //MAC-PHY interface
        .phyRdy                         (phyRdy                         ),
        .txEnd_p                        (txEnd_p                        ),
        .rxData                         (rxData                         ),
        .CCAPrimary20                   (CCAPrimary20                   ),
        .CCASecondary20                 (CCASecondary20                 ),
        .CCASecondary40                 (CCASecondary40                 ),
        .CCASecondary80                 (CCASecondary80                 ),    
        .rxEndForTiming_p               (rxEndForTiming_p               ),
        .rxErr_p                        (rxErr_p                        ),
        .rxEnd_p                        (rxEnd_p                        ),
        .phyErr_p                       (phyErr_p                       ),
        .rifsRxDetected                 (rifsRxDetected                 ),
        .txReq                          (txReq                          ),
        .rxReq                          (rxReq                          ),
        .txData                         (txData                         ),
        .macDataValid                   (macDataValid                   ),
        .mimoCmdValid                   (mimoCmdValid                   ),
        .keepRFOn                       (keepRFOn                       ),
        // Memories Interfaces
        .txFIFOReadEn                   (tx_fifo_rd_en                  ),
        .txFIFOReadAddr                 (tx_fifo_rd_addr                ),
        .txFIFOReadData                 (tx_fifo_rd_data                ),
        .txFIFOWriteEn                  (tx_fifo_wr_en                  ),
        .txFIFOWriteAddr                (tx_fifo_wr_addr                ),
        .txFIFOWriteData                (tx_fifo_wr_data                ),
        .rxFIFOReadEn                   (rx_fifo_rd_en                  ),
        .rxFIFOReadAddr                 (rx_fifo_rd_addr                ),
        .rxFIFOReadData                 (rx_fifo_rd_data                ),
        .rxFIFOWriteEn                  (rx_fifo_wr_en                  ),
        .rxFIFOWriteAddr                (rx_fifo_wr_addr                ),
        .rxFIFOWriteData                (rx_fifo_wr_data                ),
        .keyStorageEn                   (keystorage_en                  ),
        .keyStorageWriteEn              (keystorage_wr_en               ),
        .keyStorageAddr                 (keystorage_addr                ),
        .keyStorageReadData             (keystorage_rd_data             ),
        .keyStorageWriteData            (keystorage_wr_data             ),
        .sBoxAEn                        (sboxa_en                       ),
        .sBoxAWriteEn                   (sboxa_wr_en                    ),
        .sBoxAAddr                      (sboxa_addr                     ),
        .sBoxAReadData                  (sboxa_rd_data                  ),
        .sBoxAWriteData                 (sboxa_wr_data                  ),
        .sBoxBEn                        (sboxb_en                       ),
        .sBoxBWriteEn                   (sboxb_wr_en                    ),
        .sBoxBAddr                      (sboxb_addr                     ),
        .sBoxBReadData                  (sboxb_rd_data                  ),
        .sBoxBWriteData                 (sboxb_wr_data                  ),
        .mpIFTxFIFOReadEn               (mpif_tx_fifo_rd_en             ),
        .mpIFTxFIFOReadAddr             (mpif_tx_fifo_rd_addr           ),
        .mpIFTxFIFOReadData             (mpif_tx_fifo_rd_data           ),
        .mpIFTxFIFOWriteEn              (mpif_tx_fifo_wr_en             ),
        .mpIFTxFIFOWriteAddr            (mpif_tx_fifo_wr_addr           ),
        .mpIFTxFIFOWriteData            (mpif_tx_fifo_wr_data           ),
        .mpIFRxFIFOReadEn               (mpif_rx_fifo_rd_en             ),
        .mpIFRxFIFOReadAddr             (mpif_rx_fifo_rd_addr           ),
        .mpIFRxFIFOReadData             (mpif_rx_fifo_rd_data           ),
        .mpIFRxFIFOWriteEn              (mpif_rx_fifo_wr_en             ),
        .mpIFRxFIFOWriteAddr            (mpif_rx_fifo_wr_addr           ),
        .mpIFRxFIFOWriteData            (mpif_rx_fifo_wr_data           ),
        .encrRxFIFOReadEn               (encrypt_rx_fifo_rd_en          ),
        .encrRxFIFOReadAddr             (encrypt_rx_fifo_rd_addr        ),
        .encrRxFIFOReadData             (encrypt_rx_fifo_rd_data        ),
        .encrRxFIFOWriteEn              (encrypt_rx_fifo_wr_en          ),
        .encrRxFIFOWriteAddr            (encrypt_rx_fifo_wr_addr        ),
        .encrRxFIFOWriteData            (encrypt_rx_fifo_wr_data        ),
        .psBitmapEn                     (ps_bitmap_en                   ),
        .psBitmapWriteEn                (ps_bitmap_wr_en                ),
        .psBitmapAddr                   (ps_bitmap_addr                 ),
        .psBitmapReadData               (ps_bitmap_rd_data              ),
        .psBitmapWriteData              (ps_bitmap_wr_data              ),
        .mibTableEn                     (mib_table_en                   ),
        .mibTableWriteEn                (mib_table_wr_en                ),
        .mibTableAddr                   (mib_table_addr                 ),
        .mibTableReadData               (mib_table_rd_data              ),
        .mibTableWriteData              (mib_table_wr_data              )
        );

sram_dp_64x38 u_tx_fifo(
        .clka                           (mac_pi_free_clk                ),
        .wea                            (tx_fifo_wr_en                  ),
        .addra                          (tx_fifo_wr_addr                ),
        .dina                           (tx_fifo_wr_data                ),
        .clkb                           (mac_core_free_clk              ),
        .enb                            (tx_fifo_rd_en                  ),
        .addrb                          (tx_fifo_rd_addr                ),
        .doutb                          (tx_fifo_rd_data                )
        );


sram_dp_64x36 u_rx_fifo(
        .clka                           (mac_core_free_clk              ),
        .wea                            (rx_fifo_wr_en                  ),
        .addra                          (rx_fifo_wr_addr                ),
        .dina                           (rx_fifo_wr_data                ),
        .clkb                           (mac_pi_free_clk                ),
        .enb                            (rx_fifo_rd_en                  ),
        .addrb                          (rx_fifo_rd_addr                ),
        .doutb                          (rx_fifo_rd_data                )
        );

`ifdef RW_WAPI_EN
sram_sp_64x315 u_keystorage (
`else
sram_sp_64x187 u_keystorage (
`endif
        .clka                           (mac_core_free_clk              ),
        .ena                            (keystorage_en                  ),
        .addra                          (keystorage_addr                ),
        .wea                            (keystorage_wr_en               ),
        .dina                           (keystorage_wr_data             ),
        .douta                          (keystorage_rd_data             ) 
        );

sram_tdp_256x8 u_sbox (
        .clka                           (mac_wt_free_clk                ),  
        .ena                            (sboxa_en                       ),
        .addra                          (sboxa_addr                     ),
        .wea                            (sboxa_wr_en                    ),
        .dina                           (sboxa_wr_data                  ),
        .douta                          (sboxa_rd_data                  ), 
        .clkb                           (mac_wt_free_clk                ),  
        .enb                            (sboxb_en                       ),
        .addrb                          (sboxb_addr                     ),
        .web                            (sboxb_wr_en                    ),
        .dinb                           (sboxb_wr_data                  ),
        .doutb                          (sboxb_rd_data                  ) 
        );

sram_dp_128x8 u_mpif_tx_fifo (
        .clka                           (mac_core_free_clk              ),
        .wea                            (mpif_tx_fifo_wr_en             ),
        .addra                          (mpif_tx_fifo_wr_addr           ),
        .dina                           (mpif_tx_fifo_wr_data           ),
        .clkb                           (mpif_free_clk                  ),
        .enb                            (mpif_tx_fifo_rd_en             ),
        .addrb                          (mpif_tx_fifo_rd_addr           ),
        .doutb                          (mpif_tx_fifo_rd_data           )
        );

sram_dp_128x8 u_mpif_rx_fifo (
        .clka                           (mpif_free_clk                  ),
        .wea                            (mpif_rx_fifo_wr_en             ),
        .addra                          (mpif_rx_fifo_wr_addr           ),
        .dina                           (mpif_rx_fifo_wr_data           ),
        .clkb                           (mac_core_free_clk              ),
        .enb                            (mpif_rx_fifo_rd_en             ),
        .addrb                          (mpif_rx_fifo_rd_addr           ),
        .doutb                          (mpif_rx_fifo_rd_data           )
        );

sram_dp_128x8 u_encrypt_rx_fifo (
        .clka                           (mac_core_free_clk              ),
        .wea                            (encrypt_rx_fifo_wr_en          ),
        .addra                          (encrypt_rx_fifo_wr_addr        ),
        .dina                           (encrypt_rx_fifo_wr_data        ),
        .clkb                           (mac_core_free_clk              ),
        .enb                            (encrypt_rx_fifo_rd_en          ),
        .addrb                          (encrypt_rx_fifo_rd_addr        ),
        .doutb                          (encrypt_rx_fifo_rd_data        )
        );

sram_sp_4x88 u_ps_bitmap(
        .clka                           (mac_core_free_clk              ),                   
        .ena                            (ps_bitmap_en                   ), 
        .addra                          (ps_bitmap_addr                 ), 
        .wea                            (ps_bitmap_wr_en                ), 
        .dina                           (ps_bitmap_wr_data              ), 
        .douta                          (ps_bitmap_rd_data              ) 
        );

sram_sp_256x32 u_mib_table(
        .clka                           (mac_core_free_clk              ),  
        .ena                            (mib_table_en                   ),
        .addra                          (mib_table_addr                 ),
        .wea                            (mib_table_wr_en                ),
        .dina                           (mib_table_wr_data              ),
        .douta                          (mib_table_rd_data              ) 
        );


//ahb_mpa
//ahb_mpa #(
//        .g_addr_width                   (28                             )
//        ) u_ahb_mpa_phy  (
//        .clk                            (plf_clk                        ),
//        .rst_n                          (plf_rst_n                      ),
//        .s0_hready_in                   (proc_hready                    ),
//        .s0_hsel                        (proc_hsel_phy                  ),
//        .s0_haddr                       (proc_haddr                     ),
//        .s0_htrans                      (proc_htrans                    ),
//        .s0_hwrite                      (proc_hwrite                    ),
//        .s0_hsize                       (proc_hsize                     ),
//        .s0_hwdata                      (proc_hwdata                    ),
//        .s0_hrdata                      (proc_hrdata_phy                ),
//        .s0_hresp                       (proc_hresp_phy                 ),
//        .s0_hready                      (proc_hready_phy                ),
//        .s1_hready_in                   (dma2_hready                    ),
//        .s1_hsel                        (dma2_hsel_phy                  ),
//        .s1_haddr                       (dma2_haddr[27:0]               ),
//        .s1_htrans                      (dma2_htrans                    ),
//        .s1_hwrite                      (1'b0                           ),
//        .s1_hsize                       (2'b10                          ),
//        .s1_hwdata                      (32'b0                          ),
//        .s1_hrdata                      (dma2_hrdata_phy                ),
//        .s1_hresp                       (dma2_hresp_phy                 ),
//        .s1_hready                      (dma2_hready_phy                ),
//        // 
//        .m_hready_in                    (phy_hready_in                  ),
//        .m_hsel                         (phy_hsel                       ),
//        .m_haddr                        (phy_haddr                      ),
//        .m_htrans                       (phy_htrans                     ),
//        .m_hwrite                       (phy_hwrite                     ),
//        .m_hsize                        (phy_hsize                      ),
//        .m_hwdata                       (phy_hwdata                     ),
//        .m_hrdata                       (phy_hrdata                     ),
//        .m_hresp                        (phy_hresp                      ),
//        .m_hready                       (proc_hsel_phy                     )
//        );


Ahb2Apb u_Ahb2Apb(
           // AHB interface
        .HCLK                           (plf_clk                        ),
        .HRESETn                        (plf_rst_n                      ),
        .HADDR                          (proc_haddr                     ),
        .HTRANS                         (proc_htrans                    ),
        .HWRITE                         (proc_hwrite                    ),
        .HWDATA                         (proc_hwdata                    ),
        .HSEL                           (proc_hsel_phy                  ),
        .HREADY                         (proc_hsel_phy                  ),
        
        .HRDATA                         (proc_hrdata_phy                ),
        .HREADYOUT                      (proc_hready_phy                ),
        .HRESP                          (proc_hresp_phy                 ),
        
        // APB interface
        .PRDATA0                        (phy_prdata_modema              ),
        .PRDATA1                        (      ),
        .PRDATA2                        (phy_prdata_modemg              ),
        .PRDATA3                        (      ),
        .PRDATA4                        (      ),
        .PRDATA5                        (      ),
        .PRDATA6                        (      ),
        .PRDATA7                        (      ),
        .PRDATA8                        (phy_prdata_if                  ),
        .PRDATA9                        (phy_prdata_radio               ),
        .PRDATA10                       (phy_prdata_frontend            ),
        .PRDATA11                       (      ),
        .PRDATA12                       (      ),
        .PRDATA13                       (      ),
        .PRDATA14                       (      ),
        .PRDATA15                       (      ),
        
        .PWDATA                         (phy_pwdata                     ),
        .PENABLE                        (phy_penable                    ),
        .PSELS0                         (phy_psel_modema                ),
        .PSELS1                         (),
        .PSELS2                         (phy_psel_modemg                ),
        .PSELS3                         (),
        .PSELS4                         (),
        .PSELS5                         (),
        .PSELS6                         (),
        .PSELS7                         (),.PSELS8                         (phy_psel_macphy_if),
        .PSELS9                         (phy_psel_radio),
        .PSELS10                        (phy_psel_frontend),
        .PSELS11                        (),
        .PSELS12                        (),
        .PSELS13                        (),
        .PSELS14                        (),
        .PSELS15                        (),
        .PADDR                          (phy_paddr                      ),
        .PWRITE                         (phy_pwrite                     )
            
); 

pluse_gen  u_pluse1(
    .clk         (clk_80m), 
    .rst_n       (por_rst_n),  
    .pluse_addr  (32'h60b0053C),
    .wr          (proc_hwrite),
    .waddr       (proc_haddr), 
    .wdata       (proc_hwdata),
    
    .pluse       (CCAPrimary20)
);
    
  
phy_top u_phy_top(
        .external_resetn                (plf_rst_n                      ),
        .crstn                          (plf_rst_n                      ),
//   -- -------------------------------------------------------------------------
//   -- incoming clock
//   -- ------------------------------------------------------------------------
        .source_clk                     (clk_80m                        ),
        .mpifClk						(mpif_clk						),
        .plf_clk                        (plf_clk                        ),
//  -- -------------------------------------------------------------------------
//  -- Clocks & Reset               
//  -- -------------------------------------------------------------------------
//        .bus_clk_resetn_o               (),
//        .bus_clk_reset_o                (),
//        .cclk_resetn_o                  (),
//        .bus_clk_o                      (),

//        .cclk_o                         (),
//        .cclk_n_o                       (),

//        .dac_gclk                       (),
//        .adc_gclk                       (),
//        .enable_7mhz                    (),
//        .a7s_gclk                       (),
//        .mem_rst_n_o                    (),

////    -- Clock controls
//        .clkcntl_out_0                  (),
//        .clkcntl_updata_o               (),
//        .osc32ken_o                     (),
        //.reg_en_hisslp,


//--------------apb slaver interface---------------------

        .s_apb_paddr                   (phy_paddr[11:0]                 ),
        .s_apb_penable                 (phy_penable                     ),
        //.s_apb_pprot,  
        
        .s_apb_pwdata                  (phy_pwdata                      ),
        
        .s_apb_prdata_if               (phy_prdata_if                   ),
        .s_apb_prdata_radio            (phy_prdata_radio                ),             
        .s_apb_prdata_frontend         (phy_prdata_frontend             ),               
        .s_apb_prdata_modema           (phy_prdata_modema               ),
        .s_apb_prdata_modemg           (phy_prdata_modemg               ),
        
        .s_apb_pwrite                  (phy_pwrite                      ),
        
        .psel_modema                   (phy_psel_modema                 ),
        .psel_modemg                   (phy_psel_modemg                 ),
        .psel_radio                    (phy_psel_radio                  ),
        .psel_frontend                 (phy_psel_frontend               ),
        .psel_macphy_if                (phy_psel_macphy_if              ),
//----------------------- PHY interface ------------------------------------
        .phy_cca_ind_medium            (phy_cca_ind_medium              ),
        .phyRdy                        (phyRdy                          ),
        .keepRFOn                      (keepRFOn                        ),
        
        .CCAPrimary20                  (                                ),
//------------------ tx ----------------
        .txReq                         (txReq                           ),
        .txData                        (txData                          ),
        .macDataValid                  (macDataValid                    ),
        .txEnd_p                       (txEnd_p                         ),
        .mpIfTxFifoEmtpy               (mpIfTxFifoEmtpy                 ),
//-----------------  rx  --------------
        .rxReq                         (rxReq                           ),
        .rxData                        (rxData                          ),
        .rxEndForTiming_p              (rxEndForTiming_p                ),
        .rxEnd_p                       (rxEnd_p                         ),   
//-------------------------------------------------------------------------------
        .error_count                   (error_count                     )

);

endmodule        