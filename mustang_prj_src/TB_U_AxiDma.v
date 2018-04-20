`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 2018/04/09 09:41:49
// Design Name: 
// Module Name: TB_U_Axi_Dma
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module TB_U_Axi_Dma(

    );
    
    reg         init_axi_txn;
    reg         m_axi_aclk;
    reg         m_axi_aresetn;              
    //写地址通道
    wire [31:0] m_axi_awaddr;
    wire [2:0]  m_axi_awprot;
    wire        m_axi_awvalid;
    wire        m_axi_awready;
    //写数据通道
    wire [31:0] m_axi_wdata;
    wire [3:0]  m_axi_wstrb;                             
    wire        m_axi_wvalid;
    wire        m_axi_wready;        
    //写响应通道
    wire [1:0]   m_axi_bresp;
    wire         m_axi_bvalid;
    wire         m_axi_bready;
    //读地址通道
    wire [31:0]  m_axi_araddr;
    wire [2:0]   m_axi_arprot;
    wire         m_axi_arvalid;    
    wire         m_axi_arready;
    //读数据通道
    wire [31:0]  m_axi_rdata;
    wire [1:0]   m_axi_rresp;
    wire         m_axi_rvalid;
    wire         m_axi_rready; 
    //axis_fifo 数据接口
    wire [31:0] m_axis_mm2s_tdata;
    wire [3:0]  m_axis_mm2s_tkeep;
    wire        m_axis_mm2s_tlast;
    wire        m_axis_mm2s_tready;
    wire        m_axis_mm2s_tvalid;
    //内存AXI接口
    wire [31:0]       m_axi_mm2s_araddr ;
    wire [1:0]        m_axi_mm2s_arburst;
    wire [3:0]        m_axi_mm2s_arcache;
    wire [7:0]        m_axi_mm2s_arlen  ;
    wire [2:0]        m_axi_mm2s_arprot ;
    wire              m_axi_mm2s_arready;
    wire [2:0]        m_axi_mm2s_arsize ;
    wire              m_axi_mm2s_arvalid;
    wire [31:0]       m_axi_mm2s_rdata  ;
    wire              m_axi_mm2s_rlast  ;
    wire              m_axi_mm2s_rready ;
    wire [1:0]        m_axi_mm2s_rresp  ;
    wire              m_axi_mm2s_rvalid ; 
    
    reg               reg_m_axi_mm2s_arready;
    reg [31:0]        reg_m_axi_mm2s_rdata;
    reg [1:0]         reg_m_axi_mm2s_rresp;
    reg               reg_m_axi_mm2s_rlast;
    reg               reg_m_axi_mm2s_rvalid;
        
    assign m_axi_mm2s_arready   =   reg_m_axi_mm2s_arready;
    assign m_axi_mm2s_rdata     =   reg_m_axi_mm2s_rdata;
    assign m_axi_mm2s_rresp     =   reg_m_axi_mm2s_rresp;
    assign m_axi_mm2s_rlast     =   reg_m_axi_mm2s_rlast;
    assign m_axi_mm2s_rvalid    =   reg_m_axi_mm2s_rvalid;
                                        
    parameter PERIOD = 10;
    
    U_AxiDma_Ctrl_v1_0_M00_AXI u_U_AxiDma_Ctrl(
       .INIT_AXI_TXN       (init_axi_txn)      ,
       .M_AXI_ACLK         (m_axi_aclk)        ,
       .M_AXI_ARESETN      (m_axi_aresetn)     ,
       //写地址通道
       .M_AXI_AWADDR       (m_axi_awaddr)      ,//out
       .M_AXI_AWPROT       (m_axi_awprot)      ,//out
       .M_AXI_AWVALID      (m_axi_awvalid)     ,//out
       .M_AXI_AWREADY      (m_axi_awready)     ,//in
        //写数据通道
        .M_AXI_WDATA        (m_axi_wdata)       ,//out
        .M_AXI_WSTRB        (m_axi_wstrb)       ,//out
        .M_AXI_WVALID       (m_axi_wvalid)      ,//out
        .M_AXI_WREADY       (m_axi_wready)      ,//in
        //写响应通道
        .M_AXI_BRESP        (m_axi_bresp)       ,//in
        .M_AXI_BVALID       (m_axi_bvalid)      ,//in
        .M_AXI_BREADY       (m_axi_bready)      ,//out
        //读地址通道
        .M_AXI_ARADDR       (m_axi_araddr)      ,//out
        .M_AXI_ARPROT       (m_axi_arprot)      ,//out      
        .M_AXI_ARVALID      (m_axi_arvalid)     ,//out
        .M_AXI_ARREADY      (m_axi_arready)     ,//in
        //读数据通道                              
        .M_AXI_RDATA        (m_axi_rdata)       ,//in
        .M_AXI_RRESP        (m_axi_rresp)       ,//in
        .M_AXI_RVALID       (m_axi_rvalid)      ,//in
        .M_AXI_RREADY       (m_axi_rready)      //out                             
    );
    
    design_1_axi_dma_0_0 U_axi_dma_0
    (
        .s_axi_lite_aclk    (m_axi_aclk)        ,
        .m_axi_mm2s_aclk    (m_axi_aclk)        ,
        .m_axi_s2mm_aclk    (m_axi_aclk)        ,
        .axi_resetn         (m_axi_aresetn)     ,        
        //写地址通道    
        .s_axi_lite_awaddr  (m_axi_awaddr)      ,
        .s_axi_lite_awready (m_axi_awready)     ,                 //out
        .s_axi_lite_awvalid (m_axi_awvalid )    ,        //in
        //写数据通道
        .s_axi_lite_wvalid  (m_axi_wvalid)      ,                          //in
        .s_axi_lite_wdata   (m_axi_wdata)       ,
        .s_axi_lite_wready  (m_axi_wready)      ,
        //写响应通道
        .s_axi_lite_bready  (m_axi_bready)      ,
        .s_axi_lite_bresp   (m_axi_bresp)       ,
        .s_axi_lite_bvalid  (m_axi_bvalid)      ,
        //读地址通道
        .s_axi_lite_araddr  (m_axi_araddr)      ,
        .s_axi_lite_arready (m_axi_arready)     ,
        .s_axi_lite_arvalid (m_axi_arvalid)     ,
        //读数据通道
        .s_axi_lite_rdata   (m_axi_rdata)       ,
        .s_axi_lite_rresp   (m_axi_rresp)       ,
        .s_axi_lite_rvalid  (m_axi_rvalid)      ,
        .s_axi_lite_rready  (m_axi_rready)      ,
        //内存接口
        .m_axi_mm2s_araddr  (m_axi_mm2s_araddr  ),    //req out
        .m_axi_mm2s_arburst (m_axi_mm2s_arburst ),    //req out
        .m_axi_mm2s_arcache (m_axi_mm2s_arcache ),    //req out
        .m_axi_mm2s_arlen   (m_axi_mm2s_arlen   ),    //req out
        .m_axi_mm2s_arprot  (m_axi_mm2s_arprot  ),    //req out
        .m_axi_mm2s_arsize  (m_axi_mm2s_arsize  ),    //req out
        .m_axi_mm2s_arvalid (m_axi_mm2s_arvalid ),    //req out
        .m_axi_mm2s_rready  (m_axi_mm2s_rready  ),    //req out

        .m_axi_mm2s_arready (m_axi_mm2s_arready ),    //req in
        .m_axi_mm2s_rdata   (m_axi_mm2s_rdata   ),    //req in
        .m_axi_mm2s_rlast   (m_axi_mm2s_rlast   ),    //req in
        .m_axi_mm2s_rresp   (m_axi_mm2s_rresp   ),    //req in
        .m_axi_mm2s_rvalid  (m_axi_mm2s_rvalid  ),    //req in                                
        //AXIS_FIFO接口
        .m_axis_mm2s_tdata  (m_axis_mm2s_tdata  ),
        .m_axis_mm2s_tkeep  (m_axis_mm2s_tkeep  ),
        .m_axis_mm2s_tlast  (m_axis_mm2s_tlast  ),
        .m_axis_mm2s_tready (m_axis_mm2s_tready ),
        .m_axis_mm2s_tvalid (m_axis_mm2s_tvalid )                                      
    );
    
    axis_data_fifo_0 U_aixs_data_fifo(
    
        .s_axis_aresetn     (m_axi_aresetn),
        .s_axis_aclk        (m_axi_aclk),
        
        .s_axis_tvalid      (m_axis_mm2s_tvalid)        ,
        .s_axis_tready      (m_axis_mm2s_tready)        ,
        .s_axis_tdata       (m_axis_mm2s_tdata)         ,
        .s_axis_tkeep       (m_axis_mm2s_tkeep)         ,
        .s_axis_tlast       (m_axis_mm2s_tlast)   
    );
    
       
 
    always begin
       m_axi_aclk = 1'b0;
       #(PERIOD/2) m_axi_aclk = 1'b1;
       #(PERIOD/2);
    end
    
    initial begin
    m_axi_aresetn = 1'b0;
    #100
    m_axi_aresetn = 1'b1;
    end         
    
    initial begin
    init_axi_txn = 1'b0;
    #20000
    init_axi_txn = 1'b1;
    end
    
    initial begin
    #100
    reg_m_axi_mm2s_arready = 1'b1;
    reg_m_axi_mm2s_rdata      = 32'h5a5a_5a5a;
    reg_m_axi_mm2s_rresp       = 2'b00;
    reg_m_axi_mm2s_rlast      = 1'b0;
    reg_m_axi_mm2s_rvalid     = 1'b1;
    end
    
//    initial begin
//    m_axi_awready = 1'b1;
//    m_axi_wready  = 1'b1;
//    m_axi_bresp   = 1'b1;   
//    end 
    
//    always@(posedge m_axi_aclk or negedge m_axi_aresetn)
//    begin
//        if(m_axi_awvalid && m_axi_wvalid)
//        m_axi_bvalid <= 1'b1;
//        else
//        m_axi_bvalid <= 1'b0;
//    end
endmodule
