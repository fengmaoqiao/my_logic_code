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
    reg         m_axi_awready;
    reg         m_axi_wready;
    reg [1:0]   m_axi_bresp;
    reg         m_axi_bvalid;
    reg         m_axi_arready;
    reg [31:0]  m_axi_rdata;
    reg [1:0]   m_axi_rresp;
    reg         m_axi_rvalid;
    
    wire        m_axi_wvalid;
    wire        m_axi_awvalid;
    
    parameter PERIOD = 10;
    
    U_AxiDma_Ctrl_v1_0_M00_AXI u_U_AxiDma_Ctrl(
        .INIT_AXI_TXN       (init_axi_txn)      ,
        .M_AXI_ACLK         (m_axi_aclk)        ,
        .M_AXI_ARESETN      (m_axi_aresetn)     ,
        .M_AXI_AWREADY      (m_axi_awready)     ,
        .M_AXI_WREADY       (m_axi_wready)      ,
        
        .M_AXI_AWVALID      (m_axi_awvalid)     ,
        .M_AXI_WVALID       (m_axi_wvalid)      ,
        
        .M_AXI_BRESP        (m_axi_bresp)       ,
        .M_AXI_BVALID       (m_axi_bvalid)      ,
        
        .M_AXI_ARREADY      (m_axi_arready)     ,
        .M_AXI_RDATA        (m_axi_rdata)       ,
        .M_AXI_RRESP        (m_axi_rresp)       ,
        .M_AXI_RVALID       (m_axi_rvalid)                  
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
    m_axi_awready = 1'b1;
    m_axi_wready  = 1'b1;
    m_axi_bresp   = 1'b1;   
    end 
    
    always@(posedge m_axi_aclk or negedge m_axi_aresetn)
    begin
        if(m_axi_awvalid && m_axi_wvalid)
        m_axi_bvalid <= 1'b1;
        else
        m_axi_bvalid <= 1'b0;
    end
endmodule
