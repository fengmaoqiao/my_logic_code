// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-12-12
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cgnpc.com.cn
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-12  Zhang Yongjun       Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active hign
// Clock Domains    :   clk_125m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`timescale 1 ns / 1 ns
`include "DEFINES.v"
module RS232M
    (
        clk_sys                 ,   // system clock
        rst_sys_n               ,   // system reset

        uart_rxd                ,   
        uart_txd                ,   
        
        ad_rd_dval              ,   
        ad_rd_value0            ,   
        ad_rd_value1            ,   
        ad_rd_value2            ,   
        ad_rd_value3            ,   
        ad_rd_value4            ,   
        ad_rd_value5            ,   
        ad_rd_value6            ,   
        ad_rd_value7            ,   
        ad_rd_value8            ,   
        ad_rd_value9            ,   
        ad_rd_value10           ,   
        ad_rd_value11           ,   
 
        uart_tx_wenl            ,   
        uart_tx_wdatal          ,   
        uart_tx_wenh            ,   
        uart_tx_wdatah          ,   
        e2p_urd_dval            ,   
        e2p_rd_value            ,
        // output

        cal_ch_index            ,   
        rd_en                   ,   
        wr_en                   ,   
        wr_value0               ,   
        wr_value1               ,   
        wr_value2               ,   
        wr_value3               ,   
        wr_addr                 ,   
        wr_done                 ,   
        e2p_rw_sel              ,   
        e2p_busy                   
    );

/**********************************************************************************\
***************************** declare parameter ************************************

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire                    uart_rxd                            ;
input   wire                    e2p_busy                            ; 
input   wire                    wr_done                             ; 

input   wire    [11:0]          ad_rd_dval                          ;   
input   wire    [15:0]          ad_rd_value0                        ;   
input   wire    [15:0]          ad_rd_value1                        ;   
input   wire    [15:0]          ad_rd_value2                        ;   
input   wire    [15:0]          ad_rd_value3                        ;   
input   wire    [15:0]          ad_rd_value4                        ;   
input   wire    [15:0]          ad_rd_value5                        ;   
input   wire    [15:0]          ad_rd_value6                        ;   
input   wire    [15:0]          ad_rd_value7                        ;   
input   wire    [15:0]          ad_rd_value8                        ;   
input   wire    [15:0]          ad_rd_value9                        ;   
input   wire    [15:0]          ad_rd_value10                       ;   
input   wire    [15:0]          ad_rd_value11                       ;   
input   wire                    uart_tx_wenl                        ;   
input   wire    [7:0]           uart_tx_wdatal                      ;   
input   wire                    uart_tx_wenh                        ;   
input   wire    [7:0]           uart_tx_wdatah                      ;   
input   wire                    e2p_urd_dval                        ;   
input   wire    [31:0]          e2p_rd_value                        ;
// declare output signal
output  wire                    uart_txd                            ;  
output  wire                    rd_en                               ;
output  wire                    wr_en                               ;   
output  wire    [31:0]          wr_value0                           ;   
output  wire    [31:0]          wr_value1                           ;   
output  wire    [31:0]          wr_value2                           ;   
output  wire    [31:0]          wr_value3                           ;   
output  wire    [15:0]          wr_addr                             ;   
output  wire                    e2p_rw_sel                          ;   
output  wire    [11:0]          cal_ch_index                        ;
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            data_fun_sel                        ;   
wire    [15:0]                  reg_addr                            ;   
wire    [11:0]                  cur_state                           ;   
wire    [7:0]                   uart_tx_wdata                       ;   
wire                            uart_tx_wen                         ;   
wire                            uart_tx_rdy                         ;   
wire    [7:0]                   uart_rx_rdata                       ;   
wire                            uart_rx_ren                         ;   

/**********************************************************************************\
******************************** debug code ****************************************

/**********************************************************************************\
********************************* main code ****************************************/
//----------------------------------------------------------------------------------
// the module of AT24CTL 
//----------------------------------------------------------------------------------
    UART_CMD                    U_UART_CMD
    (   
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    
    .uart_tx_wen                ( uart_tx_wen               ),
    .uart_tx_wdata              ( uart_tx_wdata             ),
    .uart_tx_rdy                ( uart_tx_rdy               ),

    .ad_rd_dval                 ( ad_rd_dval                ),
    .ad_rd_value0               ( ad_rd_value0              ),
    .ad_rd_value1               ( ad_rd_value1              ),
    .ad_rd_value2               ( ad_rd_value2              ),
    .ad_rd_value3               ( ad_rd_value3              ),
    .ad_rd_value4               ( ad_rd_value4              ),
    .ad_rd_value5               ( ad_rd_value5              ),
    .ad_rd_value6               ( ad_rd_value6              ),
    .ad_rd_value7               ( ad_rd_value7              ),
    .ad_rd_value8               ( ad_rd_value8              ),
    .ad_rd_value9               ( ad_rd_value9              ),
    .ad_rd_value10              ( ad_rd_value10             ),
    .ad_rd_value11              ( ad_rd_value11             ),

    .uart_tx_wenl               ( uart_tx_wenl              ),
    .uart_tx_wdatal             ( uart_tx_wdatal            ),
    .uart_tx_wenh               ( uart_tx_wenh              ),
    .uart_tx_wdatah             ( uart_tx_wdatah            ),
    .e2p_urd_dval               ( e2p_urd_dval              ),
    .e2p_rd_value               ( e2p_rd_value              ),

    .cal_ch_index               ( cal_ch_index              ),
    .e2p_rw_sel                 ( e2p_rw_sel                ),
    .e2p_busy                   ( e2p_busy                  ),
    .rd_en                      ( rd_en                     ),
    .wr_en                      ( wr_en                     ),
    .wr_value0                  ( wr_value0                 ),
    .wr_value1                  ( wr_value1                 ),
    .wr_value2                  ( wr_value2                 ),
    .wr_value3                  ( wr_value3                 ),
    .wr_addr                    ( wr_addr                   ),
    .wr_done                    ( wr_done                   ),

    .uart_rx_ren                ( uart_rx_ren               ),
    .uart_rx_rdata              ( uart_rx_rdata             )
    );

//----------------------------------------------------------------------------------
// the module of UART_CTL 
//----------------------------------------------------------------------------------
    UARTM                       U_UARTM 
    (   
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .uart_tx_wen                ( uart_tx_wen               ),
    .uart_tx_wdata              ( uart_tx_wdata             ),
    .uart_tx_rdy                ( uart_tx_rdy               ),

    .uart_rx_ren                ( uart_rx_ren               ),
    .uart_rx_rdata              ( uart_rx_rdata             ),
    
    .uart_rxd                   ( uart_rxd                  ),
    .uart_txd                   ( uart_txd                  )
    );


endmodule
