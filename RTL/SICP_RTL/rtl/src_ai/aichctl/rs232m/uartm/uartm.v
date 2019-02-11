// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-10
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-10  YongjunZhang        Original
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
`include "DEFINES.v"

`define     BAUD_VAL     9'd67  // baud rate of uart baudval = (clk/16xbaudrate)-1  115200 : 53 650:9600 

module UARTM
    (   
        rst_sys_n               ,   
        clk_sys                 ,   
    
        uart_tx_wen             ,   
        uart_tx_wdata           ,   
        uart_tx_rdy             ,   
    
        uart_rx_ren             ,   
        uart_rx_rdata           ,   
        
        uart_rxd                ,   
        uart_txd                      
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
`ifdef SIM
    localparam BAUD_VALUE   = 9'd67 ;
`else 
    localparam BAUD_VALUE   = 9'd67 ;
`endif
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal  
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ; 
input   wire                    uart_rxd                            ;   
input   wire    [7:0]           uart_tx_wdata                       ;   
input   wire                    uart_tx_wen                         ;   
// declare output signal
output  wire                    uart_txd                            ;   
output  wire                    uart_tx_rdy                         ;   
  
output  wire    [7:0]           uart_rx_rdata                       ;   
output  wire                    uart_rx_ren                         ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [8:0]                   baudrate                            ;   
wire                            rx_fifo_dvld                        ;
wire    [7:0]                   uart_rx_data                        ;   
wire                            uart_rx_en                          ; 
wire                            xmit_pulse                          ;   
wire                            baud_clock                          ;
// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign baudrate         = BAUD_VALUE     ; //

    UART_CLK                    U_UART_CLK 
    (
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
    .baud_val                   ( baudrate                  ),
    .baud_clock                 ( baud_clock                ),
    .xmit_pulse                 ( xmit_pulse                )
    );

    UART_TX  U_UART_TX
    (
        // input
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),

    .tx_trig                    ( uart_tx_wen               ),
    .tx_data                    ( uart_tx_wdata             ),
    .xmit_pulse                 ( xmit_pulse                ),
        // output
    .txrdy                      ( uart_tx_rdy               ),
    .txd                        ( uart_txd                  )
    ) ;

    UART_RX                     U_UART_RX
    (
    // input
    .clk_sys                    ( clk_sys                   ),
    .baud_clock                 ( baud_clock                ),
    .rst_sys_n                  ( rst_sys_n                ),
    .rxd                        ( uart_rxd                  ),
    .odd_n_even                 ( 1'b0                      ),
    // output
    .parity_err                 (                           ),
    .rx_byte                    ( uart_rx_rdata             ),
    .rx_done                    ( uart_rx_ren               ),
    .rxd_idle                   (                           )
    );

endmodule
