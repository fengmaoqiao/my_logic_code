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
module AT25CTL
    (        
        clk_sys                 ,   // system clock
        rst_sys_n               ,   // system reset
    
        wr_en                   ,   // read enable , active high & only one cycle
        wr_value0               ,   
        wr_value1               ,   
        wr_value2               ,   
        wr_value3               ,   
        reg_addr                ,   
        rd_en                   ,   
        rd_dval                 ,   // read data dvalid
        rd_value                ,   // read data
        pw_on_en                ,   
        // output port
        spi_busy                ,   // spi bus busy
    
        // spi_interface
        spi_cs                  ,   
        spi_clk                 ,   
        spi_sdo                 ,   
        spi_sdi                 ,   
        spi_rst                 ,   
        con_done                ,   
        wr_done                 ,   
        chip_err
    );

/**********************************************************************************\
***************************** declare parameter ************************************/
localparam   CON_CNT         =   5'd3           ; // the times of register configure
localparam   DIV_CNT         =   5'd15           ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire                    wr_en                               ;   
input   wire    [31:0]          wr_value0                           ;   
input   wire    [31:0]          wr_value1                           ;   
input   wire    [31:0]          wr_value2                           ;   
input   wire    [31:0]          wr_value3                           ;   
input   wire                    rd_en                               ;   
input   wire                    spi_sdo                             ;   
input   wire    [15:0]          reg_addr                            ;   
input   wire                    pw_on_en                            ;   
// declare output signal
output  wire                    spi_busy                            ;   
output  wire                    spi_cs                              ;   
output  wire                    spi_clk                             ;   
output  wire                    spi_sdi                             ;   
output  wire                    spi_rst                             ;   
output  wire                    rd_dval                             ;   
output  wire    [31:0]          rd_value                            ;   
output  wire                    wr_done                             ;   
output  wire                    con_done                            ;   
output  wire                    chip_err                            ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            done                                ;   
wire                            wr_trig                             ;   
wire                            rd_trig                             ;
wire    [7:0]                   rw_len                              ;   
wire    [151:0]                 wr_data                             ;   
wire    [4:0]                   wr_cnt                              ;   
wire    [15:0]                  cur_state                           ; 
wire    [31:0]                  rd_data                             ;   
wire                            wr_dly_trig                         ;   
/**********************************************************************************\
******************************** debug code ****************************************

/**********************************************************************************\
********************************* main code ****************************************/
//----------------------------------------------------------------------------------
// the module of REGCTL
//----------------------------------------------------------------------------------
    E2PREG #(
    .CON_CNT                    ( CON_CNT                   )
    )
    U_E2PREG
    (	
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
       
    .wr_en                      ( wr_en                     ),
    .reg_addr                   ( reg_addr                  ),
    .wr_value0                  ( wr_value0                 ),
    .wr_value1                  ( wr_value1                 ),
    .wr_value2                  ( wr_value2                 ),
    .wr_value3                  ( wr_value3                 ),
    .wr_cnt                     ( wr_cnt                    ),
    .cur_state                  ( cur_state                 ),
    .wr_trig                    ( wr_trig                   ),
    .rd_trig                    ( rd_trig                   ),
    .rw_len                     ( rw_len                    ),
    .wr_dly_trig                ( wr_dly_trig               ),
    .wr_data                    ( wr_data                   )
	) ;

//----------------------------------------------------------------------------------
// the module of SPI ctroller
//----------------------------------------------------------------------------------
    E2PCTL #(
    .CON_CNT                    ( CON_CNT                   )
    )
    U_E2PCTL(	
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
        
    .wr_en                      ( wr_en                     ),
    .rd_en                      ( rd_en                     ),
    .done                       ( done                      ),
    .rd_data                    ( rd_data                   ),
    .pw_on_en                   ( pw_on_en                  ),
        // output port
    .rd_dval                    ( rd_dval                   ),
    .rd_value                   ( rd_value                  ),
    .spi_busy                   ( spi_busy                  ),
    .cur_state                  ( cur_state                 ),
    .wr_cnt                     ( wr_cnt                    ),
    .wr_dly_trig                ( wr_dly_trig               ),
    .con_done                   ( con_done                  ),
    .wr_done                    ( wr_done                   ),
    .chip_err                   ( chip_err                  )
	) ;

//----------------------------------------------------------------------------------
// the module of SPIM
//----------------------------------------------------------------------------------
    E2PSPI  #(
    .TWIDTH                     ( 8'd152                    ),
    .RWIDTH                     ( 6'd32                     ),
    .DIV_CNT                    ( DIV_CNT                   )
    )
    U_E2PSPI  
    (	
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .wr_trig                    ( wr_trig                   ),
    .rw_len                     ( rw_len                    ),
    .wr_value                   ( wr_data                   ),
    .rd_trig                    ( rd_trig                   ),
    .rd_value                   ( rd_data                   ),
    .done                       ( done                      ),
    .spi_rst                    ( spi_rst                   ),
    .spi_cs                     ( spi_cs                    ),
    .spi_clk                    ( spi_clk                   ),
    .spi_sdi                    ( spi_sdi                   ),
    .spi_sdo                    ( spi_sdo                   )
	) ;

endmodule
