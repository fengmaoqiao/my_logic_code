// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-10
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com.cn
// AUTHOR'S TEL     :   18283432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-06  Zhang Yongjun       Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active low
// Clock Domains    :   clk_100m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`timescale 1 ns / 1 ns
`include "DEFINES.v"

module ADT7310CTL
    (	
        clk_sys                 ,   // system clock
        rst_sys_n               ,   // system reset
    
        pw_on_en                ,   
        wr_en                   ,   // read enable , active high & only one cycle
        wr_value                ,   
        rd_en                   ,   
        rd_dval                 ,   // read data dvalid
        rd_dvalue               ,   // read data
        cfg_done                ,   
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
	) ;

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CON_CNT         =   5'd5           ; // the times of register configure
parameter   DIV_CNT         =   5'd15           ;

localparam  PWD_DLY         =   16'hFFF         ;
localparam  ITV_CNT         =   8'd255          ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire                    wr_en                               ;   
input   wire    [15:0]          wr_value                            ;   
input   wire                    rd_en                               ;   
input   wire                    spi_sdo                             ;   
input   wire                    pw_on_en                            ;   
input   wire                    cfg_done                            ;   
// declare output signal
output  wire                    spi_busy                            ;   
output  wire                    spi_cs                              ;   
output  wire                    spi_clk                             ;   
output  wire                    spi_sdi                             ;   
output  wire                    spi_rst                             ;   
output  wire                    rd_dval                             ;   
output  wire    [15:0]          rd_dvalue                           ;   
output  wire                    wr_done                             ;   
output  wire                    chip_err                            ;   
output  wire                    con_done                            ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            done                                ;   
wire                            wr_trig                             ;   
wire                            rd_trig                             ;
wire    [5:0]                   rw_len                              ;   
wire    [24:0]                  wr_data                             ;  
wire    [4:0]                   wr_cnt                              ;   
wire    [11:0]                  cur_state                           ;   
wire    [15:0]                  rd_data                             ;   
// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// the module of SPI ctroller
//----------------------------------------------------------------------------------
    ADTCTL #(
    .CON_CNT                    ( CON_CNT                   )
    ) 
    U_ADTCTL 
    (	
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),

    .pw_on_en                   ( pw_on_en                  ),
    .cfg_done                   ( cfg_done                  ),
    .wr_en                      ( wr_en                     ),
    .wr_value                   ( wr_value                  ),
    .rd_en                      ( rd_en                     ),
    .done                       ( done                      ),
    .rd_data                    ( rd_data                   ),

    .rd_dval                    ( rd_dval                   ),
    .rd_dvalue                  ( rd_dvalue                 ),
    .spi_busy                   ( spi_busy                  ),
    .cur_state                  ( cur_state                 ),
    .wr_cnt                     ( wr_cnt                    ),
    .wr_done                    ( wr_done                   ),
    .con_done                   ( con_done                  ),
    .chip_err                   ( chip_err                  )
	) ;
//----------------------------------------------------------------------------------
// the module of REGCTL
//----------------------------------------------------------------------------------
    ADTREG                       U_ADTREG
    (	
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
        
    .wr_value                   ( wr_value                  ),
    .wr_cnt                     ( wr_cnt                    ),
    .cur_state                  ( cur_state                 ),
    .wr_trig                    ( wr_trig                   ),
    .rd_trig                    ( rd_trig                   ),
    .rw_len                     ( rw_len                    ),
    .wr_data                    ( wr_data                   )
	) ;

//----------------------------------------------------------------------------------
// the module of SPIM
//----------------------------------------------------------------------------------
    ADTSPI  #(
    .TWIDTH                     ( 6'd24                     ),
    .RWIDTH                     ( 6'd24                     ),
    .DIV_CNT                    ( DIV_CNT                   )
    )
    U_ADTSPI  
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
