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

module FPAM
    (
        rst_sys_n               ,   
        clk_sys                 ,   
        fas_adsb_sel            ,   
        fas_data_a              ,   
        fas_data_b              ,   
        fas_start_trig          ,   
  
        fm_data_a               ,   
        fm_data_b               ,   
        fm_start_trig           ,   
        fd_data_a               ,   
        fd_data_b               ,   
        fd_start_trig           ,   
                     
        f_data_int              ,   

        f_start_trig            ,             
        fas_done                ,   
        fas_result              ,   
        fm_done                 ,   
        fm_result               ,   
        fd_done                 ,   
        fd_result               ,   
        f_done                  ,   
        f_result                   
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    f_start_trig                        ;   
input   wire    [31:0]          fas_data_a                          ;   
input   wire    [31:0]          fas_data_b                          ;   
input   wire                    fas_start_trig                      ;   
input   wire                    fas_adsb_sel                        ;   
input   wire    [31:0]          fm_data_a                           ;   
input   wire    [31:0]          fm_data_b                           ;   
input   wire                    fm_start_trig                       ;   
input   wire    [31:0]          fd_data_a                           ;   
input   wire    [31:0]          fd_data_b                           ;   
input   wire                    fd_start_trig                       ;   
input   wire    [15:0]          f_data_int                          ;   
// declare output signal
output  wire                    f_done                              ;   
output  wire    [31:0]          f_result                            ;   
output  wire                    fas_done                            ;   
output  wire    [31:0]          fas_result                          ;   // 9.375  41160000 ; 11.583 4172A7F8;
output  wire                    fm_done                             ;   
output  wire    [31:0]          fm_result                           ;   // 9.28125  41148000
output  wire                    fd_done                             ;   
output  wire    [31:0]          fd_result                           ;   // 7.33333  40EAAAAB

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [3:0]                   fas_done_temp                       ;   
wire    [3:0]                   fd_done_temp                        ;   
wire    [3:0]                   fm_done_temp                        ; 
// reg signal
  
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

assign fas_done     = fas_done_temp[0]  ;
assign fm_done      = fm_done_temp[0]   ;
assign fd_done      = fd_done_temp[0]   ;

    INT_FLOATM                  U_INT_FLOATM
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .start_trig                 ( f_start_trig              ),
    .data_int                   ( f_data_int                ),

    .result_float               ( f_result                  ),
    .done                       ( f_done                    )
    );

    FLOAT_ADDSUBM                  U_FLOAT_ADDSUBM
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .add_sub_sel                ( fas_adsb_sel              ),
    .data_a                     ( fas_data_a                ),
    .data_b                     ( fas_data_b                ),
    .start_trig                 ( fas_start_trig            ),

    .done                       ( fas_done_temp             ),
    .result                     ( fas_result                )
    );

    FLOAT_MULTIM                U_FLOAT_MULTIM
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .data_a                     ( fm_data_a                 ),  
    .data_b                     ( fm_data_b                 ),
    .start_trig                 ( fm_start_trig             ),

    .done                       ( fm_done_temp              ),
    .result                     ( fm_result                 )
    );

    FLOAT_DIVM                  U_FLOAT_DIVM
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .data_a                     ( fd_data_a                 ),
    .data_b                     ( fd_data_b                 ),
    .start_trig                 ( fd_start_trig             ),

    .done                       ( fd_done_temp              ),
    .result                     ( fd_result                 )
    );


endmodule
