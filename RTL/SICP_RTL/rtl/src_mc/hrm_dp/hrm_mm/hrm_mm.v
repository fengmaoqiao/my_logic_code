// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   HRM_MM
// CREATE DATE      :   2017-09-21
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-21  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   memory management of Hot-Redunancy MCU
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

module  HRM_MM
    (
    // clock & reset
    clk_100m                    ,   
    rst_100m                    , 
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    // connect to EMIF module
    wr_chn_sel                  ,   
    rd_chn_sel                  ,
    wr_pkt_num                  ,   
    wr_en                       ,   
    wr_data                     ,    
    rd_pkt_num                  ,   
    rd_addr                     ,   
    rd_data                     ,   

    // connect to slink protocol stack
    slink_mm_rdreq              ,   
    mm_slink_dval               ,   
    mm_slink_data               ,   

    mm_slink_rdreq              ,   
    slink_mm_empty              ,
    slink_mm_dval               ,   
    slink_mm_data               ,   

    mm_delay_err                   
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_100m                            ;   
input   wire                    rst_100m                            ;   
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   

input   wire                    wr_chn_sel                          ;   
input   wire                    rd_chn_sel                          ;   
input   wire        [3:0]       wr_pkt_num                          ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ;   
input   wire        [3:0]       rd_pkt_num                          ;   
input   wire        [8:0]       rd_addr                             ;   
input   wire                    slink_mm_empty                      ;   
input   wire                    slink_mm_rdreq                      ;   
input   wire                    slink_mm_dval                       ;   
input   wire        [17:0]      slink_mm_data                       ;   

// declare output signal
output  wire        [17:0]      rd_data                             ;   
output  wire                    mm_slink_dval                       ;   
output  wire        [17:0]      mm_slink_data                       ;   
output  wire                    mm_slink_rdreq                      ;   
output  wire                    mm_delay_err                        ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

    HRM_MMRX                    U_HRM_MMRX
    (
    .clk_100m                   ( clk_100m                  ),
    .rst_100m                   ( rst_100m                  ),

    .chn_sel                    ( rd_chn_sel                ),
    .hrm_pkt_num                ( rd_pkt_num                ),
    .rd_addr                    ( rd_addr                   ),
    .rd_data                    ( rd_data                   ),

    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mmrx_dval            ( slink_mm_dval             ),
    .slink_mmrx_data            ( slink_mm_data             ),
    .mmrx_slink_rdreq           ( mm_slink_rdreq            ),

    .mm_delay_err               ( mm_delay_err              )
    );


    HRM_MMTX                    U_HRM_MMTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_100m                  ),
    .rst_emif                   ( rst_100m                  ),

    .chn_sel                    ( wr_chn_sel                ),
    .hrm_pkt_num                ( wr_pkt_num                ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .slink_mmtx_rdreq           ( slink_mm_rdreq            ),
    .mmtx_slink_dval            ( mm_slink_dval             ),
    .mmtx_slink_data            ( mm_slink_data             )
    );

endmodule

