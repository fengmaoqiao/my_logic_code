// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   HRM_DP
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
// PURPOSE          :   data path of Hot-Redunancy MCU
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

module  HRM_DP
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    rst_125m                    ,   
    clk_125m_0                  ,   
    clk_125m_90                 ,   
    clk_125m_180                ,   
    clk_125m_270                ,   

    // cofiguration
    wd_timer                    ,  

    // connect to EMIF module
    wr_sel                      ,   
    wr_en                       ,   
    wr_pkt_num                  ,   
    wr_data                     ,   
    rd_sel                      ,   
    rd_pkt_num                  ,   
    rd_addr                     ,   
    rd_data                     ,   

    // lvds interface
    rx_en                       ,   
    lvds_rxp_in                 ,   
    lvds_rxn_in                 ,   
    lvds_txp_out                ,   
    lvds_txn_out                ,   

    // diagnose flag
    slink_err                                
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   
input   wire                    rst_125m                            ;   
input   wire                    clk_125m_0                          ;   
input   wire                    clk_125m_90                         ;   
input   wire                    clk_125m_180                        ;   
input   wire                    clk_125m_270                        ;   

input   wire        [15:0]      wd_timer                            ;   // watchdog timer , used for detecting packet delay
input   wire                    wr_sel                              ;   
input   wire                    wr_en                               ;   
input   wire        [3:0]       wr_pkt_num                          ;   
input   wire        [17:0]      wr_data                             ;   
input   wire                    rd_sel                              ;   
input   wire        [3:0]       rd_pkt_num                          ;   
input   wire        [8:0]       rd_addr                             ;  
input   wire                    rx_en                               ;   
input   wire                    lvds_rxp_in                         ;   
input   wire                    lvds_rxn_in                         ;   

// declare output signal
output  wire                    lvds_txp_out                        ;   
output  wire                    lvds_txn_out                        ;   
output  wire        [17:0]      rd_data                             ;  

output  wire                    slink_err                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            slink_mm_rdreq                      ;   
wire                            slink_mm_dval                       ;   
wire        [17:0]              slink_mm_data                       ;   
wire                            mm_slink_dval                       ;   
wire        [17:0]              mm_slink_data                       ;   
wire                            mm_slink_rdreq                      ;   
wire                            slink_mm_empty                      ; 
wire                            mm_delay_err                        ;   

// reg signal

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

    HRM_MM                      U_HRM_MM
    (
    .clk_100m                   ( clk_125m_0                ),
    .rst_100m                   ( rst_125m                  ),
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .wr_chn_sel                 ( wr_sel                    ),
    .rd_chn_sel                 ( rd_sel                    ),
    .wr_pkt_num                 ( wr_pkt_num                ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),
    .rd_pkt_num                 ( rd_pkt_num                ),
    .rd_addr                    ( rd_addr                   ),
    .rd_data                    ( rd_data                   ),

    .slink_mm_rdreq             ( slink_mm_rdreq            ),
    .mm_slink_dval              ( mm_slink_dval             ),
    .mm_slink_data              ( mm_slink_data             ),

    .mm_slink_rdreq             ( mm_slink_rdreq            ),
    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mm_dval              ( slink_mm_dval             ),
    .slink_mm_data              ( slink_mm_data             ),

    .mm_delay_err               ( mm_delay_err              )
    );

    SLINK                       U1_SLINK
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .rst_125m                   ( rst_125m                  ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),
                                  
    .wd_timer                   ( wd_timer                  ),
    .self_cfg_err               ( 1'b0                      ),
    .rx_en                      ( rx_en                     ),
    .lvds_rxp_in                ( lvds_rxp_in               ),
    .lvds_rxn_in                ( lvds_rxn_in               ),
    .mm_slink_rdreq             ( mm_slink_rdreq            ),
    .mm_slink_data              ( mm_slink_data             ),
    .mm_slink_dval              ( mm_slink_dval             ),
                                   
    .lvds_txp_out               ( lvds_txp_out              ),
    .lvds_txn_out               ( lvds_txn_out              ),
    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mm_dval              ( slink_mm_dval             ),
    .slink_mm_data              ( slink_mm_data             ),
    .slink_mm_rdreq             ( slink_mm_rdreq            ),
                                   
    .slink_tx_eop               (                           ),
    .slink_rx_eop               (                           ),
    .slink_err                  ( slink_err                 )
    );

endmodule

