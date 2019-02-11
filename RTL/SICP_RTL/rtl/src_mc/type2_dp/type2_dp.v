// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE2_DP
// CREATE DATE      :   2017-09-11
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-11  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   data path of TYPE2
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

module  TYPE2_DP
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    rst_125m                    ,   
    clk_125m_0                  ,   
    clk_125m_90                 ,   
    clk_125m_180                ,   
    clk_125m_270                ,   

    // connect to selfm module
    rd_dmm_empty                ,
    run_cycle                   ,   
    dst_sta_num                 ,   
    // mpu box configuration 
    chn_type                    , 
    master_slave_flag           ,
    self_cfg_err                ,   

    // connect to EMIF module
    wr_sel                      ,   
    wr_port                     ,   
    wr_en                       ,   
    wr_data                     ,   
    rd_sel                      ,   
    rd_port                     ,   
    rd_addr                     ,   
    rd_data                     ,   

    // lvds interface 
    lvds_rxp_in                 ,   
    lvds_rxn_in                 ,   
    lvds_txp_out                ,   
    lvds_txn_out                ,   

    // state frame
    sta_dval                    ,   
    sta_data                    ,

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

input   wire        [15:0]      run_cycle                           ;   
input   wire        [7:0]       dst_sta_num                         ;   
input   wire        [4:0]       chn_type                            ;   
input   wire        [7:0]       master_slave_flag                   ;   
input   wire                    self_cfg_err                        ;   

input   wire                    wr_sel                              ;   
input   wire        [2:0]       wr_port                             ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ;   
input   wire                    rd_sel                              ;   
input   wire        [1:0]       rd_port                             ;   
input   wire        [8:0]       rd_addr                             ;   

input   wire                    lvds_rxp_in                         ;   
input   wire                    lvds_rxn_in                         ;   

// declare output signal
output  wire                    lvds_txp_out                        ;   
output  wire                    lvds_txn_out                        ;   
output  wire        [17:0]      rd_data                             ;   
output  wire        [3:0]       rd_dmm_empty                        ;  
output  wire                    sta_dval                            ;   
output  wire        [17:0]      sta_data                            ;   
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

    TYPE2_MM                    U_TYPE2_MM
    (
    .clk_100m                   ( clk_125m_0                ),
    .rst_100m                   ( rst_125m                  ),
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .dst_sta_num                ( dst_sta_num               ),
    .run_cycle                  ( run_cycle                 ),
    .rd_dmm_empty               ( rd_dmm_empty              ),
    .chn_type                   ( chn_type                  ),
    .master_slave_flag          ( master_slave_flag         ),

    .wr_sel                     ( wr_sel                    ),
    .wr_port                    ( wr_port                   ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),
    .rd_sel                     ( rd_sel                    ),
    .rd_port                    ( rd_port                   ),
    .rd_addr                    ( rd_addr                   ),
    .rd_data                    ( rd_data                   ),

    .slink_mm_rdreq             ( slink_mm_rdreq            ),
    .mm_slink_dval              ( mm_slink_dval             ),
    .mm_slink_data              ( mm_slink_data             ),

    .mm_slink_rdreq             ( mm_slink_rdreq            ),
    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mm_dval              ( slink_mm_dval             ),
    .slink_mm_data              ( slink_mm_data             ),

    .sta_dval                   ( sta_dval                  ),
    .sta_data                   ( sta_data                  ),

    .mm_delay_err               ( mm_delay_err              )
    );

    SLINK                       #                      
    (
    .CARD_TYPE                  ( 2'b00                     )
    )
    U1_SLINK
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .rst_125m                   ( rst_125m                  ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),
                                  
    .wd_timer                   ( run_cycle                 ),
    .self_cfg_err               ( self_cfg_err              ),
    .rx_en                      ( 1'b1                      ),
    .lvds_rxp_in                ( lvds_rxp_in               ),
    .lvds_rxn_in                ( lvds_rxn_in               ),
    .mm_slink_rdreq             ( mm_slink_rdreq            ),
    .mm_slink_data              ( mm_slink_data             ),
    .mm_slink_dval              ( mm_slink_dval             ),
                                   
    .lvds_txp_out               ( lvds_txp_out              ),
    .lvds_txn_out               ( lvds_txn_out              ),
    .slink_mm_dval              ( slink_mm_dval             ),
    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mm_data              ( slink_mm_data             ),
    .slink_mm_rdreq             ( slink_mm_rdreq            ),

    .slink_tx_eop               (                           ),
    .slink_rx_eop               (                           ),
    .slink_err                  ( slink_err                 )
    );

endmodule

