// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE1_DP
// CREATE DATE      :   2017-09-07
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-07  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   data path of TYPE1
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

module  TYPE1_DP
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
    ex_box_data_ena             , // if chn_type is COM1 , this signal indicate COM1 connct to which EX box
    ex_box_cfg_ena              , // if chn_type is COM1 , this signal decide which EX box's configuration shoud send from this COM1
    rr_sel                      ,   
    self_cfg_err                ,   

    // connect to EMIF module
    wr_sel                      ,   
    wr_port                     ,   
    wr_en                       ,   
    wr_data                     ,   
    rd_sel                      ,   
    rd_port                     ,   
    rd_addr                     ,   
    rd_dval                     ,   
    rd_data                     ,   

    // extention box configuration data interface
    excmm_ssdu_empty            ,   
    excmm_ssdu_dval             ,
    excmm_ssdu_data0            ,   
    excmm_ssdu_data1            ,   
    excmm_ssdu_data2            ,   
    excmm_ssdu_data3            ,   
    ssdu_excmm_rdreq            ,

    // lvds interface 
    lvds_rxp_in                 ,   
    lvds_rxn_in                 ,   
    lvds_txp_out                ,   
    lvds_txn_out                ,   

    // state frame
    mpu_sta_dval                ,   
    mpu_sta_data                ,   
    ex1_sta_dval                ,   
    ex1_sta_data                ,   
    ex2_sta_dval                ,   
    ex2_sta_data                ,   
    ex3_sta_dval                ,   
    ex3_sta_data                ,   
    ex4_sta_dval                ,   
    ex4_sta_data                ,   

    // diagnose flag
    slink_err                                
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   MPU_SLOT = 4'd0 ;

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
input   wire        [3:0]       ex_box_data_ena                     ;   
input   wire        [3:0]       ex_box_cfg_ena                      ;   
input   wire        [3:0]       rr_sel                              ;  

input   wire                    wr_sel                              ;   
input   wire        [7:0]       wr_port                             ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ;   
input   wire                    rd_sel                              ;   
input   wire        [6:0]       rd_port                             ;   
input   wire        [8:0]       rd_addr                             ;

input   wire                    lvds_rxp_in                         ;   
input   wire                    lvds_rxn_in                         ;   
input   wire        [3:0]       excmm_ssdu_empty                    ;   
input   wire        [3:0]       excmm_ssdu_dval                     ;   
input   wire        [17:0]      excmm_ssdu_data0                    ;   
input   wire        [17:0]      excmm_ssdu_data1                    ;   
input   wire        [17:0]      excmm_ssdu_data2                    ;   
input   wire        [17:0]      excmm_ssdu_data3                    ;   

// declare output signal
output  wire        [3:0]       ssdu_excmm_rdreq                    ;
output  wire                    rd_dval                             ;   
output  wire        [17:0]      rd_data                             ;  
output  wire                    lvds_txp_out                        ;   
output  wire                    lvds_txn_out                        ;   
output  wire        [3:0]       rd_dmm_empty                        ;
output  wire                    mpu_sta_dval  /* synthesis syn_preserve = 1 */    ;   
output  wire        [17:0]      mpu_sta_data  /* synthesis syn_preserve = 1 */    ;   
output  wire                    ex1_sta_dval  /* synthesis syn_preserve = 1 */    ;   
output  wire        [17:0]      ex1_sta_data  /* synthesis syn_preserve = 1 */    ;   
output  wire                    ex2_sta_dval  /* synthesis syn_preserve = 1 */    ;   
output  wire        [17:0]      ex2_sta_data  /* synthesis syn_preserve = 1 */    ;   
output  wire                    ex3_sta_dval  /* synthesis syn_preserve = 1 */    ;   
output  wire        [17:0]      ex3_sta_data  /* synthesis syn_preserve = 1 */    ;   
output  wire                    ex4_sta_dval  /* synthesis syn_preserve = 1 */    ;   
output  wire        [17:0]      ex4_sta_data  /* synthesis syn_preserve = 1 */    ;   
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

    TYPE1_MM                    #                    
    (
    .MPU_SLOT                   ( MPU_SLOT                  )
    )
    U_TYPE1_MM
    (
    .clk_100m                   ( clk_125m_0                ),
    .rst_100m                   ( rst_125m                  ),
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .run_cycle                  ( run_cycle                 ),
    .dst_sta_num                ( dst_sta_num               ),
    .rd_dmm_empty               ( rd_dmm_empty              ),
    .chn_type                   ( chn_type                  ),
    .master_slave_flag          ( master_slave_flag         ),
    .ex_box_data_ena            ( ex_box_data_ena           ),
    .ex_box_cfg_ena             ( ex_box_cfg_ena            ),
    .rr_sel                     ( rr_sel                    ),

    .wr_sel                     ( wr_sel                    ),
    .wr_port                    ( wr_port                   ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),
    .rd_sel                     ( rd_sel                    ),
    .rd_port                    ( rd_port                   ),
    .rd_addr                    ( rd_addr                   ),
    .rd_dval                    ( rd_dval                   ),
    .rd_data                    ( rd_data                   ),

    .excmm_ssdu_empty           ( excmm_ssdu_empty          ),
    .excmm_ssdu_dval            ( excmm_ssdu_dval           ),
    .excmm_ssdu_data0           ( excmm_ssdu_data0          ),
    .excmm_ssdu_data1           ( excmm_ssdu_data1          ),
    .excmm_ssdu_data2           ( excmm_ssdu_data2          ),
    .excmm_ssdu_data3           ( excmm_ssdu_data3          ),
    .ssdu_excmm_rdreq           ( ssdu_excmm_rdreq          ),

    .slink_mm_rdreq             ( slink_mm_rdreq            ),
    .mm_slink_dval              ( mm_slink_dval             ),
    .mm_slink_data              ( mm_slink_data             ),

    .mm_slink_rdreq             ( mm_slink_rdreq            ),
    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mm_dval              ( slink_mm_dval             ),
    .slink_mm_data              ( slink_mm_data             ),

    .mpu_sta_dval               ( mpu_sta_dval              ),
    .mpu_sta_data               ( mpu_sta_data              ),
    .ex1_sta_dval               ( ex1_sta_dval              ),
    .ex1_sta_data               ( ex1_sta_data              ),
    .ex2_sta_dval               ( ex2_sta_dval              ),
    .ex2_sta_data               ( ex2_sta_data              ),
    .ex3_sta_dval               ( ex3_sta_dval              ),
    .ex3_sta_data               ( ex3_sta_data              ),
    .ex4_sta_dval               ( ex4_sta_dval              ),
    .ex4_sta_data               ( ex4_sta_data              ),

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

