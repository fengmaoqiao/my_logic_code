// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SLINK
// CREATE DATE      :   2017-08-22
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-22  TingtingGan     Original
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

module  SLINK
    (
    // clock & reset 
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    rst_125m                    ,   
    clk_125m_0                  ,   
    clk_125m_90                 ,   
    clk_125m_180                ,   
    clk_125m_270                ,   
    
    // receive interface
    wd_timer                    ,   
    self_cfg_err                ,   
    rx_en                       ,
    lvds_rxp_in                 ,   
    lvds_rxn_in                 ,   
    mm_slink_rdreq              ,   
    mm_slink_data               ,   
    mm_slink_dval               ,   
    
    // transmit interface
    lvds_txp_out                ,   
    lvds_txn_out                ,   
    slink_mm_rdreq              , 
    slink_mm_empty              ,
    slink_mm_dval               ,   
    slink_mm_data               ,  

    // diagnose flag
    slink_tx_eop                ,   
    slink_rx_eop                ,   
    slink_err                                
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CARD_TYPE   =   2'b00 ; // MCU : 2'b00 , COM : 2'b01 , EX : 2'b10 , IO : 2'b11     
parameter   FIFO_TYPE   =   2'b00 ; // 00: deep is 1024 ; 01: deep is 2048 ; 10 : 4096

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

input   wire    [15:0]          wd_timer                            ;   // watchdog timer , used for detecting packet delay
input   wire                    self_cfg_err                        ;   
input   wire                    rx_en                               ;
input   wire                    lvds_rxp_in                         ;   
input   wire                    lvds_rxn_in                         ;   
input   wire                    mm_slink_rdreq                      ;   
input   wire    [17:0]          mm_slink_data                       ;   
input   wire                    mm_slink_dval                       ;   

// declare output signal
output  wire                    lvds_txp_out                        ;   
output  wire                    lvds_txn_out                        ;   
output  wire                    slink_mm_rdreq                      ; 
output  wire                    slink_mm_empty                      ;   
output  wire                    slink_mm_dval                       ;   
output  wire      [17:0]        slink_mm_data                       ;  

output  wire                    slink_tx_eop                        ;   
output  wire                    slink_rx_eop                        ;   
output  wire                    slink_err                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

    SLINK_TX                    U_SLINK_TX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_125m                   ( clk_125m_0                ),
    .rst_125m                   ( rst_125m                  ),

    .mmtx_mactx_data            ( mm_slink_data             ),
    .mmtx_mactx_dval            ( mm_slink_dval             ),
    .mactx_mmtx_rdreq           ( slink_mm_rdreq            ),

    .lvds_txp_out               ( lvds_txp_out              ),
    .lvds_txn_out               ( lvds_txn_out              ),
    .slink_tx_eop               ( slink_tx_eop              )
    );
    
    SLINK_RX                    #                   
    (
    .CARD_TYPE                  ( CARD_TYPE                 ),
    .FIFO_TYPE                  ( FIFO_TYPE                 )
    )
    U_SLINK_RX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),
    .rst_125m                   ( rst_125m                  ),

    .wd_timer                   ( wd_timer                  ),
    .self_cfg_err               ( self_cfg_err              ),
    .rx_en                      ( rx_en                     ),
    .lvds_rxp_in                ( lvds_rxp_in               ),
    .lvds_rxn_in                ( lvds_rxn_in               ),
    .mm_slink_rdreq             ( mm_slink_rdreq            ),
                   
    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mm_dval              ( slink_mm_dval             ),
    .slink_mm_data              ( slink_mm_data             ),

    .slink_rx_eop               ( slink_rx_eop              ),
    .slink_err                  ( slink_err                 )
    );
    
endmodule

