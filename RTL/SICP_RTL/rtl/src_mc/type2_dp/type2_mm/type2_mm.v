// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE2_MM
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
// PURPOSE          :   memory management of TYPE2
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

module  TYPE2_MM
    (
    // clock & reset
    clk_100m                    ,   
    rst_100m                    , 
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    // connect to selfm module
    rd_dmm_empty                ,
    run_cycle                   ,   
    dst_sta_num                 ,   
    // mpu box configuration 
    chn_type                    , 
    master_slave_flag           ,

    // connect to EMIF module
    wr_sel                      ,   
    wr_port                     ,   
    wr_en                       ,   
    wr_data                     ,   
    rd_sel                      ,   
    rd_port                     ,   
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
    
    // state frame
    sta_dval                    ,   
    sta_data                    ,

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

input   wire        [15:0]      run_cycle                           ;
input   wire        [7:0]       dst_sta_num                         ;   
input   wire        [4:0]       chn_type                            ;   
input   wire        [7:0]       master_slave_flag                   ;   
input   wire                    wr_sel                              ;   
input   wire        [2:0]       wr_port                             ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ;   
input   wire                    rd_sel                              ;   
input   wire        [1:0]       rd_port                             ;   
input   wire        [8:0]       rd_addr                             ; 
input   wire                    slink_mm_rdreq                      ;   
input   wire                    slink_mm_empty                      ;   
input   wire                    slink_mm_dval                       ;   
input   wire        [17:0]      slink_mm_data                       ;   

// declare output signal
output  wire        [17:0]      rd_data                             ;   
output  wire                    mm_slink_dval                       ;   
output  wire        [17:0]      mm_slink_data                       ;   
output  wire                    mm_slink_rdreq                      ;  
output  wire        [3:0]       rd_dmm_empty                        ;
output  wire                    sta_dval                            ;   
output  wire        [17:0]      sta_data                            ;   
output  wire                    mm_delay_err                        ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            hot_plug_req                        ;  

// reg signal

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

    TYPE2_MMRX                  U_TYPE2_MMRX
    (
    .clk_100m                   ( clk_100m                  ),
    .rst_100m                   ( rst_100m                  ),

    .rd_dmm_empty               ( rd_dmm_empty              ),
    
    .rd_sel                     ( rd_sel                    ),
    .rd_port                    ( rd_port                   ),
    .rd_addr                    ( rd_addr                   ),
    .rd_data                    ( rd_data                   ),

    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mmrx_dval            ( slink_mm_dval             ),
    .slink_mmrx_data            ( slink_mm_data             ),
    .mmrx_slink_rdreq           ( mm_slink_rdreq            ),

    .sta_dval                   ( sta_dval                  ),
    .sta_data                   ( sta_data                  ),

    .hot_plug_req               ( hot_plug_req              ),
    .mm_delay_err               ( mm_delay_err              )
    );


    TYPE2_MMTX                  U_TYPE2_MMTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_100m                  ),
    .rst_emif                   ( rst_100m                  ),

    .run_cycle                  ( run_cycle                 ),
    .dst_sta_num                ( dst_sta_num               ),
    .chn_type                   ( chn_type                  ),
    .master_slave_flag          ( master_slave_flag         ),
    .hot_plug_req               ( hot_plug_req              ),

    .wr_sel                     ( wr_sel                    ),
    .wr_port                    ( wr_port                   ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .slink_mmtx_rdreq           ( slink_mm_rdreq            ),
    .mmtx_slink_dval            ( mm_slink_dval             ),
    .mmtx_slink_data            ( mm_slink_data             )
    );

endmodule

