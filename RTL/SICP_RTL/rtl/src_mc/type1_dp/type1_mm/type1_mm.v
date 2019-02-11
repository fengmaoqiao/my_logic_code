// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE1_MM
// CREATE DATE      :   2017-09-05
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-05  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   memory management of TYPE1
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

module  TYPE1_MM
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
    ex_box_data_ena             , // if chn_type is COM1 , this signal indicate COM1 connct to which EX box
    ex_box_cfg_ena              , // if chn_type is COM1 , this signal decide which EX box's configuration shoud send from this COM1
    rr_sel                      , // reduced redundancy selction of receive path , bit[n] = 1 inidicate correspinding box valid 

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

    // connect to slink protocol stack
    slink_mm_rdreq              ,   
    mm_slink_dval               ,   
    mm_slink_data               ,   

    mm_slink_rdreq              ,  
    slink_mm_empty              ,
    slink_mm_dval               ,   
    slink_mm_data               ,   
    
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

    mm_delay_err                 
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   MPU_SLOT = 4'd0 ;

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
input   wire                    slink_mm_empty                      ;   
input   wire                    slink_mm_rdreq                      ;   
input   wire                    slink_mm_dval                       ;   
input   wire        [17:0]      slink_mm_data                       ;   
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
output  wire                    mm_slink_dval                       ;   
output  wire        [17:0]      mm_slink_data                       ;   
output  wire                    mm_slink_rdreq                      ;  
output  wire        [3:0]       rd_dmm_empty                        ;   
output  wire                    mpu_sta_dval  /* synthesis syn_preserve = 1 */   ;   
output  wire        [17:0]      mpu_sta_data  /* synthesis syn_preserve = 1 */   ;   
output  wire                    ex1_sta_dval  /* synthesis syn_preserve = 1 */   ;   
output  wire        [17:0]      ex1_sta_data  /* synthesis syn_preserve = 1 */   ;   
output  wire                    ex2_sta_dval  /* synthesis syn_preserve = 1 */   ;   
output  wire        [17:0]      ex2_sta_data  /* synthesis syn_preserve = 1 */   ;   
output  wire                    ex3_sta_dval  /* synthesis syn_preserve = 1 */   ;   
output  wire        [17:0]      ex3_sta_data  /* synthesis syn_preserve = 1 */   ;   
output  wire                    ex4_sta_dval  /* synthesis syn_preserve = 1 */   ;   
output  wire        [17:0]      ex4_sta_data  /* synthesis syn_preserve = 1 */   ;   
output  wire                    mm_delay_err                        ;  

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            hot_plug_req                        ;   

// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

    TYPE1_MMRX                  #                 
    (
    .MPU_SLOT                   ( MPU_SLOT                  )
    )
    U_TYPE1_MMRX
    (
    .clk_100m                   ( clk_100m                  ),
    .rst_100m                   ( rst_100m                  ),

    .chn_type                   ( chn_type                  ),
    .rd_dmm_empty               ( rd_dmm_empty              ),
    .rr_sel                     ( rr_sel                    ),

    .rd_sel                     ( rd_sel                    ),
    .rd_port                    ( rd_port                   ),
    .rd_addr                    ( rd_addr                   ),
    .rd_dval                    ( rd_dval                   ),
    .rd_data                    ( rd_data                   ),

    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mmrx_dval            ( slink_mm_dval             ),
    .slink_mmrx_data            ( slink_mm_data             ),
    .mmrx_slink_rdreq           ( mm_slink_rdreq            ),

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
    .hot_plug_req               ( hot_plug_req              ),

    .mm_delay_err               ( mm_delay_err              )
    );


    TYPE1_MMTX                  #                 
    (
    .MPU_SLOT                   ( MPU_SLOT                  )
    )
    U_TYPE1_MMTX
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
    .ex_box_data_ena            ( ex_box_data_ena           ),
    .ex_box_cfg_ena             ( ex_box_cfg_ena            ),

    .wr_sel                     ( wr_sel                    ),
    .wr_port                    ( wr_port                   ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .excmm_ssdu_empty           ( excmm_ssdu_empty          ),
    .excmm_ssdu_dval            ( excmm_ssdu_dval           ),
    .excmm_ssdu_data0           ( excmm_ssdu_data0          ),
    .excmm_ssdu_data1           ( excmm_ssdu_data1          ),
    .excmm_ssdu_data2           ( excmm_ssdu_data2          ),
    .excmm_ssdu_data3           ( excmm_ssdu_data3          ),
    .ssdu_excmm_rdreq           ( ssdu_excmm_rdreq          ),

    .slink_mmtx_rdreq           ( slink_mm_rdreq            ),
    .mmtx_slink_dval            ( mm_slink_dval             ),
    .mmtx_slink_data            ( mm_slink_data             )
    );

endmodule

