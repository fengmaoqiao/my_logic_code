// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   EMIF
// CREATE DATE      :   2017-08-19
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-19  TingtingGan     Original
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

module  EMIF
    (
    clk_emif                    ,   
    rst_emif                    ,   

    slot_num                    ,   
    // EMIF interface
    emif_cs                     ,   
    emif_addr                   ,  
    emif_ba                     ,   
    emif_oe                     ,   
    emif_we                     ,   
    emif_wrdata                 , 
    emif_out_ctrl               , 
    emif_rd_data                ,   

    // write signals
    self_cfg_wr_sel             ,   
    self_cfg_wr_en              ,   
    self_cfg_wr_data            ,  
    self_sta_wr_sel             ,   
    self_sta_wr_en              ,   
    self_sta_wr_data            ,  
    prm_wr_sel                  ,   
    prm_pkt_num                 ,   
    prm_wr_en                   ,   
    prm_wr_data                 ,   
    hrm_wr_sel                  ,   
    hrm_pkt_num                 ,   
    hrm_wr_en                   ,   
    hrm_wr_data                 , 
    mpu_slot2_wr_sel            ,   
    mpu_slot3_wr_sel            ,   
    mpu_slot4_wr_sel            ,   
    mpu_slot5_wr_sel            ,   
    mpu_slot6_wr_sel            ,   
    mpu_slot7_wr_sel            ,   
    mpu_slot8_wr_sel            ,   
    mpu_slot9_wr_sel            ,   
    mpu_slot10_wr_sel           ,   
    mpu_slot11_wr_sel           ,   
    mpu_slot12_wr_sel           ,   
    mpu_slot13_wr_sel           ,   
    mpu_slot14_wr_sel           ,   
    mpu_slot15_wr_sel           ,   
    mpu_slot2_port              ,   
    mpu_slot3_port              ,   
    mpu_slot4_port              ,   
    mpu_slot5_port              ,   
    mpu_slot6_port              ,   
    mpu_slot7_port              ,   
    mpu_slot8_port              ,   
    mpu_slot9_port              ,   
    mpu_slot10_port             ,   
    mpu_slot11_port             ,   
    mpu_slot12_port             ,   
    mpu_slot13_port             ,   
    mpu_slot14_port             ,   
    mpu_slot15_port             ,   
    mpu_slot2_wr_en             ,   
    mpu_slot3_wr_en             ,   
    mpu_slot4_wr_en             ,   
    mpu_slot5_wr_en             ,   
    mpu_slot6_wr_en             ,   
    mpu_slot7_wr_en             ,   
    mpu_slot8_wr_en             ,   
    mpu_slot9_wr_en             ,   
    mpu_slot10_wr_en            ,   
    mpu_slot11_wr_en            ,   
    mpu_slot12_wr_en            ,   
    mpu_slot13_wr_en            ,   
    mpu_slot14_wr_en            ,   
    mpu_slot15_wr_en            ,   
    mpu_slot2_wr_data           ,   
    mpu_slot3_wr_data           ,   
    mpu_slot4_wr_data           ,   
    mpu_slot5_wr_data           ,   
    mpu_slot6_wr_data           ,   
    mpu_slot7_wr_data           ,   
    mpu_slot8_wr_data           ,   
    mpu_slot9_wr_data           ,   
    mpu_slot10_wr_data          ,   
    mpu_slot11_wr_data          ,   
    mpu_slot12_wr_data          ,   
    mpu_slot13_wr_data          ,   
    mpu_slot14_wr_data          ,   
    mpu_slot15_wr_data          ,   
    ex1_cfg_wr_sel              ,   
    ex2_cfg_wr_sel              ,   
    ex3_cfg_wr_sel              ,   
    ex4_cfg_wr_sel              ,   
    ex1_cfg_slot                ,   
    ex2_cfg_slot                ,   
    ex3_cfg_slot                ,   
    ex4_cfg_slot                ,   
    ex1_cfg_wr_en               ,   
    ex2_cfg_wr_en               ,   
    ex3_cfg_wr_en               ,   
    ex4_cfg_wr_en               ,   
    ex1_cfg_wr_data             ,   
    ex2_cfg_wr_data             ,   
    ex3_cfg_wr_data             ,   
    ex4_cfg_wr_data             ,   
    self_cfg_err                ,  
    emif_err                    ,   

    // read back signals
    selfm_rd_data               ,
    mpu_rd_data                 ,   
    ex1_rd_data                 ,   
    ex2_rd_data                 ,   
    ex3_rd_data                 ,   
    ex4_rd_data                 ,   
    prm_rd_data                 ,   
    hrm_rd_data                 , 
    type1_rd_dval               ,   
    slot2_rd_data               ,   
    slot3_rd_data               ,   
    slot4_rd_data               ,   
    slot5_rd_data               ,   
    slot6_rd_data               ,   
    slot7_rd_data               ,   
    slot8_rd_data               ,   
    slot9_rd_data               ,   
    slot10_rd_data              ,   
    slot11_rd_data              ,   
    slot12_rd_data              ,   
    slot13_rd_data              ,   
    slot14_rd_data              ,   
    slot15_rd_data              ,   

    selfm_rd_sel                ,   
    selfm_rd_addr               ,   
    mpu_sta_rd_sel              ,   
    ex1_sta_rd_sel              ,   
    ex2_sta_rd_sel              ,   
    ex3_sta_rd_sel              ,   
    ex4_sta_rd_sel              ,   
    mpu_rd_addr                 ,   
    ex1_rd_addr                 ,   
    ex2_rd_addr                 ,   
    ex3_rd_addr                 ,   
    ex4_rd_addr                 ,   
    prm_rd_sel                  ,   
    prm_rd_pkt_num              ,   
    prm_rd_addr                 ,   
    hrm_rd_sel                  ,   
    hrm_rd_pkt_num              ,   
    hrm_rd_addr                 ,   
    mpu_slot2_rd_sel            ,   
    mpu_slot3_rd_sel            ,   
    mpu_slot4_rd_sel            ,   
    mpu_slot5_rd_sel            ,   
    mpu_slot6_rd_sel            ,   
    mpu_slot7_rd_sel            ,   
    mpu_slot8_rd_sel            ,   
    mpu_slot9_rd_sel            ,   
    mpu_slot10_rd_sel           ,   
    mpu_slot11_rd_sel           ,   
    mpu_slot12_rd_sel           ,   
    mpu_slot13_rd_sel           ,   
    mpu_slot14_rd_sel           ,   
    mpu_slot15_rd_sel           ,   
    mpu_slot2_rd_port           ,   
    mpu_slot3_rd_port           ,   
    mpu_slot4_rd_port           ,   
    mpu_slot5_rd_port           ,   
    mpu_slot6_rd_port           ,   
    mpu_slot7_rd_port           ,   
    mpu_slot8_rd_port           ,   
    mpu_slot9_rd_port           ,   
    mpu_slot10_rd_port          ,   
    mpu_slot11_rd_port          ,   
    mpu_slot12_rd_port          ,   
    mpu_slot13_rd_port          ,   
    mpu_slot14_rd_port          ,   
    mpu_slot15_rd_port          ,   
    mpu_slot2_rd_addr           ,   
    mpu_slot3_rd_addr           ,   
    mpu_slot4_rd_addr           ,   
    mpu_slot5_rd_addr           ,   
    mpu_slot6_rd_addr           ,   
    mpu_slot7_rd_addr           ,   
    mpu_slot8_rd_addr           ,   
    mpu_slot9_rd_addr           ,   
    mpu_slot10_rd_addr          ,   
    mpu_slot11_rd_addr          ,   
    mpu_slot12_rd_addr          ,   
    mpu_slot13_rd_addr          ,   
    mpu_slot14_rd_addr          ,   
    mpu_slot15_rd_addr            
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_emif                            ;   
input   wire                    rst_emif                            ;   

input   wire    [3:0]           slot_num                            ;   
input   wire                    emif_cs                             ;   
input   wire    [21:0]          emif_addr                           ; 
input   wire                    emif_ba                             ;   
input   wire                    emif_oe                             ;   
input   wire                    emif_we                             ;   
input   wire    [15:0]          emif_wrdata                         ;  
input   wire                    self_cfg_err                        ;  

input   wire    [15:0]          selfm_rd_data                       ; 
input   wire    [15:0]          mpu_rd_data                         ;   
input   wire    [15:0]          ex1_rd_data                         ;   
input   wire    [15:0]          ex2_rd_data                         ;   
input   wire    [15:0]          ex3_rd_data                         ;   
input   wire    [15:0]          ex4_rd_data                         ;   
input   wire    [15:0]          prm_rd_data                         ;   
input   wire    [15:0]          hrm_rd_data                         ;  
input   wire    [3:0]           type1_rd_dval                       ;   
input   wire    [15:0]          slot2_rd_data                       ;   
input   wire    [15:0]          slot3_rd_data                       ;   
input   wire    [15:0]          slot4_rd_data                       ;   
input   wire    [15:0]          slot5_rd_data                       ;   
input   wire    [15:0]          slot6_rd_data                       ;   
input   wire    [15:0]          slot7_rd_data                       ;   
input   wire    [15:0]          slot8_rd_data                       ;   
input   wire    [15:0]          slot9_rd_data                       ;   
input   wire    [15:0]          slot10_rd_data                      ;   
input   wire    [15:0]          slot11_rd_data                      ;   
input   wire    [15:0]          slot12_rd_data                      ;   
input   wire    [15:0]          slot13_rd_data                      ;   
input   wire    [15:0]          slot14_rd_data                      ;   
input   wire    [15:0]          slot15_rd_data                      ;   

// declare output signal
output  wire                    emif_out_ctrl                       ;   
output  wire    [15:0]          emif_rd_data                        ;   

output  wire                    self_cfg_wr_sel                     ;   
output  wire                    self_cfg_wr_en                      ;   
output  wire    [17:0]          self_cfg_wr_data                    ;   
output  wire                    self_sta_wr_sel                     ;   
output  wire                    self_sta_wr_en                      ;   
output  wire    [15:0]          self_sta_wr_data                    ;   
output  wire                    prm_wr_sel                          ;   
output  wire    [3:0]           prm_pkt_num                         ;   
output  wire                    prm_wr_en                           ;   
output  wire    [17:0]          prm_wr_data                         ;   
output  wire                    hrm_wr_sel                          ;   
output  wire    [3:0]           hrm_pkt_num                         ;   
output  wire                    hrm_wr_en                           ;   
output  wire    [17:0]          hrm_wr_data                         ;   
output  wire                    mpu_slot2_wr_sel                    ;   
output  wire                    mpu_slot3_wr_sel                    ;   
output  wire                    mpu_slot4_wr_sel                    ;   
output  wire                    mpu_slot5_wr_sel                    ;   
output  wire                    mpu_slot6_wr_sel                    ;   
output  wire                    mpu_slot7_wr_sel                    ;   
output  wire                    mpu_slot8_wr_sel                    ;   
output  wire                    mpu_slot9_wr_sel                    ;   
output  wire                    mpu_slot10_wr_sel                   ;   
output  wire                    mpu_slot11_wr_sel                   ;   
output  wire                    mpu_slot12_wr_sel                   ;   
output  wire                    mpu_slot13_wr_sel                   ;   
output  wire                    mpu_slot14_wr_sel                   ;   
output  wire                    mpu_slot15_wr_sel                   ;   
output  wire    [7:0]           mpu_slot2_port     /* synthesis syn_preserve = 1 */  ;   
output  wire    [7:0]           mpu_slot3_port     /* synthesis syn_preserve = 1 */  ;   
output  wire    [7:0]           mpu_slot4_port     /* synthesis syn_preserve = 1 */  ;   
output  wire    [7:0]           mpu_slot5_port     /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot6_port     /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot7_port     /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot8_port     /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot9_port     /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot10_port    /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot11_port    /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot12_port    /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot13_port    /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot14_port    /* synthesis syn_preserve = 1 */  ;   
output  wire    [2:0]           mpu_slot15_port    /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot2_wr_en    /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot3_wr_en    /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot4_wr_en    /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot5_wr_en    /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot6_wr_en    /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot7_wr_en    /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot8_wr_en    /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot9_wr_en    /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot10_wr_en   /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot11_wr_en   /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot12_wr_en   /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot13_wr_en   /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot14_wr_en   /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_slot15_wr_en   /* synthesis syn_preserve = 1 */  ;  
output  wire    [17:0]          mpu_slot2_wr_data  /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot3_wr_data  /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot4_wr_data  /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot5_wr_data  /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot6_wr_data  /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot7_wr_data  /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot8_wr_data  /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot9_wr_data  /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot10_wr_data /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot11_wr_data /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot12_wr_data /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot13_wr_data /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot14_wr_data /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          mpu_slot15_wr_data /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex1_cfg_wr_sel     /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex2_cfg_wr_sel     /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex3_cfg_wr_sel     /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex4_cfg_wr_sel     /* synthesis syn_preserve = 1 */  ;   
output  wire    [3:0]           ex1_cfg_slot       /* synthesis syn_preserve = 1 */  ;   
output  wire    [3:0]           ex2_cfg_slot       /* synthesis syn_preserve = 1 */  ;   
output  wire    [3:0]           ex3_cfg_slot       /* synthesis syn_preserve = 1 */  ;   
output  wire    [3:0]           ex4_cfg_slot       /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex1_cfg_wr_en      /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex2_cfg_wr_en      /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex3_cfg_wr_en      /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex4_cfg_wr_en      /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          ex1_cfg_wr_data    /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          ex2_cfg_wr_data    /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          ex3_cfg_wr_data    /* synthesis syn_preserve = 1 */  ;   
output  wire    [17:0]          ex4_cfg_wr_data    /* synthesis syn_preserve = 1 */  ;   
output  wire                    emif_err           /* synthesis syn_preserve = 1 */  ;   
                                                    
output  wire                    selfm_rd_sel       /* synthesis syn_preserve = 1 */  ;   
output  wire    [8:0]           selfm_rd_addr      /* synthesis syn_preserve = 1 */  ;   
output  wire                    mpu_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex1_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex2_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex3_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  wire                    ex4_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  wire    [8:0]           mpu_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  wire    [8:0]           ex1_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  wire    [8:0]           ex2_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  wire    [8:0]           ex3_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  wire    [8:0]           ex4_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  wire                    prm_rd_sel         /* synthesis syn_preserve = 1 */  ;   
output  wire    [3:0]           prm_rd_pkt_num     /* synthesis syn_preserve = 1 */  ;   
output  wire    [8:0]           prm_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  wire                    hrm_rd_sel         /* synthesis syn_preserve = 1 */  ;   
output  wire    [3:0]           hrm_rd_pkt_num     /* synthesis syn_preserve = 1 */  ;   
output  wire    [8:0]           hrm_rd_addr        /* synthesis syn_preserve = 1 */  ;  
output  wire                    mpu_slot2_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot3_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot4_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot5_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot6_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot7_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot8_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot9_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot10_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot11_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot12_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot13_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot14_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  wire                    mpu_slot15_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  wire    [6:0]           mpu_slot2_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  wire    [6:0]           mpu_slot3_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  wire    [6:0]           mpu_slot4_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  wire    [6:0]           mpu_slot5_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot6_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot7_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot8_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot9_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot10_rd_port /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot11_rd_port /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot12_rd_port /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot13_rd_port /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot14_rd_port /* synthesis syn_preserve = 1 */  ; 
output  wire    [1:0]           mpu_slot15_rd_port /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot2_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot3_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot4_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot5_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot6_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot7_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot8_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot9_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot10_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot11_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot12_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot13_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot14_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  wire    [8:0]           mpu_slot15_rd_addr /* synthesis syn_preserve = 1 */  ; 

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [10:0]              rd_pkt_len                          ;   
wire        [22:0]              emif_combine_addr                   ;   

// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  emif_combine_addr = { emif_addr , emif_ba } ;
assign  emif_out_ctrl   =   ( emif_cs == 1'b0 && emif_addr[21] == 1'b1 ) ? 1'b1 : 1'b0 ;  
           
    EMIF_WR                     U_EMIF_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .slot_num                   ( slot_num                  ),
    .emif_cs                    ( emif_cs                   ),
    .emif_addr                  ( emif_combine_addr         ),
    .emif_we                    ( emif_we                   ),
    .emif_wrdata                ( emif_wrdata               ),
    .rd_pkt_len                 ( rd_pkt_len                ),

    .self_cfg_wr_sel            ( self_cfg_wr_sel           ),
    .self_cfg_wr_en             ( self_cfg_wr_en            ),
    .self_cfg_wr_data           ( self_cfg_wr_data          ),
    .self_sta_wr_sel            ( self_sta_wr_sel           ),
    .self_sta_wr_en             ( self_sta_wr_en            ),
    .self_sta_wr_data           ( self_sta_wr_data          ),
    .prm_wr_sel                 ( prm_wr_sel                ),
    .prm_pkt_num                ( prm_pkt_num               ),
    .prm_wr_en                  ( prm_wr_en                 ),
    .prm_wr_data                ( prm_wr_data               ),
    .hrm_wr_sel                 ( hrm_wr_sel                ),
    .hrm_pkt_num                ( hrm_pkt_num               ),
    .hrm_wr_en                  ( hrm_wr_en                 ),
    .hrm_wr_data                ( hrm_wr_data               ),
    .mpu_slot2_wr_sel           ( mpu_slot2_wr_sel          ),
    .mpu_slot3_wr_sel           ( mpu_slot3_wr_sel          ),
    .mpu_slot4_wr_sel           ( mpu_slot4_wr_sel          ),
    .mpu_slot5_wr_sel           ( mpu_slot5_wr_sel          ),
    .mpu_slot6_wr_sel           ( mpu_slot6_wr_sel          ),
    .mpu_slot7_wr_sel           ( mpu_slot7_wr_sel          ),
    .mpu_slot8_wr_sel           ( mpu_slot8_wr_sel          ),
    .mpu_slot9_wr_sel           ( mpu_slot9_wr_sel          ),
    .mpu_slot10_wr_sel          ( mpu_slot10_wr_sel         ),
    .mpu_slot11_wr_sel          ( mpu_slot11_wr_sel         ),
    .mpu_slot12_wr_sel          ( mpu_slot12_wr_sel         ),
    .mpu_slot13_wr_sel          ( mpu_slot13_wr_sel         ),
    .mpu_slot14_wr_sel          ( mpu_slot14_wr_sel         ),
    .mpu_slot15_wr_sel          ( mpu_slot15_wr_sel         ),
    .mpu_slot2_port             ( mpu_slot2_port            ),
    .mpu_slot3_port             ( mpu_slot3_port            ),
    .mpu_slot4_port             ( mpu_slot4_port            ),
    .mpu_slot5_port             ( mpu_slot5_port            ),
    .mpu_slot6_port             ( mpu_slot6_port            ),
    .mpu_slot7_port             ( mpu_slot7_port            ),
    .mpu_slot8_port             ( mpu_slot8_port            ),
    .mpu_slot9_port             ( mpu_slot9_port            ),
    .mpu_slot10_port            ( mpu_slot10_port           ),
    .mpu_slot11_port            ( mpu_slot11_port           ),
    .mpu_slot12_port            ( mpu_slot12_port           ),
    .mpu_slot13_port            ( mpu_slot13_port           ),
    .mpu_slot14_port            ( mpu_slot14_port           ),
    .mpu_slot15_port            ( mpu_slot15_port           ),
    .mpu_slot2_wr_en            ( mpu_slot2_wr_en           ),
    .mpu_slot3_wr_en            ( mpu_slot3_wr_en           ),
    .mpu_slot4_wr_en            ( mpu_slot4_wr_en           ),
    .mpu_slot5_wr_en            ( mpu_slot5_wr_en           ),
    .mpu_slot6_wr_en            ( mpu_slot6_wr_en           ),
    .mpu_slot7_wr_en            ( mpu_slot7_wr_en           ),
    .mpu_slot8_wr_en            ( mpu_slot8_wr_en           ),
    .mpu_slot9_wr_en            ( mpu_slot9_wr_en           ),
    .mpu_slot10_wr_en           ( mpu_slot10_wr_en          ),
    .mpu_slot11_wr_en           ( mpu_slot11_wr_en          ),
    .mpu_slot12_wr_en           ( mpu_slot12_wr_en          ),
    .mpu_slot13_wr_en           ( mpu_slot13_wr_en          ),
    .mpu_slot14_wr_en           ( mpu_slot14_wr_en          ),
    .mpu_slot15_wr_en           ( mpu_slot15_wr_en          ),
    .mpu_slot2_wr_data          ( mpu_slot2_wr_data         ),
    .mpu_slot3_wr_data          ( mpu_slot3_wr_data         ),
    .mpu_slot4_wr_data          ( mpu_slot4_wr_data         ),
    .mpu_slot5_wr_data          ( mpu_slot5_wr_data         ),
    .mpu_slot6_wr_data          ( mpu_slot6_wr_data         ),
    .mpu_slot7_wr_data          ( mpu_slot7_wr_data         ),
    .mpu_slot8_wr_data          ( mpu_slot8_wr_data         ),
    .mpu_slot9_wr_data          ( mpu_slot9_wr_data         ),
    .mpu_slot10_wr_data         ( mpu_slot10_wr_data        ),
    .mpu_slot11_wr_data         ( mpu_slot11_wr_data        ),
    .mpu_slot12_wr_data         ( mpu_slot12_wr_data        ),
    .mpu_slot13_wr_data         ( mpu_slot13_wr_data        ),
    .mpu_slot14_wr_data         ( mpu_slot14_wr_data        ),
    .mpu_slot15_wr_data         ( mpu_slot15_wr_data        ),
    .ex1_cfg_wr_sel             ( ex1_cfg_wr_sel            ),
    .ex2_cfg_wr_sel             ( ex2_cfg_wr_sel            ),
    .ex3_cfg_wr_sel             ( ex3_cfg_wr_sel            ),
    .ex4_cfg_wr_sel             ( ex4_cfg_wr_sel            ),
    .ex1_cfg_slot               ( ex1_cfg_slot              ),
    .ex2_cfg_slot               ( ex2_cfg_slot              ),
    .ex3_cfg_slot               ( ex3_cfg_slot              ),
    .ex4_cfg_slot               ( ex4_cfg_slot              ),
    .ex1_cfg_wr_en              ( ex1_cfg_wr_en             ),
    .ex2_cfg_wr_en              ( ex2_cfg_wr_en             ),
    .ex3_cfg_wr_en              ( ex3_cfg_wr_en             ),
    .ex4_cfg_wr_en              ( ex4_cfg_wr_en             ),
    .ex1_cfg_wr_data            ( ex1_cfg_wr_data           ),
    .ex2_cfg_wr_data            ( ex2_cfg_wr_data           ),
    .ex3_cfg_wr_data            ( ex3_cfg_wr_data           ),
    .ex4_cfg_wr_data            ( ex4_cfg_wr_data           ),

    .self_cfg_err               ( self_cfg_err              ),
    .emif_err                   ( emif_err                  )
    );

    EMIF_RD                     U_EMIF_RD
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .emif_cs                    ( emif_cs                   ),
    .emif_addr                  ( emif_combine_addr         ),
    .emif_oe                    ( emif_oe                   ),
    .rd_pkt_len                 ( rd_pkt_len                ),
    .emif_rd_data               ( emif_rd_data              ),

    .selfm_rd_data              ( selfm_rd_data             ),
    .mpu_rd_data                ( mpu_rd_data               ),
    .ex1_rd_data                ( ex1_rd_data               ),
    .ex2_rd_data                ( ex2_rd_data               ),
    .ex3_rd_data                ( ex3_rd_data               ),
    .ex4_rd_data                ( ex4_rd_data               ),
    .prm_rd_data                ( prm_rd_data               ),
    .hrm_rd_data                ( hrm_rd_data               ),
    .type1_rd_dval              ( type1_rd_dval             ),
    .slot2_rd_data              ( slot2_rd_data             ),
    .slot3_rd_data              ( slot3_rd_data             ),
    .slot4_rd_data              ( slot4_rd_data             ),
    .slot5_rd_data              ( slot5_rd_data             ),
    .slot6_rd_data              ( slot6_rd_data             ),
    .slot7_rd_data              ( slot7_rd_data             ),
    .slot8_rd_data              ( slot8_rd_data             ),
    .slot9_rd_data              ( slot9_rd_data             ),
    .slot10_rd_data             ( slot10_rd_data            ),
    .slot11_rd_data             ( slot11_rd_data            ),
    .slot12_rd_data             ( slot12_rd_data            ),
    .slot13_rd_data             ( slot13_rd_data            ),
    .slot14_rd_data             ( slot14_rd_data            ),
    .slot15_rd_data             ( slot15_rd_data            ),

    .selfm_rd_sel               ( selfm_rd_sel              ),
    .selfm_rd_addr              ( selfm_rd_addr             ),
    .mpu_sta_rd_sel             ( mpu_sta_rd_sel            ),
    .ex1_sta_rd_sel             ( ex1_sta_rd_sel            ),
    .ex2_sta_rd_sel             ( ex2_sta_rd_sel            ),
    .ex3_sta_rd_sel             ( ex3_sta_rd_sel            ),
    .ex4_sta_rd_sel             ( ex4_sta_rd_sel            ),
    .mpu_rd_addr                ( mpu_rd_addr               ),
    .ex1_rd_addr                ( ex1_rd_addr               ),
    .ex2_rd_addr                ( ex2_rd_addr               ),
    .ex3_rd_addr                ( ex3_rd_addr               ),
    .ex4_rd_addr                ( ex4_rd_addr               ),
    .prm_rd_sel                 ( prm_rd_sel                ),
    .prm_rd_pkt_num             ( prm_rd_pkt_num            ),
    .prm_rd_addr                ( prm_rd_addr               ),
    .hrm_rd_sel                 ( hrm_rd_sel                ),
    .hrm_rd_pkt_num             ( hrm_rd_pkt_num            ),
    .hrm_rd_addr                ( hrm_rd_addr               ),
    .mpu_slot2_rd_sel           ( mpu_slot2_rd_sel          ),
    .mpu_slot3_rd_sel           ( mpu_slot3_rd_sel          ),
    .mpu_slot4_rd_sel           ( mpu_slot4_rd_sel          ),
    .mpu_slot5_rd_sel           ( mpu_slot5_rd_sel          ),
    .mpu_slot6_rd_sel           ( mpu_slot6_rd_sel          ),
    .mpu_slot7_rd_sel           ( mpu_slot7_rd_sel          ),
    .mpu_slot8_rd_sel           ( mpu_slot8_rd_sel          ),
    .mpu_slot9_rd_sel           ( mpu_slot9_rd_sel          ),
    .mpu_slot10_rd_sel          ( mpu_slot10_rd_sel         ),
    .mpu_slot11_rd_sel          ( mpu_slot11_rd_sel         ),
    .mpu_slot12_rd_sel          ( mpu_slot12_rd_sel         ),
    .mpu_slot13_rd_sel          ( mpu_slot13_rd_sel         ),
    .mpu_slot14_rd_sel          ( mpu_slot14_rd_sel         ),
    .mpu_slot15_rd_sel          ( mpu_slot15_rd_sel         ),
    .mpu_slot2_rd_port          ( mpu_slot2_rd_port         ),
    .mpu_slot3_rd_port          ( mpu_slot3_rd_port         ),
    .mpu_slot4_rd_port          ( mpu_slot4_rd_port         ),
    .mpu_slot5_rd_port          ( mpu_slot5_rd_port         ),
    .mpu_slot6_rd_port          ( mpu_slot6_rd_port         ),
    .mpu_slot7_rd_port          ( mpu_slot7_rd_port         ),
    .mpu_slot8_rd_port          ( mpu_slot8_rd_port         ),
    .mpu_slot9_rd_port          ( mpu_slot9_rd_port         ),
    .mpu_slot10_rd_port         ( mpu_slot10_rd_port        ),
    .mpu_slot11_rd_port         ( mpu_slot11_rd_port        ),
    .mpu_slot12_rd_port         ( mpu_slot12_rd_port        ),
    .mpu_slot13_rd_port         ( mpu_slot13_rd_port        ),
    .mpu_slot14_rd_port         ( mpu_slot14_rd_port        ),
    .mpu_slot15_rd_port         ( mpu_slot15_rd_port        ),
    .mpu_slot2_rd_addr          ( mpu_slot2_rd_addr         ),
    .mpu_slot3_rd_addr          ( mpu_slot3_rd_addr         ),
    .mpu_slot4_rd_addr          ( mpu_slot4_rd_addr         ),
    .mpu_slot5_rd_addr          ( mpu_slot5_rd_addr         ),
    .mpu_slot6_rd_addr          ( mpu_slot6_rd_addr         ),
    .mpu_slot7_rd_addr          ( mpu_slot7_rd_addr         ),
    .mpu_slot8_rd_addr          ( mpu_slot8_rd_addr         ),
    .mpu_slot9_rd_addr          ( mpu_slot9_rd_addr         ),
    .mpu_slot10_rd_addr         ( mpu_slot10_rd_addr        ),
    .mpu_slot11_rd_addr         ( mpu_slot11_rd_addr        ),
    .mpu_slot12_rd_addr         ( mpu_slot12_rd_addr        ),
    .mpu_slot13_rd_addr         ( mpu_slot13_rd_addr        ),
    .mpu_slot14_rd_addr         ( mpu_slot14_rd_addr        ),
    .mpu_slot15_rd_addr         ( mpu_slot15_rd_addr        )
    );


endmodule

