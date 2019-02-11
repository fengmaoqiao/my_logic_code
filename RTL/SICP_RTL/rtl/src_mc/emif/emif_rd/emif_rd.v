// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   EMIF_RD
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

module  EMIF_RD
    (
    clk_emif                    ,   
    rst_emif                    ,   

    // EMIF interface
    emif_cs                     ,   
    emif_addr                   ,   
    emif_oe                     ,  
    rd_pkt_len                  ,
    emif_rd_data                ,  

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

    // rd sel & addr
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

input   wire                    emif_cs                             ;   
input   wire    [22:0]          emif_addr                           ;   
input   wire                    emif_oe                             ;   
input   wire    [10:0]          rd_pkt_len                          ;

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
output  wire    [15:0]          emif_rd_data                        ;   

output  reg                     selfm_rd_sel       /* synthesis syn_preserve = 1 */  ;   
output  reg                     mpu_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  reg                     ex1_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  reg                     ex2_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  reg                     ex3_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  reg                     ex4_sta_rd_sel     /* synthesis syn_preserve = 1 */  ;   
output  reg     [8:0]           selfm_rd_addr      /* synthesis syn_preserve = 1 */  ;   
output  reg     [8:0]           mpu_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  reg     [8:0]           ex1_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  reg     [8:0]           ex2_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  reg     [8:0]           ex3_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  reg     [8:0]           ex4_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  reg                     prm_rd_sel         /* synthesis syn_preserve = 1 */  ;   
output  reg     [3:0]           prm_rd_pkt_num     /* synthesis syn_preserve = 1 */  ;   
output  reg     [8:0]           prm_rd_addr        /* synthesis syn_preserve = 1 */  ;   
output  reg                     hrm_rd_sel         /* synthesis syn_preserve = 1 */  ;   
output  reg     [3:0]           hrm_rd_pkt_num     /* synthesis syn_preserve = 1 */  ;   
output  reg     [8:0]           hrm_rd_addr        /* synthesis syn_preserve = 1 */  ;  
output  reg                     mpu_slot2_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot3_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot4_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot5_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot6_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot7_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot8_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot9_rd_sel   /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot10_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot11_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot12_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot13_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot14_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  reg                     mpu_slot15_rd_sel  /* synthesis syn_preserve = 1 */  ; 
output  reg     [6:0]           mpu_slot2_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  reg     [6:0]           mpu_slot3_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  reg     [6:0]           mpu_slot4_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  reg     [6:0]           mpu_slot5_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot6_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot7_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot8_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot9_rd_port  /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot10_rd_port /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot11_rd_port /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot12_rd_port /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot13_rd_port /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot14_rd_port /* synthesis syn_preserve = 1 */  ; 
output  reg     [1:0]           mpu_slot15_rd_port /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot2_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot3_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot4_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot5_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot6_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot7_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot8_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot9_rd_addr  /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot10_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot11_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot12_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot13_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot14_rd_addr /* synthesis syn_preserve = 1 */  ; 
output  reg     [8:0]           mpu_slot15_rd_addr /* synthesis syn_preserve = 1 */  ; 

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [63:0]              crc64_dout                          ;   
wire        [63:0]              crc64_data                          ;   
wire                            crc64_dval                          ;   
wire                            crc64_eop                           ;  
wire        [21:0]              emif_rd_dval                        ;
wire                            cs_fall                             ;   
wire                            cs_ring                             ;  
wire                            cs_fall_tmp                         ;   

// reg signal
reg         [3:0]               rd_strobe_cnt                       ;   
reg         [1:0]               rd_dval_cnt                         ;   
reg         [15:0]              crc64_data0                         ;   
reg         [15:0]              crc64_data1                         ;   
reg         [15:0]              crc64_data2                         ;   
reg                             crc_flag                            ; 
reg         [1:0]               crc_cnt                             ;  
reg         [15:0]              crc_data                            ;   
reg                             rd_dval                             ; 
reg         [10:0]              pkt_len_cnt                         ;
reg         [15:0]              rd_back_data                        ;
reg                             emif_ba_d1                          ;   
reg                             emif_ba_d2                          ;   
reg                             emif_ba_d3                          ;   
reg                             emif_cs_d1    /* synthesis syn_preserve = 1 */  ;   
reg                             emif_cs_d2    /* synthesis syn_preserve = 1 */  ;   
reg                             emif_cs_d3    /* synthesis syn_preserve = 1 */  ;  
reg                             emif_cs_d4    /* synthesis syn_preserve = 1 */  ;  
reg                             emif_oe_d1    /* synthesis syn_preserve = 1 */  ;  
reg                             emif_oe_d2    /* synthesis syn_preserve = 1 */  ;  
reg         [22:0]              emif_addr_d1  /* synthesis syn_preserve = 1 */  ;
reg         [22:0]              emif_addr_d2  /* synthesis syn_preserve = 1 */  ;
reg                             cs_fall_d1    /* synthesis syn_preserve = 1 */  ;   
reg                             cs_fall_d2    /* synthesis syn_preserve = 1 */  ;   
reg                             crc64_eop_d1  /* synthesis syn_preserve = 1 */  ;  
reg                             mpu_cs_fall   /* synthesis syn_preserve = 1 */  ;   
reg                             selfm_eop     /* synthesis syn_preserve = 1 */  ;   
reg                             mpu_eop       /* synthesis syn_preserve = 1 */  ;   
reg         [22:0]              mpu_emif_addr /* synthesis syn_preserve = 1 */  ;
reg         [22:0]              mpu_emif_addr_d1 /* synthesis syn_preserve = 1 */  ;
reg                             rd_eop                              ;   
reg                             selfm_sel_tmp                       ;   
reg                             mpu_sta_sel_tmp                     ;   
reg                             ex1_sta_sel_tmp                     ;   
reg                             ex2_sta_sel_tmp                     ;   
reg                             ex3_sta_sel_tmp                     ;   
reg                             ex4_sta_sel_tmp                     ;   
reg                             prm_sel_tmp                         ;   
reg                             hrm_sel_tmp                         ;   
reg                             mpu_6_rd_sel_tmp                    ;   
reg                             mpu_7_rd_sel_tmp                    ;   
reg                             mpu_8_rd_sel_tmp                    ;   
reg                             mpu_9_rd_sel_tmp                    ;   
reg                             mpu_10_rd_sel_tmp                   ;   
reg                             mpu_11_rd_sel_tmp                   ;   
reg                             mpu_12_rd_sel_tmp                   ;   
reg                             mpu_13_rd_sel_tmp                   ;   
reg                             mpu_14_rd_sel_tmp                   ;   
reg                             mpu_15_rd_sel_tmp                   ;   
reg                             rd_sop                              ;   
reg         [6:0]               type1_mpu_port                      ;   
reg         [1:0]               type2_mpu_port                      ; 

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        emif_cs_d1   <=   1'b1 ;
    end
    else begin
        emif_cs_d1   <=   emif_cs ;
    end
end

always @ ( posedge clk_emif ) begin
    emif_cs_d2   <=   emif_cs_d1 ;
    emif_cs_d3   <=   emif_cs_d2 ;
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        emif_addr_d1   <=   23'h00 ;
    end
    else begin
        emif_addr_d1   <=   emif_addr ;
    end
end

always @ ( posedge clk_emif ) begin
    emif_addr_d2   <=   emif_addr_d1 ;
end

assign  cs_fall_tmp = ( emif_cs_d1 == 1'b0 && emif_cs_d2 == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  cs_fall = ( emif_cs_d2 == 1'b0 && emif_cs_d3 == 1'b1 ) ? 1'b1 : 1'b0 ;

//----------------------------------------------------------------------------------
// EMIF rd bus parse
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        emif_ba_d1   <=   1'b1 ;
        emif_ba_d2   <=   1'b1 ;
    end
    else begin
        emif_ba_d1   <=   emif_addr[0] ;
        emif_ba_d2   <=   emif_ba_d1 ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        rd_strobe_cnt   <=   4'h0 ;
    end
    else begin
        if( emif_cs == 1'b0 && emif_oe == 1'b0 && emif_addr_d2[22] == 1'b1 ) begin
            if ( emif_ba_d2 != emif_ba_d1 ) begin
                rd_strobe_cnt   <=   4'h0 ;
            end
            else begin
                rd_strobe_cnt   <=   rd_strobe_cnt + 1'b1 ;
            end
        end
        else begin
            rd_strobe_cnt   <=   4'h0 ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    if( rd_strobe_cnt == 4'd5 ) begin 
        rd_dval   <=   1'b1 ;
    end
    else begin
        rd_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_emif ) begin
    if( rd_strobe_cnt == 4'd3 && emif_addr_d2[8:0] == 9'h00 ) begin 
        rd_sop   <=   1'b1 ;
    end
    else begin
        rd_sop   <=   1'b0 ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        pkt_len_cnt   <=   11'h00 ;
    end
    else begin
        if( rd_eop == 1'b1 ) begin
            pkt_len_cnt <=   11'h00 ;
        end
        else if( rd_strobe_cnt == 4'd3 && emif_addr_d2[8:0] == 9'h00 ) begin
            pkt_len_cnt <=   11'h00 ;
        end
        else if( rd_dval == 1'b1 ) begin
            pkt_len_cnt <=   pkt_len_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    if( crc_flag == 1'b1 && crc_cnt == 2'b11 && rd_strobe_cnt == 4'd7 ) begin
        rd_eop   <=   1'b1 ;
    end
    else begin
        rd_eop   <=   1'b0 ;
    end
end

//----------------------------------------------------------------------------------
// rd_back_data generator
//----------------------------------------------------------------------------------
assign  emif_rd_dval = { ex4_sta_sel_tmp    ,
                         ex3_sta_sel_tmp    ,
                         ex2_sta_sel_tmp    ,
                         ex1_sta_sel_tmp    ,
                         mpu_sta_sel_tmp    ,
                         mpu_15_rd_sel_tmp  , 
                         mpu_14_rd_sel_tmp  , 
                         mpu_13_rd_sel_tmp  , 
                         mpu_12_rd_sel_tmp  , 
                         mpu_11_rd_sel_tmp  , 
                         mpu_10_rd_sel_tmp  , 
                         mpu_9_rd_sel_tmp   , 
                         mpu_8_rd_sel_tmp   , 
                         mpu_7_rd_sel_tmp   , 
                         mpu_6_rd_sel_tmp   , 
                         type1_rd_dval      , 
                         hrm_sel_tmp        , 
                         prm_sel_tmp        , 
                         selfm_sel_tmp      } ;  

always @ ( posedge clk_emif ) begin
    case( emif_rd_dval )
        22'b0000000000000000000001   :   rd_back_data    <=  selfm_rd_data  ; 
        22'b0000000000000000000010   :   rd_back_data    <=  prm_rd_data    ; 
        22'b0000000000000000000100   :   rd_back_data    <=  hrm_rd_data    ; 
        22'b0000000000000000001000   :   rd_back_data    <=  slot2_rd_data  ; 
        22'b0000000000000000010000   :   rd_back_data    <=  slot3_rd_data  ; 
        22'b0000000000000000100000   :   rd_back_data    <=  slot4_rd_data  ; 
        22'b0000000000000001000000   :   rd_back_data    <=  slot5_rd_data  ; 
        22'b0000000000000010000000   :   rd_back_data    <=  slot6_rd_data  ; 
        22'b0000000000000100000000   :   rd_back_data    <=  slot7_rd_data  ;  
        22'b0000000000001000000000   :   rd_back_data    <=  slot8_rd_data  ;  
        22'b0000000000010000000000   :   rd_back_data    <=  slot9_rd_data  ;  
        22'b0000000000100000000000   :   rd_back_data    <=  slot10_rd_data ;  
        22'b0000000001000000000000   :   rd_back_data    <=  slot11_rd_data ;  
        22'b0000000010000000000000   :   rd_back_data    <=  slot12_rd_data ;  
        22'b0000000100000000000000   :   rd_back_data    <=  slot13_rd_data ;  
        22'b0000001000000000000000   :   rd_back_data    <=  slot14_rd_data ;  
        22'b0000010000000000000000   :   rd_back_data    <=  slot15_rd_data ;  
        22'b0000100000000000000000   :   rd_back_data    <=  mpu_rd_data ;  
        22'b0001000000000000000000   :   rd_back_data    <=  ex1_rd_data ;  
        22'b0010000000000000000000   :   rd_back_data    <=  ex2_rd_data ;  
        22'b0100000000000000000000   :   rd_back_data    <=  ex3_rd_data ;  
        22'b1000000000000000000000   :   rd_back_data    <=  ex4_rd_data ;  
        default                      :   rd_back_data    <=  16'h00 ; 
    endcase
end

//----------------------------------------------------------------------------------
// read data CRC64 generator
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        rd_dval_cnt   <=   2'b00 ;
    end
    else begin
        if( rd_eop == 1'b1 ) begin
            rd_dval_cnt   <=   2'b00 ;
        end
        else if( rd_dval == 1'b1 ) begin
            rd_dval_cnt   <=   rd_dval_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc64_data0   <=   16'h00 ;
    end
    else begin
        if( rd_dval == 1'b1 && rd_dval_cnt == 2'b00 ) begin
            crc64_data0   <=   rd_back_data ;
        end
        else ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc64_data1   <=   16'h00 ;
    end
    else begin
        if( rd_dval == 1'b1 && rd_dval_cnt == 2'b01 ) begin
            crc64_data1   <=   rd_back_data ;
        end
        else ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc64_data2   <=   16'h00 ;
    end
    else begin
        if( rd_dval == 1'b1 && rd_dval_cnt == 2'b10 ) begin
            crc64_data2   <=   rd_back_data ;
        end
        else ;
    end
end

assign  crc64_data = { rd_back_data , crc64_data2 , crc64_data1 , crc64_data0 } ;
assign  crc64_dval = ( rd_dval == 1'b1 && rd_dval_cnt == 2'b11 && crc_flag == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  crc64_eop  = ( rd_dval == 1'b1 && pkt_len_cnt == rd_pkt_len - 4'd5 && crc_flag == 1'b0 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc64_eop_d1   <=   1'b0 ;
    end
    else begin
        crc64_eop_d1   <=   crc64_eop ;
    end
end

    CRC64D64                    U_CRC64D64 
    (
    //input port
    .clk_sys                    ( clk_emif                  ),
    .rst_sys                    ( rst_emif                  ),
    .crc_din                    ( crc64_data                ),
    .crc_cap                    ( crc64_eop                 ),
    .crc_sop                    ( rd_sop                    ),
    .crc_din_vld                ( crc64_dval                ),
    //output port
    .crc_dout                   ( crc64_dout                )
    );

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc_flag   <=   1'b0 ;
    end
    else begin
        if( rd_eop == 1'b1 ) begin
            crc_flag   <=   1'b0 ;
        end
        else if( cs_fall == 1'b1 && pkt_len_cnt == rd_pkt_len - 4 ) begin
            crc_flag   <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    if( crc_flag == 1'b1 ) begin
        if( emif_ba_d2 != emif_ba_d1 ) begin
            crc_cnt   <=   crc_cnt + 1'b1 ;
        end
        else ;
    end
    else begin
        crc_cnt   <=   2'b00 ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc_data   <=  16'h00 ;
    end
    else begin
        case ( crc_cnt ) 
            2'b00   : crc_data   <=  crc64_dout[15:0]  ;
            2'b01   : crc_data   <=  crc64_dout[31:16] ;
            2'b10   : crc_data   <=  crc64_dout[47:32] ;
            2'b11   : crc_data   <=  crc64_dout[63:48] ;
            default : crc_data   <=  16'h00 ;
        endcase
    end
end

assign  emif_rd_data = crc_flag == 1'b1 ? crc_data : rd_back_data ;

//----------------------------------------------------------------------------------
// state & prm & hrm
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif ) begin
    if ( cs_fall == 1'b1 && emif_addr_d1[8:0] == 9'h00 ) begin
        cs_fall_d1   <= 1'b1 ;
    end
    else begin
        cs_fall_d1   <= 1'b0 ;
    end
end

always @ ( posedge clk_emif ) begin
    selfm_eop   <=   crc64_eop_d1 ;
end

always @ ( posedge clk_emif ) begin
    prm_rd_pkt_num  <=  emif_addr_d1[12:9] ;
    hrm_rd_pkt_num  <=  emif_addr_d1[12:9] ;
end

always @ ( posedge clk_emif ) begin
    selfm_rd_addr   <=   emif_addr_d1[8:0] ;
    mpu_rd_addr     <=   emif_addr_d1[8:0] ;
    ex1_rd_addr     <=   emif_addr_d1[8:0] ;
    ex2_rd_addr     <=   emif_addr_d1[8:0] ;
    ex3_rd_addr     <=   emif_addr_d1[8:0] ;
    ex4_rd_addr     <=   emif_addr_d1[8:0] ;
    prm_rd_addr     <=   emif_addr_d1[8:0] ;
    hrm_rd_addr     <=   emif_addr_d1[8:0] ;
end

always @ ( posedge clk_emif ) begin
    selfm_rd_sel    <=   selfm_sel_tmp ;
    mpu_sta_rd_sel  <=   mpu_sta_sel_tmp ;
    ex1_sta_rd_sel  <=   ex1_sta_sel_tmp ;
    ex2_sta_rd_sel  <=   ex2_sta_sel_tmp ;
    ex3_sta_rd_sel  <=   ex3_sta_sel_tmp ;
    ex4_sta_rd_sel  <=   ex4_sta_sel_tmp ;
    prm_rd_sel      <=   prm_sel_tmp ;
    hrm_rd_sel      <=   hrm_sel_tmp ;
end

// selfm read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        selfm_sel_tmp   <=   1'b0 ;
    end
    else begin
        if ( selfm_eop == 1'b1 ) begin
            selfm_sel_tmp   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( emif_addr_d1[22:13] == 10'b10_00_0000_01 ) begin 
                selfm_sel_tmp  <=   1'b1 ;
            end
            else begin
                selfm_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu case status read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_sta_sel_tmp   <=   1'b0 ;
    end
    else begin
        if ( selfm_eop == 1'b1 ) begin
            mpu_sta_sel_tmp   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( emif_addr_d1[22:13] == 10'b10_00_0000_00 ) begin 
                mpu_sta_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_sta_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// ex1 case status read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex1_sta_sel_tmp   <=   1'b0 ;
    end
    else begin
        if ( selfm_eop == 1'b1 ) begin
            ex1_sta_sel_tmp   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( emif_addr_d1[22:13] == 10'b11_00_0000_00 ) begin 
                ex1_sta_sel_tmp  <=   1'b1 ;
            end
            else begin
                ex1_sta_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// ex2 case status read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex2_sta_sel_tmp   <=   1'b0 ;
    end
    else begin
        if ( selfm_eop == 1'b1 ) begin
            ex2_sta_sel_tmp   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( emif_addr_d1[22:13] == 10'b11_01_0000_00 ) begin 
                ex2_sta_sel_tmp  <=   1'b1 ;
            end
            else begin
                ex2_sta_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// ex3 case status read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex3_sta_sel_tmp   <=   1'b0 ;
    end
    else begin
        if ( selfm_eop == 1'b1 ) begin
            ex3_sta_sel_tmp   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( emif_addr_d1[22:13] == 10'b11_10_0000_00 ) begin 
                ex3_sta_sel_tmp  <=   1'b1 ;
            end
            else begin
                ex3_sta_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// ex4 case status read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex4_sta_sel_tmp   <=   1'b0 ;
    end
    else begin
        if ( selfm_eop == 1'b1 ) begin
            ex4_sta_sel_tmp   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( emif_addr_d1[22:13] == 10'b11_11_0000_00 ) begin 
                ex4_sta_sel_tmp  <=   1'b1 ;
            end
            else begin
                ex4_sta_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// prm read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        prm_sel_tmp   <=   1'b0 ;
    end
    else begin
        if ( selfm_eop == 1'b1 ) begin
            prm_sel_tmp   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( emif_addr_d2[22:13] == 10'b10_00_0000_10 ) begin 
                prm_sel_tmp  <=   1'b1 ;
            end
            else begin
                prm_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// hrm read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        hrm_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( selfm_eop == 1'b1 ) begin
            hrm_sel_tmp   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( emif_addr_d1[22:13] == 10'b10_00_0001_10 ) begin 
                hrm_sel_tmp  <=   1'b1 ;
            end
            else begin
                hrm_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

//----------------------------------------------------------------------------------
// mpu case
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif ) begin
    if ( cs_fall == 1'b1 && emif_addr_d1[8:0] == 9'h00 ) begin
        mpu_cs_fall   <= 1'b1 ;
    end
    else begin
        mpu_cs_fall   <= 1'b0 ;
    end
end

//always @ ( posedge clk_emif ) begin
//    if ( cs_fall_tmp == 1'b1 && emif_addr[8:0] == 9'h00 ) begin
//        type1_mpu_port   <= mpu_emif_addr[21:15] ;
//        type2_mpu_port   <= mpu_emif_addr[20:19] ;
//    end
//end

always @ ( posedge clk_emif ) begin
    mpu_eop   <=   crc64_eop_d1 ;
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_emif_addr   <=   23'h00 ;
    end
    else begin
        mpu_emif_addr   <=   emif_addr ;
    end
end

always @ ( posedge clk_emif ) begin
    mpu_slot2_rd_port   <=  mpu_emif_addr[21:15] ;
    mpu_slot3_rd_port   <=  mpu_emif_addr[21:15] ;
    mpu_slot4_rd_port   <=  mpu_emif_addr[21:15] ;
    mpu_slot5_rd_port   <=  mpu_emif_addr[21:15] ;
    mpu_slot6_rd_port   <=  mpu_emif_addr[20:19] ;
    mpu_slot7_rd_port   <=  mpu_emif_addr[20:19] ;
    mpu_slot8_rd_port   <=  mpu_emif_addr[20:19] ;
    mpu_slot9_rd_port   <=  mpu_emif_addr[20:19] ;
    mpu_slot10_rd_port  <=  mpu_emif_addr[20:19] ;
    mpu_slot11_rd_port  <=  mpu_emif_addr[20:19] ;
    mpu_slot12_rd_port  <=  mpu_emif_addr[20:19] ;
    mpu_slot13_rd_port  <=  mpu_emif_addr[20:19] ;
    mpu_slot14_rd_port  <=  mpu_emif_addr[20:19] ;
    mpu_slot15_rd_port  <=  mpu_emif_addr[20:19] ;
end

always @ ( posedge clk_emif ) begin
    mpu_slot2_rd_addr    <=   mpu_emif_addr[8:0] ;
    mpu_slot3_rd_addr    <=   mpu_emif_addr[8:0] ;
    mpu_slot4_rd_addr    <=   mpu_emif_addr[8:0] ;
    mpu_slot5_rd_addr    <=   mpu_emif_addr[8:0] ;
    mpu_slot6_rd_addr    <=   mpu_emif_addr[8:0] ;
    mpu_slot7_rd_addr    <=   mpu_emif_addr[8:0] ;
    mpu_slot8_rd_addr    <=   mpu_emif_addr[8:0] ;
    mpu_slot9_rd_addr    <=   mpu_emif_addr[8:0] ;
    mpu_slot10_rd_addr   <=   mpu_emif_addr[8:0] ;
    mpu_slot11_rd_addr   <=   mpu_emif_addr[8:0] ;
    mpu_slot12_rd_addr   <=   mpu_emif_addr[8:0] ;
    mpu_slot13_rd_addr   <=   mpu_emif_addr[8:0] ;
    mpu_slot14_rd_addr   <=   mpu_emif_addr[8:0] ;
    mpu_slot15_rd_addr   <=   mpu_emif_addr[8:0] ;
end

always @ ( posedge clk_emif ) begin
    mpu_slot6_rd_sel   <=  mpu_6_rd_sel_tmp   ;
    mpu_slot7_rd_sel   <=  mpu_7_rd_sel_tmp   ;
    mpu_slot8_rd_sel   <=  mpu_8_rd_sel_tmp   ;
    mpu_slot9_rd_sel   <=  mpu_9_rd_sel_tmp   ;
    mpu_slot10_rd_sel  <=  mpu_10_rd_sel_tmp  ;
    mpu_slot11_rd_sel  <=  mpu_11_rd_sel_tmp  ;
    mpu_slot12_rd_sel  <=  mpu_12_rd_sel_tmp  ;
    mpu_slot13_rd_sel  <=  mpu_13_rd_sel_tmp  ;
    mpu_slot14_rd_sel  <=  mpu_14_rd_sel_tmp  ;
    mpu_slot15_rd_sel  <=  mpu_15_rd_sel_tmp  ;
end

// mpu slot2 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_slot2_rd_sel  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_slot2_rd_sel   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22] == 2'b1 && mpu_emif_addr[14:13] == 2'b10 ) begin 
                mpu_slot2_rd_sel  <=   1'b1 ;
            end
            else begin
                mpu_slot2_rd_sel  <=   1'b0 ;
            end
        end
    end
end

// mpu slot3 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_slot3_rd_sel  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_slot3_rd_sel   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22] == 2'b1 && mpu_emif_addr[14:13] == 2'b10 ) begin 
                mpu_slot3_rd_sel  <=   1'b1 ;
            end
            else begin
                mpu_slot3_rd_sel  <=   1'b0 ;
            end
        end
    end
end

// mpu slot4 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_slot4_rd_sel  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_slot4_rd_sel   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22] == 2'b1 && mpu_emif_addr[14:13] == 2'b10 ) begin 
                mpu_slot4_rd_sel  <=   1'b1 ;
            end
            else begin
                mpu_slot4_rd_sel  <=   1'b0 ;
            end
        end
    end
end

// mpu slot5 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_slot5_rd_sel  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_slot5_rd_sel   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22] == 2'b1 && mpu_emif_addr[14:13] == 2'b10 ) begin 
                mpu_slot5_rd_sel  <=   1'b1 ;
            end
            else begin
                mpu_slot5_rd_sel  <=   1'b0 ;
            end
        end
    end
end

// mpu slot6 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_6_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_6_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b0110_10 ) begin 
                mpu_6_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_6_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu slot7 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_7_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_7_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b0111_10 ) begin 
                mpu_7_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_7_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu slot8 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_8_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_8_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b1000_10 ) begin 
                mpu_8_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_8_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu slot9 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_9_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_9_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b1001_10 ) begin 
                mpu_9_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_9_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu slot10 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_10_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_10_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b1010_10 ) begin 
                mpu_10_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_10_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu slot11 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_11_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_11_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b1011_10 ) begin 
                mpu_11_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_11_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu slot12 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_12_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_12_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b1100_10 ) begin 
                mpu_12_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_12_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu slot13 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_13_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_13_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b1101_10 ) begin 
                mpu_13_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_13_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu slot14 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_14_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_14_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b1110_10 ) begin 
                mpu_14_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_14_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

// mpu slot15 read
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        mpu_15_rd_sel_tmp  <=   1'b0 ;
    end
    else begin
        if ( mpu_eop == 1'b1 ) begin
            mpu_15_rd_sel_tmp   <=   1'b0 ;
        end
        else if( mpu_cs_fall == 1'b1 ) begin
            if( mpu_emif_addr[22:21] == 2'b10 && mpu_emif_addr[18:13] == 6'b1111_10 ) begin 
                mpu_15_rd_sel_tmp  <=   1'b1 ;
            end
            else begin
                mpu_15_rd_sel_tmp  <=   1'b0 ;
            end
        end
    end
end

endmodule

