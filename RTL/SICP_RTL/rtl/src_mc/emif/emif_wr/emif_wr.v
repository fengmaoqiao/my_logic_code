// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   EMIF_WR
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

module  EMIF_WR
    (
    clk_emif                    ,   
    rst_emif                    ,   

    slot_num                    ,   
    // EMIF interface
    emif_cs                     ,   
    emif_addr                   ,   
    emif_we                     ,   
    emif_wrdata                 ,  
    rd_pkt_len                  ,

    // slef config
    self_cfg_wr_sel             ,   
    self_cfg_wr_en              ,   
    self_cfg_wr_data            ,  

    // arm status
    self_sta_wr_sel             ,   
    self_sta_wr_en              ,   
    self_sta_wr_data            , 

    // write to prm 
    prm_wr_sel                  ,   
    prm_pkt_num                 ,   
    prm_wr_en                   ,   
    prm_wr_data                 ,   

    // write to hrm
    hrm_wr_sel                  ,   
    hrm_pkt_num                 ,   
    hrm_wr_en                   ,   
    hrm_wr_data                 , 

    // write to mpu case
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

    // write to ex case
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
    arm_cycle              
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CNT_1MS =   32'd125000 ; // 125000 * 8 = 1ms
parameter   CRC_ERR_THRESHOLD   =   8'd20 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_emif                            ;   
input   wire                    rst_emif                            ;   

input   wire    [3:0]           slot_num                            ;   
input   wire                    emif_cs                             ;   
input   wire    [22:0]          emif_addr                           ;   
input   wire                    emif_we                             ;   
input   wire    [15:0]          emif_wrdata                         ;   
input   wire                    self_cfg_err                        ; 

// declare output signal
output  reg     [10:0]          rd_pkt_len                          ;   
output  reg                     emif_err                            ;  

output  reg                     self_cfg_wr_sel     /* synthesis syn_preserve = 1 */ ;   
output  reg                     self_cfg_wr_en      /* synthesis syn_preserve = 1 */ ;   
output  reg     [17:0]          self_cfg_wr_data    /* synthesis syn_preserve = 1 */ ;   
output  reg                     self_sta_wr_sel     /* synthesis syn_preserve = 1 */ ;   
output  reg                     self_sta_wr_en      /* synthesis syn_preserve = 1 */ ;   
output  reg     [15:0]          self_sta_wr_data    /* synthesis syn_preserve = 1 */ ;   
output  reg                     prm_wr_sel          /* synthesis syn_preserve = 1 */ ;   
output  reg     [3:0]           prm_pkt_num         /* synthesis syn_preserve = 1 */ ;   
output  reg                     prm_wr_en           /* synthesis syn_preserve = 1 */ ;   
output  reg     [17:0]          prm_wr_data         /* synthesis syn_preserve = 1 */ ;   
output  reg                     hrm_wr_sel          /* synthesis syn_preserve = 1 */ ;   
output  reg     [3:0]           hrm_pkt_num         /* synthesis syn_preserve = 1 */ ;   
output  reg                     hrm_wr_en           /* synthesis syn_preserve = 1 */ ;   
output  reg     [17:0]          hrm_wr_data         /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot2_wr_sel    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot3_wr_sel    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot4_wr_sel    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot5_wr_sel    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot6_wr_sel    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot7_wr_sel    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot8_wr_sel    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot9_wr_sel    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot10_wr_sel   /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot11_wr_sel   /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot12_wr_sel   /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot13_wr_sel   /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot14_wr_sel   /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot15_wr_sel   /* synthesis syn_preserve = 1 */ ;   
output  wire    [7:0]           mpu_slot2_port      /* synthesis syn_preserve = 1 */ ;   
output  wire    [7:0]           mpu_slot3_port      /* synthesis syn_preserve = 1 */ ;   
output  wire    [7:0]           mpu_slot4_port      /* synthesis syn_preserve = 1 */ ;   
output  wire    [7:0]           mpu_slot5_port      /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot6_port      /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot7_port      /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot8_port      /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot9_port      /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot10_port     /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot11_port     /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot12_port     /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot13_port     /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot14_port     /* synthesis syn_preserve = 1 */ ;   
output  wire    [2:0]           mpu_slot15_port     /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot2_wr_en     /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot3_wr_en     /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot4_wr_en     /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot5_wr_en     /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot6_wr_en     /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot7_wr_en     /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot8_wr_en     /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot9_wr_en     /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot10_wr_en    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot11_wr_en    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot12_wr_en    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot13_wr_en    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot14_wr_en    /* synthesis syn_preserve = 1 */ ;   
output  wire                    mpu_slot15_wr_en    /* synthesis syn_preserve = 1 */ ;  
output  wire    [17:0]          mpu_slot2_wr_data   /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot3_wr_data   /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot4_wr_data   /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot5_wr_data   /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot6_wr_data   /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot7_wr_data   /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot8_wr_data   /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot9_wr_data   /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot10_wr_data  /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot11_wr_data  /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot12_wr_data  /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot13_wr_data  /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot14_wr_data  /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          mpu_slot15_wr_data  /* synthesis syn_preserve = 1 */ ;   
output  wire                    ex1_cfg_wr_sel      /* synthesis syn_preserve = 1 */ ;   
output  wire                    ex2_cfg_wr_sel      /* synthesis syn_preserve = 1 */ ;   
output  wire                    ex3_cfg_wr_sel      /* synthesis syn_preserve = 1 */ ;   
output  wire                    ex4_cfg_wr_sel      /* synthesis syn_preserve = 1 */ ;   
output  wire    [3:0]           ex1_cfg_slot        /* synthesis syn_preserve = 1 */ ;   
output  wire    [3:0]           ex2_cfg_slot        /* synthesis syn_preserve = 1 */ ;   
output  wire    [3:0]           ex3_cfg_slot        /* synthesis syn_preserve = 1 */ ;   
output  wire    [3:0]           ex4_cfg_slot        /* synthesis syn_preserve = 1 */ ;   
output  wire                    ex1_cfg_wr_en       /* synthesis syn_preserve = 1 */ ;   
output  wire                    ex2_cfg_wr_en       /* synthesis syn_preserve = 1 */ ;   
output  wire                    ex3_cfg_wr_en       /* synthesis syn_preserve = 1 */ ;   
output  wire                    ex4_cfg_wr_en       /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          ex1_cfg_wr_data     /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          ex2_cfg_wr_data     /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          ex3_cfg_wr_data     /* synthesis syn_preserve = 1 */ ;   
output  wire    [17:0]          ex4_cfg_wr_data     /* synthesis syn_preserve = 1 */ ;

output  reg     [15:0]          arm_cycle           /* synthesis syn_preserve = 1 */ ;
                                                    
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            cs_fall                             ;   
wire        [3:0]               chn_num                             ;   
wire        [63:0]              wr_data_crc                         ; 
wire        [63:0]              crc64_dout                          ;  
wire                            self_cmm_dval                       ;  
wire                            pkt_err_flag                        ;   

// reg signal
reg                             emif_cs_d1     /* synthesis syn_preserve = 1 */  ;   
reg                             emif_cs_d2     /* synthesis syn_preserve = 1 */  ;   
reg                             emif_cs_d3     /* synthesis syn_preserve = 1 */  ;   
reg                             emif_cs_d4     /* synthesis syn_preserve = 1 */  ;   
reg                             emif_cs_d5     /* synthesis syn_preserve = 1 */  ;   
reg                             ex_cs_fall     /* synthesis syn_preserve = 1 */  ;   
reg                             emif_we_d1     /* synthesis syn_preserve = 1 */  ;   
reg                             emif_we_d2     /* synthesis syn_preserve = 1 */  ;   
reg         [22:0]              emif_addr_d1   /* synthesis syn_preserve = 1 */  ;   
reg         [22:0]              emif_addr_d2   /* synthesis syn_preserve = 1 */  ;   
reg         [22:0]              emif_addr_d3   /* synthesis syn_preserve = 1 */  ;   
reg         [22:0]              emif_addr_lc   /* synthesis syn_preserve = 1 */  ;   
reg         [15:0]              emif_wrdata_d1 /* synthesis syn_preserve = 1 */  ;   
reg         [15:0]              emif_wrdata_d2 /* synthesis syn_preserve = 1 */  ;   
reg         [15:0]              emif_wrdata_d3 /* synthesis syn_preserve = 1 */  ;   
reg         [3:0]               wr_strobe_cnt                       ;   
reg                             wr_dval                             ;   
reg         [4:0]               chn_type    [13:0]                  ;   
reg         [10:0]              pkt_len                             ;   
reg         [10:0]              pkt_len_cnt                         ;  
reg                             wr_sop                              ;   
reg                             wr_eop                              ;   
reg                             wr_eop_d1                           ;   
reg                             wr_eop_d2                           ;   
reg                             wr_eop_d3                           ;   
reg         [1:0]               wr_dval_cnt                         ;   
reg         [15:0]              crc64_data0                         ;   
reg         [15:0]              crc64_data1                         ;   
reg         [15:0]              crc64_data2                         ;   
reg         [63:0]              crc64_data                          ;   
reg                             crc64_dval                          ;   
reg                             crc64_eop                           ;   
reg                             crc_err                             ;  
reg                             crc_flag                            ; 
reg                             pkt_len_err                         ;  
reg                             emif_wr_en                          ;   
reg         [17:0]              emif_wr_data                        ;  
reg         [31:0]              clk_1ms_cnt                         ;
reg                             clk_1ms_flag                        ;   
reg         [15:0]              run_cycle                           ;   
reg         [15:0]              delay_cnt                           ; 
reg                             delay_err                           ; 
reg                             emif_wr_eop       /* synthesis syn_preserve = 1 */ ; 
reg                             sta_cs_fall       /* synthesis syn_preserve = 1 */ ;   
reg         [22:0]              sta_addr          /* synthesis syn_preserve = 1 */ ;  
reg                             sta_eop_d1        /* synthesis syn_preserve = 1 */ ;   
reg                             mpu_cs_fall       /* synthesis syn_preserve = 1 */ ;   
reg         [22:0]              mpu_addr          /* synthesis syn_preserve = 1 */ ;   
reg                             mpu_wr_eop        /* synthesis syn_preserve = 1 */ ;   
reg                             mpu_case_wr_en    /* synthesis syn_preserve = 1 */ ;   
reg         [17:0]              mpu_case_wr_data  /* synthesis syn_preserve = 1 */ ;   
reg                             hrm_cs_fall       /* synthesis syn_preserve = 1 */ ;   
reg         [22:0]              hrm_addr          /* synthesis syn_preserve = 1 */ ;   
reg                             hrm_wr_eop        /* synthesis syn_preserve = 1 */ ;   
reg                             hrm_wr_en_tmp     /* synthesis syn_preserve = 1 */ ;   
reg         [17:0]              hrm_wr_data_tmp   /* synthesis syn_preserve = 1 */ ;   
reg                             type1_cs_fall     /* synthesis syn_preserve = 1 */ ;   
reg         [22:0]              type1_wr_addr     /* synthesis syn_preserve = 1 */ ;   
reg                             type1_wr_eop      /* synthesis syn_preserve = 1 */ ;   
reg                             type1_wr_en       /* synthesis syn_preserve = 1 */ ;   
reg         [17:0]              type1_wr_data     /* synthesis syn_preserve = 1 */ ;   
reg                             type2_cs_fall     /* synthesis syn_preserve = 1 */ ;   
reg         [22:0]              type2_wr_addr     /* synthesis syn_preserve = 1 */ ;   
reg                             type2_wr_eop      /* synthesis syn_preserve = 1 */ ;   
reg                             type2_wr_en       /* synthesis syn_preserve = 1 */ ;   
reg         [17:0]              type2_wr_data     /* synthesis syn_preserve = 1 */ ;   
reg                             type2_1_cs_fall   /* synthesis syn_preserve = 1 */ ;   
reg         [22:0]              type2_1_wr_addr   /* synthesis syn_preserve = 1 */ ;   
reg                             type2_1_wr_eop    /* synthesis syn_preserve = 1 */ ;   
reg                             type2_1_wr_en     /* synthesis syn_preserve = 1 */ ;   
reg         [17:0]              type2_1_wr_data   /* synthesis syn_preserve = 1 */ ;   
reg                             type2_2_cs_fall   /* synthesis syn_preserve = 1 */ ;   
reg         [22:0]              type2_2_wr_addr   /* synthesis syn_preserve = 1 */ ;   
reg                             type2_2_wr_eop    /* synthesis syn_preserve = 1 */ ;   
reg                             type2_2_wr_en     /* synthesis syn_preserve = 1 */ ;   
reg         [17:0]              type2_2_wr_data   /* synthesis syn_preserve = 1 */ ;   
reg                             excfg_cs_fall     /* synthesis syn_preserve = 1 */ ;   
reg         [22:0]              excfg_wr_addr     /* synthesis syn_preserve = 1 */ ;   
reg                             excfg_wr_eop      /* synthesis syn_preserve = 1 */ ;   
reg                             excfg_wr_en       /* synthesis syn_preserve = 1 */ ;   
reg         [17:0]              excfg_wr_data     /* synthesis syn_preserve = 1 */ ;   
reg         [3:0]               slot_num_d1                         ;   
reg         [3:0]               slot_num_d2                         ;   
reg         [7:0]               crc_err_cnt                         ;  
reg                             wr_start                            ;   

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
    emif_cs_d4   <=   emif_cs_d3 ;
    emif_cs_d5   <=   emif_cs_d4 ;
end

assign  cs_fall = ( emif_cs_d3 == 1'b0 && emif_cs_d4 == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        emif_we_d1   <=   1'b1 ;
    end
    else begin
        emif_we_d1   <=   emif_we ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        emif_addr_d1   <=   23'h00 ;
    end
    else begin
        emif_addr_d1   <=   emif_addr ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        emif_wrdata_d1   <=   16'h00 ;
    end
    else begin
        emif_wrdata_d1   <=   emif_wrdata ;
    end
end

always @ ( posedge clk_emif ) begin
    emif_we_d2      <=   emif_we_d1 ;
    emif_addr_d2    <=   emif_addr_d1 ;
    emif_addr_d3    <=   emif_addr_d2 ;
    emif_wrdata_d2  <=   emif_wrdata_d1 ;
    emif_wrdata_d3  <=   emif_wrdata_d2 ;
end

//----------------------------------------------------------------------------------
// emif write control
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        wr_strobe_cnt   <=   4'h0 ;
    end
    else begin
        if( emif_cs_d2 == 1'b0 && emif_we_d2 == 1'b0 && emif_addr_d2[22] == 1'b0 ) begin 
            wr_strobe_cnt   <=   wr_strobe_cnt + 1'b1 ;
        end
        else begin
            wr_strobe_cnt   <=   4'h0 ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    if( wr_strobe_cnt == 3'd2 ) begin
        wr_dval   <=   1'b1 ;
    end
    else begin
        wr_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_emif ) begin
    if( wr_strobe_cnt == 3'd2 && emif_addr_d2[8:0] == 9'h00 ) begin
        wr_sop   <=   1'b1 ;
    end
    else begin
        wr_sop   <=   1'b0 ;
    end
end

// channel board type judge
assign  self_cmm_dval  =   ( self_cfg_wr_sel == 1'b1 && wr_dval == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[0]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd20 ) begin
        chn_type[0]   <=   emif_wrdata_d3[4:0] ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[1]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd20 ) begin
        chn_type[1]   <=   emif_wrdata_d3[12:8] ;
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[2]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd21 ) begin
        chn_type[2]   <=   emif_wrdata_d3[4:0] ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[3]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd21 ) begin
        chn_type[3]   <=   emif_wrdata_d3[12:8] ;
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[4]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd22 ) begin
        chn_type[4]   <=   emif_wrdata_d3[4:0] ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[5]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd22 ) begin
        chn_type[5]   <=   emif_wrdata_d3[12:8] ;
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[6]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd23 ) begin
        chn_type[6]   <=   emif_wrdata_d3[4:0] ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[7]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd23 ) begin
        chn_type[7]   <=   emif_wrdata_d3[12:8] ;
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[8]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd24 ) begin
        chn_type[8]   <=   emif_wrdata_d3[4:0] ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[9]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd24 ) begin
        chn_type[9]   <=   emif_wrdata_d3[12:8] ;
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[10]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd25 ) begin
        chn_type[10]   <=   emif_wrdata_d3[4:0] ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[11]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd25 ) begin
        chn_type[11]   <=   emif_wrdata_d3[12:8] ;
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[12]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd26 ) begin
        chn_type[12]   <=   emif_wrdata_d3[4:0] ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type[13]   <=   `COM3_TYPE ;
    end
    else if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd26 ) begin
        chn_type[13]   <=   emif_wrdata_d3[12:8] ;
    end
end

// pkt_length , data width is 16 , actual length = ( pkt_len * 2 ) byte
assign chn_num = emif_addr_d2[18:15] ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        pkt_len   <=   `IO_LEN ;
    end
    else begin
        if( cs_fall == 3'd1 && emif_addr_d2[8:0] == 9'h00 ) begin
            if ( emif_addr_d2[13] == 1'b1 ) begin
                if ( emif_addr_d2[22] == 1'b0 ) begin
                    pkt_len   <=   11'd8 ;
                end
                else begin
                    pkt_len   <=   `STA_LEN ;
                end
            end
            else if( emif_addr_d2[14] == 1'b0 ) begin
                if ( emif_addr_d2[22] == 1'b0 ) begin
                    pkt_len   <=   `CFG_LEN ;
                end
                else begin
                    pkt_len   <=   `STA_LEN;
                end
            end
            else if( emif_addr_d2[21] == 1'b1 ) begin
                pkt_len   <=   `IO_LEN ;
            end
            else if( emif_addr_d2[18:16] == 3'b000 || chn_type[chn_num-2] == `COM2_TYPE || chn_type[chn_num-2] == `COM3_TYPE ) begin
                pkt_len   <=   `COM_LEN ;
            end
            else begin
                pkt_len   <=   `IO_LEN ;
            end
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        rd_pkt_len   <=   11'h00 ;
    end
    else begin
        rd_pkt_len   <=   pkt_len ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        pkt_len_cnt   <=   11'h00 ;
    end
    else begin
        if( wr_eop_d3 == 1'b1 ) begin
            pkt_len_cnt <=   11'h00 ;
        end
        else if( wr_strobe_cnt == 3'd1 && emif_addr_d2[8:0] == 9'h00 ) begin
            pkt_len_cnt <=   11'h00 ;
        end
        else if( wr_dval == 1'b1 ) begin
            pkt_len_cnt <=   pkt_len_cnt + 1'b1 ;
        end
    end
end

assign  pkt_err_flag = ( wr_strobe_cnt == 3'd2 && emif_addr_d2[8:0] == 9'h00 
                         && pkt_len_cnt != 11'h00 && ( pkt_len_cnt != pkt_len ) ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        pkt_len_err   <=   1'b0 ;
    end
    else begin
        if( wr_eop_d2 == 1'b1 ) begin
            pkt_len_err   <=   1'b0 ;
        end
        else if( pkt_err_flag == 1'b1 ) begin
            pkt_len_err   <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_emif ) begin
  //  if( ( wr_strobe_cnt == 3'd1 && pkt_len_cnt == pkt_len - 1'b1 ) || pkt_err_flag == 1'b1 ) begin
    if( wr_strobe_cnt == 3'd2 && pkt_len_cnt == pkt_len - 1'b1 ) begin
        wr_eop   <=   1'b1 ;
    end
    else begin
        wr_eop   <=   1'b0 ;
    end
end

always @ ( posedge clk_emif ) begin
    wr_eop_d1   <=   wr_eop ;
    wr_eop_d2   <=   wr_eop_d1 ;
    wr_eop_d3   <=   wr_eop_d2 ;
end

always @ ( posedge clk_emif ) begin
 //   if( wr_eop_d3 == 1'b1 && pkt_len_err == 1'b0 ) begin
    if( wr_eop_d3 == 1'b1 ) begin
        emif_wr_eop <=   1'b1 ;
    end
    else begin
        emif_wr_eop <=   1'b0 ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc_flag   <=   1'b0 ;
    end
    else begin
        if( wr_eop == 1'b1 ) begin
            crc_flag   <=   1'b0 ;
        end
        else if( wr_dval == 1'b1 && pkt_len_cnt == pkt_len - 4'd7 ) begin
            crc_flag   <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    if( ( wr_dval == 1'b1 && crc_flag == 1'b0 ) || wr_eop_d1 == 1'b1 || wr_eop_d2 == 1'b1 ) begin
        emif_wr_en   <=   1'b1 ;
    end
    else begin
        emif_wr_en   <=   1'b0 ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        emif_wr_data   <=   18'h00 ;
    end
    else begin
        if( wr_dval == 1'b1 ) begin
            if( wr_sop == 1'b1 ) begin
                emif_wr_data   <=   { 2'b10 , emif_wrdata_d3 } ;
            end
            else begin
                emif_wr_data   <=   { 2'b00 , emif_wrdata_d3 } ;
            end
        end
        else if( wr_eop_d1 == 1'b1 ) begin
            emif_wr_data   <=   18'h00 ;
        end
        else if( wr_eop_d2 == 1'b1 ) begin
            emif_wr_data   <=   { 2'b01 , 4'h0 , self_cfg_err , delay_err , pkt_len_err , crc_err , 8'h00 } ;
        end
    end
end


//----------------------------------------------------------------------------------
// delay check 
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        clk_1ms_cnt   <=   32'h00 ;
    end
    else begin
        if( clk_1ms_cnt == CNT_1MS ) begin
            clk_1ms_cnt   <=   32'h00 ;
        end
        else begin
            clk_1ms_cnt   <=   clk_1ms_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    if( clk_1ms_cnt == CNT_1MS ) begin
        clk_1ms_flag   <=   1'b1 ;
    end
    else begin
        clk_1ms_flag   <=   1'b0 ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        run_cycle   <=   16'd33 ;
    end
    else begin
        if( self_cmm_dval == 1'b1 && pkt_len_cnt == 11'd6 ) begin
            run_cycle   <=   emif_wrdata_d3[15:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        arm_cycle   <=   16'd33 ;
    end
    else begin
        arm_cycle   <=  run_cycle;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        delay_cnt   <=   16'h00 ;
    end
    else begin
        if( wr_eop == 1'b1 ) begin
            delay_cnt   <=   16'h00 ;
        end
        else if ( clk_1ms_flag == 1'b1 ) begin
            delay_cnt   <=   delay_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        delay_err   <=   1'b0 ;
    end
    else begin
        if( delay_cnt >= run_cycle + 2'b11 ) begin
            delay_err   <=   1'b1 ;
        end
        else begin
            delay_err   <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// write data CRC64 check
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        wr_dval_cnt   <=   2'b00 ;
    end
    else begin
        if( wr_strobe_cnt == 3'd1 && emif_addr_d2[8:0] == 9'h00 ) begin
            wr_dval_cnt   <=   2'b00 ;
        end
        else if( wr_dval == 1'b1 ) begin
            wr_dval_cnt   <=   wr_dval_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc64_data0   <=   16'h00 ;
    end
    else begin
        if( wr_dval == 1'b1 && wr_dval_cnt == 2'b00 ) begin
            crc64_data0   <=   emif_wrdata_d3 ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc64_data1   <=   16'h00 ;
    end
    else begin
        if( wr_dval == 1'b1 && wr_dval_cnt == 2'b01 ) begin
            crc64_data1   <=   emif_wrdata_d3 ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc64_data2   <=   16'h00 ;
    end
    else begin
        if( wr_dval == 1'b1 && wr_dval_cnt == 2'b10 ) begin
            crc64_data2   <=   emif_wrdata_d3 ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc64_data   <=   64'h00 ;
    end
    else begin
        if( wr_dval == 1'b1 && wr_dval_cnt == 2'b11 ) begin
            crc64_data   <=   { emif_wrdata_d3 , crc64_data2 , crc64_data1 , crc64_data0 } ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    if( wr_dval == 1'b1 && wr_dval_cnt == 2'b11 && wr_eop == 1'b0 ) begin
        crc64_dval   <=   1'b1 ;
    end
    else begin
        crc64_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_emif ) begin
    if( wr_dval == 1'b1 && pkt_len_cnt == pkt_len - 5 ) begin
        crc64_eop   <=   1'b1 ;
    end
    else begin
        crc64_eop   <=   1'b0 ;
    end
end


    CRC64D64                    U_CRC64D64 
    (
    //input port
    .clk_sys                    ( clk_emif                  ),
    .rst_sys                    ( rst_emif                  ),
    .crc_din                    ( crc64_data                ),
    .crc_cap                    ( crc64_eop                 ),
    .crc_sop                    ( wr_sop                    ),
    .crc_din_vld                ( crc64_dval                ),
    //output port
    .crc_dout                   ( crc64_dout                )
    );

assign  wr_data_crc = { crc64_data0[7:0] , crc64_data0[15:8] , crc64_data1[7:0]    , crc64_data1[15:8] ,
                        crc64_data2[7:0] , crc64_data2[15:8] , emif_wrdata_d3[7:0] , emif_wrdata_d3[15:8] } ;

`ifdef  SIM
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc_err   <=   1'b0 ;
    end
    else begin
        if( wr_sop == 1'b1 ) begin
            crc_err   <=   1'b0 ;
        end
        else if( wr_eop_d1 == 1'b1 ) begin
            if( crc64_dout != wr_data_crc ) begin
                crc_err   <=   1'b1 ;
            end
            else begin
                crc_err   <=   1'b0 ;
            end
        end
    end
end

`else
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc_err   <=   1'b0 ;
    end
    else begin
        if( wr_sop == 1'b1 ) begin
            crc_err   <=   1'b0 ;
        end
        else if( wr_eop_d1 == 1'b1 ) begin
            if( crc64_dout != crc64_data ) begin
                crc_err   <=   1'b1 ;
            end
            else begin
                crc_err   <=   1'b0 ;
            end
        end
    end
end
`endif

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        crc_err_cnt  <=   8'h00 ;
    end
    else begin
        if( crc_err_cnt == 8'hff ) begin
            crc_err_cnt  <=   crc_err_cnt ;
        end
        else if( wr_eop_d3 == 1'b1 && crc_err == 1'b1 ) begin
            crc_err_cnt  <=   crc_err_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    if( crc_err_cnt >= CRC_ERR_THRESHOLD ) begin
        emif_err  <=   1'b1 ;
    end
    else begin
        emif_err  <=   1'b0 ;
    end
end

//----------------------------------------------------------------------------------
// fist level logic copy
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif ) begin
    if ( cs_fall == 1'b1 && emif_addr_d1[8:0] == 9'h00 ) begin
        wr_start    <=  1'b1 ;
    end
    else begin
        wr_start    <=  1'b0 ;
    end
end

always @ ( posedge clk_emif ) begin
    emif_addr_lc    <=   emif_addr_d1 ;
end

always @ ( posedge clk_emif ) begin
    sta_cs_fall        <=   wr_start ;
    sta_addr           <=   emif_addr_lc ;
    sta_eop_d1         <=   emif_wr_eop ;
end

always @ ( posedge clk_emif ) begin
    mpu_cs_fall        <=   wr_start ;
    mpu_addr           <=   emif_addr_lc ;
    mpu_wr_eop         <=   emif_wr_eop ;
    mpu_case_wr_en     <=   emif_wr_en ;
    mpu_case_wr_data   <=   emif_wr_data ;
end

//----------------------------------------------------------------------------------
// second level logic copy  ( MPU case )
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif ) begin
    hrm_cs_fall     <=   mpu_cs_fall      ; 
    hrm_addr        <=   mpu_addr         ; 
    hrm_wr_eop      <=   mpu_wr_eop       ; 
    hrm_wr_en_tmp   <=   mpu_case_wr_en   ; 
    hrm_wr_data_tmp <=   mpu_case_wr_data ; 
end

always @ ( posedge clk_emif ) begin
    type1_cs_fall   <=   mpu_cs_fall      ; 
    type1_wr_addr   <=   mpu_addr         ; 
    type1_wr_eop    <=   mpu_wr_eop       ; 
    type1_wr_en     <=   mpu_case_wr_en   ; 
    type1_wr_data   <=   mpu_case_wr_data ; 
end

always @ ( posedge clk_emif ) begin
    type2_cs_fall   <=   mpu_cs_fall      ; 
    type2_wr_addr   <=   mpu_addr         ; 
    type2_wr_eop    <=   mpu_wr_eop       ; 
    type2_wr_en     <=   mpu_case_wr_en   ; 
    type2_wr_data   <=   mpu_case_wr_data ; 
end

//----------------------------------------------------------------------------------
// third level logic copy  
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif ) begin
    type2_1_cs_fall   <=   type2_cs_fall ; 
    type2_1_wr_addr   <=   type2_wr_addr ; 
    type2_1_wr_eop    <=   type2_wr_eop  ; 
    type2_1_wr_en     <=   type2_wr_en   ; 
    type2_1_wr_data   <=   type2_wr_data ; 
end

always @ ( posedge clk_emif ) begin
    type2_2_cs_fall   <=   type2_cs_fall ; 
    type2_2_wr_addr   <=   type2_wr_addr ; 
    type2_2_wr_eop    <=   type2_wr_eop  ; 
    type2_2_wr_en     <=   type2_wr_en   ; 
    type2_2_wr_data   <=   type2_wr_data ; 
end

always @ ( posedge clk_emif ) begin
    excfg_cs_fall   <=   type2_cs_fall ; 
    excfg_wr_addr   <=   type2_wr_addr ; 
    excfg_wr_eop    <=   type2_wr_eop  ; 
    excfg_wr_en     <=   type2_wr_en   ; 
    excfg_wr_data   <=   type2_wr_data ; 
end

//----------------------------------------------------------------------------------
// self configuration 
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        slot_num_d1   <=   4'h00 ;
        slot_num_d2   <=   4'h00 ;
    end
    else begin
        slot_num_d1   <=   slot_num ;
        slot_num_d2   <=   slot_num_d1 ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        self_cfg_wr_sel   <=   1'b0 ;
    end
    else begin
        if ( sta_eop_d1 == 1'b1 ) begin
            self_cfg_wr_sel   <=   1'b0 ;
        end
        else if( sta_cs_fall == 1'b1 ) begin
            if( sta_addr[22:19] == 4'b0000 && sta_addr[18:15] == slot_num_d2 && sta_addr[14:13] == 2'b00 ) begin 
                self_cfg_wr_sel  <=   1'b1 ;
            end
            else begin
                self_cfg_wr_sel  <=   1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_emif ) begin
    self_cfg_wr_en     <=   emif_wr_en ;
    self_cfg_wr_data   <=   emif_wr_data ;
end

//----------------------------------------------------------------------------------
// arm status
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        self_sta_wr_sel   <=   1'b0 ;
    end
    else begin
        if ( sta_eop_d1 == 1'b1 ) begin
            self_sta_wr_sel   <=   1'b0 ;
        end
        else if( sta_cs_fall == 1'b1 ) begin
            if( sta_addr[22:13] == 10'b00_00_0000_01 ) begin 
                self_sta_wr_sel  <=   1'b1 ;
            end
            else begin
                self_sta_wr_sel  <=   1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_emif ) begin
    self_sta_wr_en     <=   emif_wr_en ;
    self_sta_wr_data   <=   emif_wr_data[15:0] ;
end

//----------------------------------------------------------------------------------
// rm data
//----------------------------------------------------------------------------------
// prm data
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        prm_wr_sel  <=   1'b0 ;
    end
    else begin
        if ( hrm_wr_eop == 1'b1 ) begin
            prm_wr_sel   <=   1'b0 ;
        end
        else if( hrm_cs_fall == 1'b1 ) begin
            if( hrm_addr[22:21] == 2'b00 && hrm_addr[20:13] == 8'b00_0000_10 ) begin 
                prm_wr_sel  <=   1'b1 ;
            end
            else begin
                prm_wr_sel  <=   1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_emif ) begin
    prm_pkt_num   <=   hrm_addr[12:9] ; 
    prm_wr_en     <=   hrm_wr_en_tmp ;
    prm_wr_data   <=   hrm_wr_data_tmp ;
end

// hrm data
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        hrm_wr_sel  <=   1'b0 ;
    end
    else begin
        if ( hrm_wr_eop == 1'b1 ) begin
            hrm_wr_sel   <=   1'b0 ;
        end
        else if( hrm_cs_fall == 1'b1 ) begin
            if( hrm_addr[22:21] == 2'b00 && hrm_addr[20:13] == 8'b00_0001_10 ) begin 
                hrm_wr_sel  <=   1'b1 ;
            end
            else begin
                hrm_wr_sel  <=   1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_emif ) begin
    hrm_pkt_num   <=   hrm_addr[12:9] ; 
    hrm_wr_en     <=   hrm_wr_en_tmp ;
    hrm_wr_data   <=   hrm_wr_data_tmp ;
end

//----------------------------------------------------------------------------------
// MPU slot
//----------------------------------------------------------------------------------
//  slot2 data & config
    TYPE1_WR                    U_0_TYPE1_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type1_cs_fall             ),
    .wr_en                      ( type1_wr_en               ),
    .wr_addr                    ( type1_wr_addr             ),
    .wr_data                    ( type1_wr_data             ),
    .wr_eop                     ( type1_wr_eop              ),

    .type1_wr_sel               ( mpu_slot2_wr_sel          ),
    .type1_wr_en                ( mpu_slot2_wr_en           ),
    .type1_wr_port              ( mpu_slot2_port            ),
    .type1_wr_data              ( mpu_slot2_wr_data         )
    );

//  slot3 data & config
    TYPE1_WR                    U_1_TYPE1_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type1_cs_fall             ),
    .wr_en                      ( type1_wr_en               ),
    .wr_addr                    ( type1_wr_addr             ),
    .wr_data                    ( type1_wr_data             ),
    .wr_eop                     ( type1_wr_eop              ),

    .type1_wr_sel               ( mpu_slot3_wr_sel          ),
    .type1_wr_en                ( mpu_slot3_wr_en           ),
    .type1_wr_port              ( mpu_slot3_port            ),
    .type1_wr_data              ( mpu_slot3_wr_data         )
    );

//  slot4 data & config
    TYPE1_WR                    U_2_TYPE1_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type1_cs_fall             ),
    .wr_en                      ( type1_wr_en               ),
    .wr_addr                    ( type1_wr_addr             ),
    .wr_data                    ( type1_wr_data             ),
    .wr_eop                     ( type1_wr_eop              ),

    .type1_wr_sel               ( mpu_slot4_wr_sel          ),
    .type1_wr_en                ( mpu_slot4_wr_en           ),
    .type1_wr_port              ( mpu_slot4_port            ),
    .type1_wr_data              ( mpu_slot4_wr_data         )
    );

//  slot5 data & config
    TYPE1_WR                    U_3_TYPE1_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type1_cs_fall             ),
    .wr_en                      ( type1_wr_en               ),
    .wr_addr                    ( type1_wr_addr             ),
    .wr_data                    ( type1_wr_data             ),
    .wr_eop                     ( type1_wr_eop              ),

    .type1_wr_sel               ( mpu_slot5_wr_sel          ),
    .type1_wr_en                ( mpu_slot5_wr_en           ),
    .type1_wr_port              ( mpu_slot5_port            ),
    .type1_wr_data              ( mpu_slot5_wr_data         )
    );

// mpu slot6 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd6                      )
    )
    U_0_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_1_cs_fall           ),
    .wr_en                      ( type2_1_wr_en             ),
    .wr_addr                    ( type2_1_wr_addr           ),
    .wr_data                    ( type2_1_wr_data           ),
    .wr_eop                     ( type2_1_wr_eop            ),

    .type2_wr_sel               ( mpu_slot6_wr_sel          ),
    .type2_wr_en                ( mpu_slot6_wr_en           ),
    .type2_wr_port              ( mpu_slot6_port            ),
    .type2_wr_data              ( mpu_slot6_wr_data         )
    );

// mpu slot7 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd7                      )
    )
    U_1_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_1_cs_fall           ),
    .wr_en                      ( type2_1_wr_en             ),
    .wr_addr                    ( type2_1_wr_addr           ),
    .wr_data                    ( type2_1_wr_data           ),
    .wr_eop                     ( type2_1_wr_eop            ),

    .type2_wr_sel               ( mpu_slot7_wr_sel          ),
    .type2_wr_en                ( mpu_slot7_wr_en           ),
    .type2_wr_port              ( mpu_slot7_port            ),
    .type2_wr_data              ( mpu_slot7_wr_data         )
    );

// mpu slot8 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd8                      )
    )
    U_2_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_1_cs_fall           ),
    .wr_en                      ( type2_1_wr_en             ),
    .wr_addr                    ( type2_1_wr_addr           ),
    .wr_data                    ( type2_1_wr_data           ),
    .wr_eop                     ( type2_1_wr_eop            ),

    .type2_wr_sel               ( mpu_slot8_wr_sel          ),
    .type2_wr_en                ( mpu_slot8_wr_en           ),
    .type2_wr_port              ( mpu_slot8_port            ),
    .type2_wr_data              ( mpu_slot8_wr_data         )
    );

// mpu slot9 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd9                      )
    )
    U_3_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_1_cs_fall           ),
    .wr_en                      ( type2_1_wr_en             ),
    .wr_addr                    ( type2_1_wr_addr           ),
    .wr_data                    ( type2_1_wr_data           ),
    .wr_eop                     ( type2_1_wr_eop            ),

    .type2_wr_sel               ( mpu_slot9_wr_sel          ),
    .type2_wr_en                ( mpu_slot9_wr_en           ),
    .type2_wr_port              ( mpu_slot9_port            ),
    .type2_wr_data              ( mpu_slot9_wr_data         )
    );

// mpu slot10 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd10                     )
    )
    U_4_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_1_cs_fall           ),
    .wr_en                      ( type2_1_wr_en             ),
    .wr_addr                    ( type2_1_wr_addr           ),
    .wr_data                    ( type2_1_wr_data           ),
    .wr_eop                     ( type2_1_wr_eop            ),

    .type2_wr_sel               ( mpu_slot10_wr_sel         ),
    .type2_wr_en                ( mpu_slot10_wr_en          ),
    .type2_wr_port              ( mpu_slot10_port           ),
    .type2_wr_data              ( mpu_slot10_wr_data        )
    );

// mpu slot11 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd11                     )
    )
    U_5_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_2_cs_fall           ),
    .wr_en                      ( type2_2_wr_en             ),
    .wr_addr                    ( type2_2_wr_addr           ),
    .wr_data                    ( type2_2_wr_data           ),
    .wr_eop                     ( type2_2_wr_eop            ),

    .type2_wr_sel               ( mpu_slot11_wr_sel         ),
    .type2_wr_en                ( mpu_slot11_wr_en          ),
    .type2_wr_port              ( mpu_slot11_port           ),
    .type2_wr_data              ( mpu_slot11_wr_data        )
    );

// mpu slot12 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd12                     )
    )
    U_6_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_2_cs_fall           ),
    .wr_en                      ( type2_2_wr_en             ),
    .wr_addr                    ( type2_2_wr_addr           ),
    .wr_data                    ( type2_2_wr_data           ),
    .wr_eop                     ( type2_2_wr_eop            ),

    .type2_wr_sel               ( mpu_slot12_wr_sel         ),
    .type2_wr_en                ( mpu_slot12_wr_en          ),
    .type2_wr_port              ( mpu_slot12_port           ),
    .type2_wr_data              ( mpu_slot12_wr_data        )
    );

// mpu slot13 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd13                     )
    )
    U_7_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_2_cs_fall           ),
    .wr_en                      ( type2_2_wr_en             ),
    .wr_addr                    ( type2_2_wr_addr           ),
    .wr_data                    ( type2_2_wr_data           ),
    .wr_eop                     ( type2_2_wr_eop            ),

    .type2_wr_sel               ( mpu_slot13_wr_sel         ),
    .type2_wr_en                ( mpu_slot13_wr_en          ),
    .type2_wr_port              ( mpu_slot13_port           ),
    .type2_wr_data              ( mpu_slot13_wr_data        )
    );

// mpu slot14 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd14                     )
    )
    U_8_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_2_cs_fall           ),
    .wr_en                      ( type2_2_wr_en             ),
    .wr_addr                    ( type2_2_wr_addr           ),
    .wr_data                    ( type2_2_wr_data           ),
    .wr_eop                     ( type2_2_wr_eop            ),

    .type2_wr_sel               ( mpu_slot14_wr_sel         ),
    .type2_wr_en                ( mpu_slot14_wr_en          ),
    .type2_wr_port              ( mpu_slot14_port           ),
    .type2_wr_data              ( mpu_slot14_wr_data        )
    );

// mpu slot15 data & config
    TYPE2_WR                    #
    (
    .SLOT_NUM                   ( 4'd15                     )
    )
    U_9_TYPE2_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( type2_2_cs_fall           ),
    .wr_en                      ( type2_2_wr_en             ),
    .wr_addr                    ( type2_2_wr_addr           ),
    .wr_data                    ( type2_2_wr_data           ),
    .wr_eop                     ( type2_2_wr_eop            ),

    .type2_wr_sel               ( mpu_slot15_wr_sel         ),
    .type2_wr_en                ( mpu_slot15_wr_en          ),
    .type2_wr_port              ( mpu_slot15_port           ),
    .type2_wr_data              ( mpu_slot15_wr_data        )
    );

//----------------------------------------------------------------------------------
// EX BOX CONFIG
//----------------------------------------------------------------------------------
// ex1 config
    EXCFG_WR                    #
    (
    .EX_NUM                     ( 2'd0                      )
    )
    U_0_EXCFG_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( excfg_cs_fall             ),
    .wr_en                      ( excfg_wr_en               ),
    .wr_addr                    ( excfg_wr_addr             ),
    .wr_data                    ( excfg_wr_data             ),
    .wr_eop                     ( excfg_wr_eop              ),

    .excfg_wr_sel               ( ex1_cfg_wr_sel            ),
    .excfg_wr_en                ( ex1_cfg_wr_en             ),
    .excfg_wr_slot              ( ex1_cfg_slot              ),
    .excfg_wr_data              ( ex1_cfg_wr_data           )
    );

// ex2 config
    EXCFG_WR                    #
    (
    .EX_NUM                     ( 2'd1                      )
    )
    U_1_EXCFG_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( excfg_cs_fall             ),
    .wr_en                      ( excfg_wr_en               ),
    .wr_addr                    ( excfg_wr_addr             ),
    .wr_data                    ( excfg_wr_data             ),
    .wr_eop                     ( excfg_wr_eop              ),

    .excfg_wr_sel               ( ex2_cfg_wr_sel            ),
    .excfg_wr_en                ( ex2_cfg_wr_en             ),
    .excfg_wr_slot              ( ex2_cfg_slot              ),
    .excfg_wr_data              ( ex2_cfg_wr_data           )
    );

// ex3 config
    EXCFG_WR                    #
    (
    .EX_NUM                     ( 2'd2                      )
    )
    U_2_EXCFG_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( excfg_cs_fall             ),
    .wr_en                      ( excfg_wr_en               ),
    .wr_addr                    ( excfg_wr_addr             ),
    .wr_data                    ( excfg_wr_data             ),
    .wr_eop                     ( excfg_wr_eop              ),

    .excfg_wr_sel               ( ex3_cfg_wr_sel            ),
    .excfg_wr_en                ( ex3_cfg_wr_en             ),
    .excfg_wr_slot              ( ex3_cfg_slot              ),
    .excfg_wr_data              ( ex3_cfg_wr_data           )
    );

// ex4 config
    EXCFG_WR                    #
    (
    .EX_NUM                     ( 2'd3                      )
    )
    U_3_EXCFG_WR
    (
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .cs_fall                    ( excfg_cs_fall             ),
    .wr_en                      ( excfg_wr_en               ),
    .wr_addr                    ( excfg_wr_addr             ),
    .wr_data                    ( excfg_wr_data             ),
    .wr_eop                     ( excfg_wr_eop              ),

    .excfg_wr_sel               ( ex4_cfg_wr_sel            ),
    .excfg_wr_en                ( ex4_cfg_wr_en             ),
    .excfg_wr_slot              ( ex4_cfg_slot              ),
    .excfg_wr_data              ( ex4_cfg_wr_data           )
    );


endmodule

