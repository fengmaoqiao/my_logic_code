// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SELF_CMM
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
// PURPOSE          :   The configuration Memory Management of MPU board self
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

module  MPU_CASE_STA
    (
    // clock & reset
    clk_150m                    ,   
    rst_150m                    , 

    clk_12_5m                    ,
    rst_12_5m                   ,  

    // connect to EMIF module
    mpu_sta_rd_sel              ,   
    mpu_rd_addr                 ,   
    mpu_rd_data                 ,

    uart_dval                   ,
    uart_sel                    ,
    uart_addr                   ,
    uart_data                   ,

    // configuration
    other_online                ,
    card_id                     ,   
    code_version                ,   
    enable_slot                 ,  
    slot_num                    ,   
    sta_num                     ,   
    box_num                     ,   
    hmcu_oline                  ,   
    pmcu_oline                  ,
    emif_self_cfg_err           ,   
    hotr_self_cfg_err           ,   
    type1_self_cfg_err          ,   
    type2_self_cfg_err          ,   
    emif_err                    ,   
    mpu_cfg_wr_ok               ,   

    // state frame
    slot2_sta_dval              ,   
    slot2_sta_data              ,   
    slot3_sta_dval              ,   
    slot3_sta_data              ,   
    slot4_sta_dval              ,   
    slot4_sta_data              ,   
    slot5_sta_dval              ,   
    slot5_sta_data              ,   
    slot6_sta_dval              ,   
    slot6_sta_data              ,   
    slot7_sta_dval              ,   
    slot7_sta_data              ,   
    slot8_sta_dval              ,   
    slot8_sta_data              ,   
    slot9_sta_dval              ,   
    slot9_sta_data              ,   
    slot10_sta_dval             ,   
    slot10_sta_data             ,   
    slot11_sta_dval             ,   
    slot11_sta_data             ,   
    slot12_sta_dval             ,   
    slot12_sta_data             ,   
    slot13_sta_dval             ,   
    slot13_sta_data             ,   
    slot14_sta_dval             ,   
    slot14_sta_data             ,   
    slot15_sta_dval             ,   
    slot15_sta_data             ,   
    
    // slink channel diagnose result
    dst_sta_num                   ,   
    prm_slink_err               ,   
    hrm_slink_err               , 
    type1_slink_err             ,   
    type2_slink_err             ,   
    slink_err                     
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam      FB_CHECK_SLOT =   32'd62500000;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_150m                            ;    
input   wire                    rst_150m                            ; 

input   wire                    clk_12_5m                           ;
input   wire                    rst_12_5m                           ;   

input   wire                    mpu_sta_rd_sel                      ;   
input   wire        [8:0]       mpu_rd_addr                         ;   
input   wire        [13:0]      other_online                        ;  
input   wire                    hmcu_oline                          ;   
input   wire                    pmcu_oline                          ;   
input   wire        [31:0]      card_id                             ;   
input   wire        [15:0]      code_version                        ;   
input   wire        [15:0]      enable_slot                         ;   
input   wire        [3:0]       slot_num                            ;   
input   wire        [7:0]       sta_num                             ;   
input   wire        [2:0]       box_num                             ;   
input   wire                    emif_err                            ; 
input   wire                    mpu_cfg_wr_ok                       ;

input   wire                    uart_dval                           ;
input   wire                    uart_sel                            ;
input   wire                    uart_addr                           ;

output  reg         [15:0]      uart_data                           ;

input   wire                    slot2_sta_dval                      ;   
input   wire        [17:0]      slot2_sta_data                      ;   
input   wire                    slot3_sta_dval                      ;   
input   wire        [17:0]      slot3_sta_data                      ;   
input   wire                    slot4_sta_dval                      ;   
input   wire        [17:0]      slot4_sta_data                      ;   
input   wire                    slot5_sta_dval                      ;   
input   wire        [17:0]      slot5_sta_data                      ;   
input   wire                    slot6_sta_dval                      ;   
input   wire        [17:0]      slot6_sta_data                      ;   
input   wire                    slot7_sta_dval                      ;   
input   wire        [17:0]      slot7_sta_data                      ;   
input   wire                    slot8_sta_dval                      ;   
input   wire        [17:0]      slot8_sta_data                      ;   
input   wire                    slot9_sta_dval                      ;   
input   wire        [17:0]      slot9_sta_data                      ;   
input   wire                    slot10_sta_dval                     ;   
input   wire        [17:0]      slot10_sta_data                     ;   
input   wire                    slot11_sta_dval                     ;   
input   wire        [17:0]      slot11_sta_data                     ;   
input   wire                    slot12_sta_dval                     ;   
input   wire        [17:0]      slot12_sta_data                     ;   
input   wire                    slot13_sta_dval                     ;   
input   wire        [17:0]      slot13_sta_data                     ;   
input   wire                    slot14_sta_dval                     ;   
input   wire        [17:0]      slot14_sta_data                     ;   
input   wire                    slot15_sta_dval                     ;   
input   wire        [17:0]      slot15_sta_data                     ;   

input   wire                    prm_slink_err                       ;   
input   wire                    hrm_slink_err                       ;   
input   wire        [3:0]       type1_slink_err                     ;   
input   wire        [9:0]       type2_slink_err                     ;   

// declare output signal
output  reg                     emif_self_cfg_err   /* synthesis syn_preserve = 1 */ ;   
output  reg                     hotr_self_cfg_err   /* synthesis syn_preserve = 1 */ ;   
output  reg         [3:0]       type1_self_cfg_err  /* synthesis syn_preserve = 1 */ ;   
output  reg         [9:0]       type2_self_cfg_err  /* synthesis syn_preserve = 1 */ ;   
output  wire        [15:0]      slink_err                           ;   
output  reg         [15:0]      mpu_rd_data                         ;   
output  reg         [7:0]       dst_sta_num                           ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            self_cfg_err                        ;   
wire        [7:0]               cfg_feedback                        ;  
wire                            hr_feedback                         ;   
wire        [15:0]              online_detect                       ; 
wire        [15:0]              chn_slink_err                       ;   
wire        [15:0]              mpu_slot_sta1   [13:0]              ;   
wire        [15:0]              mpu_slot_sta2   [13:0]              ;  
wire        [13:0]              slot_sta_dval                       ;  
wire        [17:0]              slot_sta_data   [13:0]              ;

// reg signal
reg                                 emif_err_d1                         ;   
reg             [3:0]               slot_num_d1                         ;   
reg             [3:0]               slot_num_d2                         ;   
reg             [7:0]               sta_num_d1                          ;   
reg             [7:0]               sta_num_d2                          ;   
reg             [2:0]               box_num_d1                          ;   
reg             [2:0]               box_num_d2                          ; 
reg             [15:0]              online_detect_d1                    ;   
reg             [15:0]              online_detect_d2                    ;   
reg                                 slot_num_feedback                   ;   
reg                                 sta_num_feedback                    ;   
reg                                 box_num_feedback                    ;   
reg                                 board_type_feedback                 ;   
reg                                 version_feedback                    ;   
reg             [13:0]              enable_slot_feedback                ;   
reg             [31:0]              card_id_d1                          ;   
reg             [15:0]              code_version_d1                     ;   
reg             [15:0]              enable_slot_d1                      ;  
reg                                 feedback_check_point                ;
reg             [31:0]              check_point_cnt                     ;

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        mpu_rd_data    <=   16'h00 ;
    end
    else if( mpu_sta_rd_sel == 1'b1 ) begin
        case( mpu_rd_addr )
            9'd0    :   mpu_rd_data <=   { 7'h00 , emif_err_d1 , cfg_feedback } ;
            9'd1    :   mpu_rd_data <=   { slink_err[7:0] , slink_err[15:8] } ;
            9'd2    :   mpu_rd_data <=   16'h00 ;
            9'd3    :   mpu_rd_data <=   16'h00 ;
            9'd4    :   mpu_rd_data <=   { mpu_slot_sta1[0][7:0]  , mpu_slot_sta1[0][15:7] , enable_slot_feedback[0] } ;
            9'd5    :   mpu_rd_data <=   { mpu_slot_sta2[0][7:0]  , mpu_slot_sta2[0][15:8]  } ;
            9'd6    :   mpu_rd_data <=   { mpu_slot_sta1[1][7:0]  , mpu_slot_sta1[1][15:7] , enable_slot_feedback[1] } ;
            9'd7    :   mpu_rd_data <=   { mpu_slot_sta2[1][7:0]  , mpu_slot_sta2[1][15:8]  } ;
            9'd8    :   mpu_rd_data <=   { mpu_slot_sta1[2][7:0]  , mpu_slot_sta1[2][15:7] , enable_slot_feedback[2] } ;
            9'd9    :   mpu_rd_data <=   { mpu_slot_sta2[2][7:0]  , mpu_slot_sta2[2][15:8]  } ;
            9'd10   :   mpu_rd_data <=   { mpu_slot_sta1[3][7:0]  , mpu_slot_sta1[3][15:7] , enable_slot_feedback[3] } ;
            9'd11   :   mpu_rd_data <=   { mpu_slot_sta2[3][7:0]  , mpu_slot_sta2[3][15:8]  } ;
            9'd12   :   mpu_rd_data <=   { mpu_slot_sta1[4][7:0]  , mpu_slot_sta1[4][15:7] , enable_slot_feedback[4] } ;
            9'd13   :   mpu_rd_data <=   { mpu_slot_sta2[4][7:0]  , mpu_slot_sta2[4][15:8]  } ;
            9'd14   :   mpu_rd_data <=   { mpu_slot_sta1[5][7:0]  , mpu_slot_sta1[5][15:7] , enable_slot_feedback[5] } ;
            9'd15   :   mpu_rd_data <=   { mpu_slot_sta2[5][7:0]  , mpu_slot_sta2[5][15:8]  } ;
            9'd16   :   mpu_rd_data <=   { mpu_slot_sta1[6][7:0]  , mpu_slot_sta1[6][15:7] , enable_slot_feedback[6] } ;
            9'd17   :   mpu_rd_data <=   { mpu_slot_sta2[6][7:0]  , mpu_slot_sta2[6][15:8]  } ;
            9'd18   :   mpu_rd_data <=   { mpu_slot_sta1[7][7:0]  , mpu_slot_sta1[7][15:7] , enable_slot_feedback[7] } ;
            9'd19   :   mpu_rd_data <=   { mpu_slot_sta2[7][7:0]  , mpu_slot_sta2[7][15:8]  } ;
            9'd20   :   mpu_rd_data <=   { mpu_slot_sta1[8][7:0]  , mpu_slot_sta1[8][15:7] , enable_slot_feedback[8] } ;
            9'd21   :   mpu_rd_data <=   { mpu_slot_sta2[8][7:0]  , mpu_slot_sta2[8][15:8] } ;
            9'd22   :   mpu_rd_data <=   { mpu_slot_sta1[9][7:0]  , mpu_slot_sta1[9][15:7] , enable_slot_feedback[9] } ;
            9'd23   :   mpu_rd_data <=   { mpu_slot_sta2[9][7:0]  , mpu_slot_sta2[9][15:8] } ;
            9'd24   :   mpu_rd_data <=   { mpu_slot_sta1[10][7:0] , mpu_slot_sta1[10][15:7] , enable_slot_feedback[10] } ;
            9'd25   :   mpu_rd_data <=   { mpu_slot_sta2[10][7:0] , mpu_slot_sta2[10][15:8] } ;
            9'd26   :   mpu_rd_data <=   { mpu_slot_sta1[11][7:0] , mpu_slot_sta1[11][15:7] , enable_slot_feedback[11] } ;
            9'd27   :   mpu_rd_data <=   { mpu_slot_sta2[11][7:0] , mpu_slot_sta2[11][15:8] } ;
            9'd28   :   mpu_rd_data <=   { mpu_slot_sta1[12][7:0] , mpu_slot_sta1[12][15:7] , enable_slot_feedback[12] } ;
            9'd29   :   mpu_rd_data <=   { mpu_slot_sta2[12][7:0] , mpu_slot_sta2[12][15:8] } ;
            9'd30   :   mpu_rd_data <=   { mpu_slot_sta1[13][7:0] , mpu_slot_sta1[13][15:7] , enable_slot_feedback[13] } ;
            9'd31   :   mpu_rd_data <=   { mpu_slot_sta2[13][7:0] , mpu_slot_sta2[13][15:8] } ;
            default :   mpu_rd_data <=   16'h00 ;       
        endcase                                         
    end                                                 
    else begin                                          
        mpu_rd_data    <=   16'h00 ;
    end
end


always @( posedge clk_12_5m or negedge rst_12_5m ) begin 
    if( ~rst_12_5m ) begin
         check_point_cnt <= 32'd0;
    end else begin
        if ( check_point_cnt == 32'd0 ) 
            check_point_cnt <= FB_CHECK_SLOT;
        else
            check_point_cnt <= check_point_cnt - 1;
    end
end

always @( posedge clk_12_5m or negedge rst_12_5m ) begin 
    if( ~rst_12_5m ) begin
         feedback_check_point <= 1'b0 ;
    end else begin
        if( check_point_cnt == 32'd0 )
            feedback_check_point <= 1'b1 ;
        else
            feedback_check_point <= 1'b0;    
    end
end
//----------------------------------------------------------------------------------
// 
//----------------------------------------------------------------------------------
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        uart_data   <= 16'h0;        
    end
    else begin
        if(uart_sel)
            case(uart_addr)
            9'd0    :   uart_data <=   { 7'h00 , emif_err_d1 , cfg_feedback } ;
            9'd1    :   uart_data <=   { slink_err[7:0] , slink_err[15:8] } ;
            9'd2    :   uart_data <=   16'h00 ;
            9'd3    :   uart_data <=   16'h00 ;
            9'd4    :   uart_data <=   { mpu_slot_sta1[0][7:0]  , mpu_slot_sta1[0][15:7] , enable_slot_feedback[0] } ;
            9'd5    :   uart_data <=   { mpu_slot_sta2[0][7:0]  , mpu_slot_sta2[0][15:8]  } ;
            9'd6    :   uart_data <=   { mpu_slot_sta1[1][7:0]  , mpu_slot_sta1[1][15:7] , enable_slot_feedback[1] } ;
            9'd7    :   uart_data <=   { mpu_slot_sta2[1][7:0]  , mpu_slot_sta2[1][15:8]  } ;
            9'd8    :   uart_data <=   { mpu_slot_sta1[2][7:0]  , mpu_slot_sta1[2][15:7] , enable_slot_feedback[2] } ;
            9'd9    :   uart_data <=   { mpu_slot_sta2[2][7:0]  , mpu_slot_sta2[2][15:8]  } ;
            9'd10   :   uart_data <=   { mpu_slot_sta1[3][7:0]  , mpu_slot_sta1[3][15:7] , enable_slot_feedback[3] } ;
            9'd11   :   uart_data <=   { mpu_slot_sta2[3][7:0]  , mpu_slot_sta2[3][15:8]  } ;
            9'd12   :   uart_data <=   { mpu_slot_sta1[4][7:0]  , mpu_slot_sta1[4][15:7] , enable_slot_feedback[4] } ;
            9'd13   :   uart_data <=   { mpu_slot_sta2[4][7:0]  , mpu_slot_sta2[4][15:8]  } ;
            9'd14   :   uart_data <=   { mpu_slot_sta1[5][7:0]  , mpu_slot_sta1[5][15:7] , enable_slot_feedback[5] } ;
            9'd15   :   uart_data <=   { mpu_slot_sta2[5][7:0]  , mpu_slot_sta2[5][15:8]  } ;
            9'd16   :   uart_data <=   { mpu_slot_sta1[6][7:0]  , mpu_slot_sta1[6][15:7] , enable_slot_feedback[6] } ;
            9'd17   :   uart_data <=   { mpu_slot_sta2[6][7:0]  , mpu_slot_sta2[6][15:8]  } ;
            9'd18   :   uart_data <=   { mpu_slot_sta1[7][7:0]  , mpu_slot_sta1[7][15:7] , enable_slot_feedback[7] } ;
            9'd19   :   uart_data <=   { mpu_slot_sta2[7][7:0]  , mpu_slot_sta2[7][15:8]  } ;
            9'd20   :   uart_data <=   { mpu_slot_sta1[8][7:0]  , mpu_slot_sta1[8][15:7] , enable_slot_feedback[8] } ;
            9'd21   :   uart_data <=   { mpu_slot_sta2[8][7:0]  , mpu_slot_sta2[8][15:8] } ;
            9'd22   :   uart_data <=   { mpu_slot_sta1[9][7:0]  , mpu_slot_sta1[9][15:7] , enable_slot_feedback[9] } ;
            9'd23   :   uart_data <=   { mpu_slot_sta2[9][7:0]  , mpu_slot_sta2[9][15:8] } ;
            9'd24   :   uart_data <=   { mpu_slot_sta1[10][7:0] , mpu_slot_sta1[10][15:7] , enable_slot_feedback[10] } ;
            9'd25   :   uart_data <=   { mpu_slot_sta2[10][7:0] , mpu_slot_sta2[10][15:8] } ;
            9'd26   :   uart_data <=   { mpu_slot_sta1[11][7:0] , mpu_slot_sta1[11][15:7] , enable_slot_feedback[11] } ;
            9'd27   :   uart_data <=   { mpu_slot_sta2[11][7:0] , mpu_slot_sta2[11][15:8] } ;
            9'd28   :   uart_data <=   { mpu_slot_sta1[12][7:0] , mpu_slot_sta1[12][15:7] , enable_slot_feedback[12] } ;
            9'd29   :   uart_data <=   { mpu_slot_sta2[12][7:0] , mpu_slot_sta2[12][15:8] } ;
            9'd30   :   uart_data <=   { mpu_slot_sta1[13][7:0] , mpu_slot_sta1[13][15:7] , enable_slot_feedback[13] } ;
            9'd31   :   uart_data <=   { mpu_slot_sta2[13][7:0] , mpu_slot_sta2[13][15:8] } ;
            default :   uart_data <=   16'h00 ; 
        endcase
    end
end



//----------------------------------------------------------------------------------
// external interface signal delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        slot_num_d1   <=   4'h00 ;
        slot_num_d2   <=   4'h00 ;
    end
    else begin
        slot_num_d1   <=   slot_num ;
        slot_num_d2   <=   slot_num_d1 ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        sta_num_d1   <=   8'h00 ;
        sta_num_d2   <=   8'h00 ;
    end
    else begin
        sta_num_d1   <=   sta_num ;
        sta_num_d2   <=   sta_num_d1 ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        box_num_d1   <=   3'h00 ;
        box_num_d2   <=   3'h00 ;
    end
    else begin
        box_num_d1   <=   box_num ;
        box_num_d2   <=   box_num_d1 ;
    end
end

assign  online_detect = { pmcu_oline , hmcu_oline , other_online } ;

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        online_detect_d1   <=   16'h00 ;
        online_detect_d2   <=   16'h00 ;
    end
    else begin
        online_detect_d1   <=   online_detect ;
        online_detect_d2   <=   online_detect_d1 ;
    end
end

//----------------------------------------------------------------------------------
// configuration feedback
//----------------------------------------------------------------------------------
assign  cfg_feedback = { mpu_cfg_wr_ok , sta_num_feedback , box_num_feedback , slot_num_feedback , 
                         version_feedback , hr_feedback , board_type_feedback , 1'b0 } ;
assign  hr_feedback =   1'b0 ;
assign  self_cfg_err =  | cfg_feedback[6:0] ; 

always @ ( posedge clk_150m ) begin
    emif_self_cfg_err      <=   self_cfg_err ; 
    hotr_self_cfg_err      <=   self_cfg_err ; 
    type1_self_cfg_err[0]  <=   self_cfg_err ; 
    type1_self_cfg_err[1]  <=   self_cfg_err ; 
    type1_self_cfg_err[2]  <=   self_cfg_err ; 
    type1_self_cfg_err[3]  <=   self_cfg_err ; 
    type2_self_cfg_err[0]  <=   self_cfg_err ; 
    type2_self_cfg_err[1]  <=   self_cfg_err ; 
    type2_self_cfg_err[2]  <=   self_cfg_err ; 
    type2_self_cfg_err[3]  <=   self_cfg_err ; 
    type2_self_cfg_err[4]  <=   self_cfg_err ; 
    type2_self_cfg_err[5]  <=   self_cfg_err ; 
    type2_self_cfg_err[6]  <=   self_cfg_err ; 
    type2_self_cfg_err[7]  <=   self_cfg_err ; 
    type2_self_cfg_err[8]  <=   self_cfg_err ; 
    type2_self_cfg_err[9]  <=   self_cfg_err ; 
end

always @ ( posedge clk_150m ) begin
    card_id_d1      <=  card_id ;
    code_version_d1 <=  code_version ;
    enable_slot_d1  <=  enable_slot ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        slot_num_feedback         <=   1'b0 ;
    end
    else begin
        if( feedback_check_point ) begin
            if( card_id_d1[3:0] == slot_num_d2 ) begin
                slot_num_feedback <=   1'b0 ;
            end
            else begin
                slot_num_feedback <=   1'b1 ;
            end
        end
        else
            slot_num_feedback     <=  slot_num_feedback;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sta_num_feedback    <=   1'b0 ;
    end
    else begin
        if( feedback_check_point ) begin
            if( card_id_d1[15:8] == sta_num_d2 ) begin
                sta_num_feedback    <=   1'b0 ;
            end
            else begin
                sta_num_feedback    <=   1'b1 ;
            end
        end // if( feedback_check_point )
        else
            sta_num_feedback        <=  sta_num_feedback;
    end
end
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        dst_sta_num    <=   1'b0 ;
    end
    else begin
        dst_sta_num   <=   sta_num_d2 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        box_num_feedback    <=   1'b0 ;
    end
    else begin
        if( feedback_check_point ) begin
            if( card_id_d1[7:5] == box_num_d2 ) begin
                box_num_feedback    <=   1'b0 ;
            end
            else begin
                box_num_feedback    <=   1'b1 ;
            end
        end // if( feedback_check_point )
        else
            box_num_feedback        <= box_num_feedback;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        board_type_feedback         <=   1'b0 ;
    end
    else begin
        if( feedback_check_point ) begin
            if( card_id_d1[22:18] == `MPU_TYPE ) begin
                board_type_feedback <=   1'b0 ;
            end
            else begin
                board_type_feedback <=   1'b1 ;
            end
        end // if( feedback_check_point )
        else
            board_type_feedback     <= board_type_feedback;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        version_feedback         <=   1'b0 ;
    end
    else begin
        if( feedback_check_point ) begin
            if( code_version_d1 == `CODE_VERSION ) begin
                version_feedback <=   1'b0 ;
            end
            else begin
                version_feedback <=   1'b1 ;
            end
        end // if( feedback_check_point )
        else
            version_feedback     <= version_feedback;
    end
end

//----------------------------------------------------------------------------------
// MPU case status
//----------------------------------------------------------------------------------
  genvar i ;
  generate
  for( i = 0 ; i < 14 ; i = i+1 ) 
  begin : Nsta

    MPU_STA                      #
    (
    .SLOT_NUM                   ( i + 2'd2                  )
    )
    U_MPU_STA
    (
    .clk_150m                   ( clk_150m                  ),
    .rst_150m                   ( rst_150m                  ),
    .rd_dval                    ( mpu_sta_rd_sel            ),
    .mpu_sta_dval               ( slot_sta_dval[i]          ),
    .mpu_sta_data               ( slot_sta_data[i]          ),
    .mpu_slot_sta1              ( mpu_slot_sta1[i]          ),
    .mpu_slot_sta2              ( mpu_slot_sta2[i]          )
    );

  end
  endgenerate

assign  slot_sta_dval[0]    =   slot2_sta_dval ;
assign  slot_sta_dval[1]    =   slot3_sta_dval ;
assign  slot_sta_dval[2]    =   slot4_sta_dval ;
assign  slot_sta_dval[3]    =   slot5_sta_dval ;
assign  slot_sta_dval[4]    =   slot6_sta_dval ;
assign  slot_sta_dval[5]    =   slot7_sta_dval ;
assign  slot_sta_dval[6]    =   slot8_sta_dval ;
assign  slot_sta_dval[7]    =   slot9_sta_dval ;
assign  slot_sta_dval[8]    =   slot10_sta_dval ;
assign  slot_sta_dval[9]    =   slot11_sta_dval ;
assign  slot_sta_dval[10]   =   slot12_sta_dval ;
assign  slot_sta_dval[11]   =   slot13_sta_dval ;
assign  slot_sta_dval[12]   =   slot14_sta_dval ;
assign  slot_sta_dval[13]   =   slot15_sta_dval ;

assign  slot_sta_data[0]    =   slot2_sta_data ;
assign  slot_sta_data[1]    =   slot3_sta_data ;
assign  slot_sta_data[2]    =   slot4_sta_data ;
assign  slot_sta_data[3]    =   slot5_sta_data ;
assign  slot_sta_data[4]    =   slot6_sta_data ;
assign  slot_sta_data[5]    =   slot7_sta_data ;
assign  slot_sta_data[6]    =   slot8_sta_data ;
assign  slot_sta_data[7]    =   slot9_sta_data ;
assign  slot_sta_data[8]    =   slot10_sta_data ;
assign  slot_sta_data[9]    =   slot11_sta_data ;
assign  slot_sta_data[10]   =   slot12_sta_data ;
assign  slot_sta_data[11]   =   slot13_sta_data ;
assign  slot_sta_data[12]   =   slot14_sta_data ;
assign  slot_sta_data[13]   =   slot15_sta_data ;

//----------------------------------------------------------------------------------
// slink diagnose
//----------------------------------------------------------------------------------
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        emif_err_d1    <=   1'b0 ;
    end
    else begin
        if ( mpu_sta_rd_sel == 1'b0 ) begin
            emif_err_d1    <=   emif_err ;
        end
    end
end

assign  chn_slink_err[15]   =   prm_slink_err ;   
assign  chn_slink_err[14]   =   hrm_slink_err ;   
assign  chn_slink_err[13]   =   type2_slink_err[9] ;   
assign  chn_slink_err[12]   =   type2_slink_err[8] ;   
assign  chn_slink_err[11]   =   type2_slink_err[7] ;   
assign  chn_slink_err[10]   =   type2_slink_err[6] ;   
assign  chn_slink_err[9]    =   type2_slink_err[5] ;   
assign  chn_slink_err[8]    =   type2_slink_err[4] ;   
assign  chn_slink_err[7]    =   type2_slink_err[3] ;   
assign  chn_slink_err[6]    =   type2_slink_err[2] ;   
assign  chn_slink_err[5]    =   type2_slink_err[1] ;   
assign  chn_slink_err[4]    =   type2_slink_err[0] ;   
assign  chn_slink_err[3]    =   type1_slink_err[3] ;   
assign  chn_slink_err[2]    =   type1_slink_err[2] ;   
assign  chn_slink_err[1]    =   type1_slink_err[1] ;   
assign  chn_slink_err[0]    =   type1_slink_err[0] ;   

//----------------------------------------------------------------------------------
// add by fmq 
//----------------------------------------------------------------------------------
reg [15:0]                      slot_sta_enable                     ;   
reg [31:0]                      dly_cnt_slot[0:15]                  ;
localparam  SLOT_DLY        =   32'd125000000                       ;

  genvar j ;
  generate
  for( j = 0 ; j < 16 ; j = j+1 ) 
  begin : Nslinkdiag
  

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        slot_sta_enable[j] <= 1'b0;
    end
    else begin
        if( online_detect_d2[j] == 1'b0 )
            slot_sta_enable[j] <= 1'b0;
        else begin
            if( slot_sta_dval[j] )
                slot_sta_enable[j] <= 1'b1;
            else
                ;
        end
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        dly_cnt_slot[j] <= 32'd0;
    end
    else begin
        if( slot_sta_enable[j] ) begin
            if( dly_cnt_slot[j] != SLOT_DLY )
                dly_cnt_slot[j] <= dly_cnt_slot[j] + 1;
            else
                ;
        end
        else
            dly_cnt_slot[j] <= 32'd0;
    end
end

        
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        enable_slot_feedback[j]    <=   1'b0 ;
    end
    else begin
        if ( mpu_sta_rd_sel == 1'b0 ) begin
            if ( enable_slot_d1[j] == ( online_detect_d2[j] &  ( dly_cnt_slot[j] == SLOT_DLY ) ) ) begin
            //if ( enable_slot_d1[j] == online_detect_delay[j] ) begin
                enable_slot_feedback[j]    <=   1'b0 ;
            end
            else begin
                enable_slot_feedback[j]    <=   1'b1 ;
            end
        end
    end
end

    SLINK_ERR_SYNC              U_SLINK_ERR_SYNC
    (
    .clk_sys                    ( clk_150m                  ),
    .rst_sys_n                  ( rst_150m                  ),

    .rd_dval                    ( mpu_sta_rd_sel            ),
    .chn_enable                 ( enable_slot_d1[j]         ),

    .chn_slink_err              ( chn_slink_err[j]          ),
    .slink_err                  ( slink_err[j]              )
    );

  end
  endgenerate

endmodule

