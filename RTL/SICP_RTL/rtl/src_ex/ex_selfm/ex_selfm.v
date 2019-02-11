// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SELFM
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
// PURPOSE          :   self management
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

module  EX_SELFM
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    // self hardware configurantion
    cfg_en                      ,   
    slot_num                    ,   
    sta_num                     ,   
    box_num                     ,  

    // configurantion frame interface
    card_id                     ,   
    code_version                ,   
    enable_slot                 ,   

    // slink diagnose flag
    ex0_slink_err               ,   
    ex1_slink_err               ,   
    fiber0_slink_err            ,   
    fiber1_slink_err            ,   
    slot2_slink_err             ,   
    slot3_slink_err             ,   
    slot4_slink_err             ,   
    slot5_slink_err             ,   
    slot6_slink_err             ,   
    slot7_slink_err             ,   
    slot8_slink_err             ,   
    slot9_slink_err             ,   
    slot10_slink_err            ,   
    slot11_slink_err            ,   
    slot12_slink_err            ,   
    slot13_slink_err            ,   
    slot14_slink_err            ,   
    slot15_slink_err            ,   

    // status frame interface
    ex_txsdu_rdreq              ,   
    txsdu_ex_dval               ,   
    txsdu_ex_data               ,   

    rxsdu_sfm_rdreq             ,   
    sfm_rxsdu_empty             ,   
    sfm_rxsdu_dval              ,   
    sfm_rxsdu_data              ,   

    // control signals 
    self_cfg_err                ,  
    led_slink_err               ,
    online                      
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   SF_PERIOD   =   32'd125000 ; // 80ns * 125000 = 10ms

parameter   EX_STA_LEN  =   16'd16 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   

input   wire    [3:0]           slot_num                            ;   
input   wire    [7:0]           sta_num                             ;   
input   wire    [2:0]           box_num                             ;   

input   wire    [31:0]          card_id                             ;   
input   wire    [15:0]          code_version                        ;   
input   wire    [16:0]          enable_slot                         ;   
input   wire                    cfg_en                              ;   

input   wire    [1:0]           ex0_slink_err                       ;   
input   wire    [1:0]           ex1_slink_err                       ;   
input   wire    [1:0]           fiber0_slink_err                    ;   
input   wire    [1:0]           fiber1_slink_err                    ;   
input   wire    [1:0]           slot2_slink_err                     ;   
input   wire    [1:0]           slot3_slink_err                     ;   
input   wire    [1:0]           slot4_slink_err                     ;   
input   wire    [1:0]           slot5_slink_err                     ;   
input   wire    [1:0]           slot6_slink_err                     ;   
input   wire    [1:0]           slot7_slink_err                     ;   
input   wire    [1:0]           slot8_slink_err                     ;   
input   wire    [1:0]           slot9_slink_err                     ;   
input   wire    [1:0]           slot10_slink_err                    ;   
input   wire    [1:0]           slot11_slink_err                    ;   
input   wire    [1:0]           slot12_slink_err                    ;   
input   wire    [1:0]           slot13_slink_err                    ;   
input   wire    [1:0]           slot14_slink_err                    ;   
input   wire    [1:0]           slot15_slink_err                    ;   

input   wire                    rxsdu_sfm_rdreq                     ; 
input   wire                    ex_txsdu_rdreq                      ;   
input   wire    [14:0]          online                              ;

// declare output signal
output  wire                    txsdu_ex_dval                       ;   
output  reg     [17:0]          txsdu_ex_data                       ;   
output  reg                     sfm_rxsdu_empty                     ;   
output  wire                    sfm_rxsdu_dval                      ;   
output  reg     [17:0]          sfm_rxsdu_data                      ;   
output  wire                    self_cfg_err                        ;   
output  reg     [17:0]          led_slink_err                       ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [16:0]              online_detect                       ; 
wire        [7:0]               cfg_feedback                        ;  

wire        [1:0]               chn_slink_err       [17:0]          ;   
wire        [17:0]              slink_err                           ;   
wire        [17:0]              chn_enable                          ;   
wire        [3:0]               self_status                         ; 
wire                            ex_sta_rden                         ;   

// reg signal
reg         [3:0]               slot_num_d1                         ;   
reg         [3:0]               slot_num_d2                         ;   
reg         [7:0]               sta_num_d1                          ;   
reg         [7:0]               sta_num_d2                          ;   
reg         [2:0]               box_num_d1                          ;   
reg         [2:0]               box_num_d2                          ;   
reg                             slot_num_feedback                   ;   
reg                             sta_num_feedback                    ;   
reg                             box_num_feedback                    ;   
reg                             board_type_feedback                 ;   
reg                             version_feedback                    ;   
reg         [31:0]              sf_period_cnt                       ;  
reg         [4:0]               sfm_data_addr                       ;   
reg         [31:0]              ex_period_cnt                       ;  
reg         [4:0]               ex_data_addr                        ;  
reg                             ex_rxsdu_empty                      ;  
reg                             sfm_rxsdu_dval_tmp                  ;  
reg                             txsdu_ex_dval_tmp                   ;  
reg         [15:0]              sta_tick                            ;
reg         [14:0]              online_d1                           ;   
reg         [14:0]              online_d2                           ;
            
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// external interface signal delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        slot_num_d1   <=   4'h0 ;
        slot_num_d2   <=   4'h0 ;
    end
    else begin
        slot_num_d1   <=   slot_num ;
        slot_num_d2   <=   slot_num_d1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sta_num_d1   <=   8'h00 ;
        sta_num_d2   <=   8'h00 ;
    end
    else begin
        sta_num_d1   <=   sta_num ;
        sta_num_d2   <=   sta_num_d1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        box_num_d1   <=   3'h00 ;
        box_num_d2   <=   3'h00 ;
    end
    else begin
        box_num_d1   <=   box_num ;
        box_num_d2   <=   box_num_d1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        online_d1   <=  15'b0;
        online_d2   <=  15'b0;
    end
    else begin
        online_d1   <=  online;
        online_d2   <=  online_d1;
    end
end

//----------------------------------------------------------------------------------
// configuration feedback
//----------------------------------------------------------------------------------
assign  cfg_feedback = { ~ cfg_en , sta_num_feedback , box_num_feedback , slot_num_feedback , 
                         version_feedback , 1'b0 , board_type_feedback , 1'b0 } ;

assign  self_cfg_err =  | cfg_feedback[6:1] ; 

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        slot_num_feedback    <=   1'b0 ;
    end
    else if( card_id[3:0] == slot_num_d2 ) begin
        slot_num_feedback    <=   1'b0 ;
    end
    else begin
        slot_num_feedback    <=   1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sta_num_feedback    <=   1'b0 ;
    end
    else if( card_id[15:8] == sta_num_d2 ) begin
        sta_num_feedback    <=   1'b0 ;
    end
    else begin
        sta_num_feedback    <=   1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        box_num_feedback    <=   1'b0 ;
    end
    else if( card_id[7:5] == box_num_d2 ) begin
        box_num_feedback    <=   1'b0 ;
    end
    else begin
        box_num_feedback    <=   1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        board_type_feedback    <=   1'b0 ;
    end
    else if( card_id[22:18] == `EX_TYPE ) begin
        board_type_feedback    <=   1'b0 ;
    end
    else begin
        board_type_feedback    <=   1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        version_feedback    <=   1'b0 ;
    end
    else if( code_version == `CODE_VERSION ) begin
        version_feedback    <=   1'b0 ;
    end
    else begin
        version_feedback    <=   1'b1 ;
    end
end

//----------------------------------------------------------------------------------
// status frame control
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sf_period_cnt    <=   32'h00 ;
    end
    else begin
        if ( sfm_rxsdu_empty == 1'b1 ) begin 
            if ( sf_period_cnt == SF_PERIOD ) begin
                sf_period_cnt    <=   32'h00 ;
            end
            else begin
                sf_period_cnt    <=   sf_period_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sfm_rxsdu_empty    <=   1'b1 ;
    end
    else begin
        if ( slot_num_d2[3:1] == 3'b000 ) begin
            if ( sfm_rxsdu_dval == 1'b1 && sfm_rxsdu_data[16] == 1'b1 ) begin
                sfm_rxsdu_empty    <=   1'b1 ;
            end
            else if ( sf_period_cnt == SF_PERIOD ) begin
                sfm_rxsdu_empty    <=   1'b0 ;
            end
        end
        else begin
            sfm_rxsdu_empty    <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sfm_rxsdu_dval_tmp    <=   1'b0 ;
    end
    else begin
        sfm_rxsdu_dval_tmp    <=   rxsdu_sfm_rdreq ;
    end
end

assign  sfm_rxsdu_dval  = ( sfm_rxsdu_dval_tmp == 1'b1 && sfm_rxsdu_empty == 1'b0 ) ? 1'b1 : 1'b0 ;

assign  self_status =   4'h0 ;

//----------------------------------------------------------------------------------
// rx from ex selfm to main controller
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sfm_rxsdu_data    <=   18'h00 ;
    end
    else begin
        if( rxsdu_sfm_rdreq == 1'b1 ) begin
            case( sfm_data_addr )
                9'd0    :   sfm_rxsdu_data <=   { 2'b10 , 4'b1000 , slot_num_d2 , 8'h00 } ;
                9'd1    :   sfm_rxsdu_data <=   { 2'b00 , `STA_TYPE } ;
                9'd2    :   sfm_rxsdu_data <=   { 2'b00 , 16'h00 } ;
                9'd3    :   sfm_rxsdu_data <=   { 2'b00 , EX_STA_LEN } ;
                9'd4    :   sfm_rxsdu_data <=   { 2'b00 , cfg_feedback , self_status , 2'b00 , slink_err[17:16] } ;
                //9'd5    :   sfm_rxsdu_data <=   { 2'b00 , slink_err[15:0] } ;
                9'd5    :   sfm_rxsdu_data <=   { 2'b00 , { 2'b00 } , ( ~online_d2[14:1] & enable_slot[13:0] ) } ;
                9'd11   :   sfm_rxsdu_data <=   { 2'b01 , { 2'b00 , ( ~online_d2[14:1] & enable_slot[13:0] ) } };  // FMQ modified. @2018/8/1 16:57:52
                default :   sfm_rxsdu_data <=   18'h00 ; 
            endcase
        end
        else begin
            sfm_rxsdu_data    <=   18'h00 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sfm_data_addr    <=   5'h00 ;
    end
    else begin
        if ( sfm_rxsdu_dval == 1'b1 && sfm_rxsdu_data[16] == 1'b1 ) begin
            sfm_data_addr    <=   5'h00 ;
        end
        else if ( rxsdu_sfm_rdreq == 1'b1 ) begin
            sfm_data_addr    <=   sfm_data_addr + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// 
//----------------------------------------------------------------------------------
assign ex_sta_rden = ( ex_rxsdu_empty == 1'b0 && ex_txsdu_rdreq == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        ex_period_cnt    <=   32'h00 ;
    end
    else begin
        if ( ex_rxsdu_empty == 1'b1 ) begin 
            if ( ex_period_cnt == SF_PERIOD ) begin
                ex_period_cnt    <=   32'h00 ;
            end
            else begin
                ex_period_cnt    <=   ex_period_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        ex_rxsdu_empty    <=   1'b1 ;
    end
    else begin
        if ( slot_num_d2[3:1] == 3'b000 ) begin
            if ( txsdu_ex_dval == 1'b1 && txsdu_ex_data[16] == 1'b1 ) begin
                ex_rxsdu_empty    <=   1'b1 ;
            end
            else if ( ex_period_cnt == SF_PERIOD ) begin
                ex_rxsdu_empty    <=   1'b0 ;
            end
        end
        else begin
            ex_rxsdu_empty    <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        txsdu_ex_dval_tmp    <=   1'b0 ;
    end
    else begin
        txsdu_ex_dval_tmp    <=   ex_sta_rden ;
    end
end

assign  txsdu_ex_dval  = ( txsdu_ex_dval_tmp == 1'b1 && ex_rxsdu_empty == 1'b0 ) ? 1'b1 : 1'b0 ;

//----------------------------------------------------------------------------------
// tx from main controller to io 
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        txsdu_ex_data    <=   18'h00 ;
    end
    else begin
        if( ex_sta_rden == 1'b1 ) begin
            case( ex_data_addr )
                9'd0    :   txsdu_ex_data <=   { 2'b10 , 4'b1000 , slot_num_d2 , 8'h00 } ;
                9'd1    :   txsdu_ex_data <=   { 2'b00 , `STA_TYPE } ;
                9'd2    :   txsdu_ex_data <=   { 2'b00 , sta_tick } ;
                9'd3    :   txsdu_ex_data <=   { 2'b00 , EX_STA_LEN } ;
                9'd4    :   txsdu_ex_data <=   { 2'b00 , cfg_feedback , self_status , 2'b00 , slink_err[17:16] } ;
                9'd5    :   txsdu_ex_data <=   { 2'b00 , slink_err[15:0] } ;
                9'd11   :   txsdu_ex_data <=   { 2'b01 , 16'h00 } ;
                default :   txsdu_ex_data <=   18'h00 ; 
            endcase
        end
        else begin
            txsdu_ex_data    <=   18'h00 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sta_tick <=   16'h00 ;           
    end
    else begin
        if( ex_period_cnt == SF_PERIOD ) begin
            sta_tick <=   sta_tick + 1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        ex_data_addr    <=   5'h00 ;
    end
    else begin
        if ( txsdu_ex_dval == 1'b1 && txsdu_ex_data[16] == 1'b1 ) begin
            ex_data_addr    <=   5'h00 ;
        end
        else if ( ex_sta_rden == 1'b1 ) begin
            ex_data_addr    <=   ex_data_addr + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// slink diagnose
//----------------------------------------------------------------------------------

assign  chn_slink_err[17]   =   ex1_slink_err ;   
assign  chn_slink_err[16]   =   ex0_slink_err ;   
assign  chn_slink_err[15]   =   fiber1_slink_err ;   
assign  chn_slink_err[14]   =   fiber0_slink_err ;   
assign  chn_slink_err[13]   =   slot15_slink_err ;   
assign  chn_slink_err[12]   =   slot14_slink_err ;   
assign  chn_slink_err[11]   =   slot13_slink_err ;   
assign  chn_slink_err[10]   =   slot12_slink_err ;   
assign  chn_slink_err[9]    =   slot11_slink_err ;   
assign  chn_slink_err[8]    =   slot10_slink_err ;   
assign  chn_slink_err[7]    =   slot9_slink_err ;   
assign  chn_slink_err[6]    =   slot8_slink_err ;   
assign  chn_slink_err[5]    =   slot7_slink_err ;   
assign  chn_slink_err[4]    =   slot6_slink_err ;   
assign  chn_slink_err[3]    =   slot5_slink_err ;   
assign  chn_slink_err[2]    =   slot4_slink_err ;   
assign  chn_slink_err[1]    =   slot3_slink_err ;   
assign  chn_slink_err[0]    =   slot2_slink_err ; 

assign  chn_enable  =   { enable_slot[16] , enable_slot } ;

  genvar j ;
  generate
  for( j = 0 ; j < 18 ; j = j+1 ) 
  begin : Nslinkdiag

    SELF_EX_SLINK_DIAG              U_SLINK_DIAG
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .chn_enable                 ( chn_enable[j]             ),

    .chn_slink_err              ( chn_slink_err[j]          ),
    .slink_err                  ( slink_err[j]              )
    );

  end
  endgenerate

always @ ( posedge clk_12_5m ) begin
    led_slink_err    <=   slink_err ;
end

endmodule

