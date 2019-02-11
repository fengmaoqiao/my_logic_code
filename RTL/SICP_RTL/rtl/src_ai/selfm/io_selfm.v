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

module  IO_SELFM
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m_n                 ,   

    clk_sys                     ,   
    rst_sys_n                   ,   
    // self hardware configurantion
    slot_num                    ,   

    // configurantion frame interface
    card_id                     ,   
    code_version                ,   
    cfg_done                    ,   
    cfg_enable_slot             ,   
    cfg_slink_chen              ,   
    com_fault                   ,   
    // slink diagnose flag
    slink_err                   , 
    cfg_req_fail                ,   

    // status frame interface 
    txsdu_sfm_rdreq             ,   
    sfm_txsdu_empty             ,   
    sfm_txsdu_dval              ,   
    sfm_txsdu_data              , 

    // status  
    self_cfg_err                ,   
    self_id_err                 ,   
    cfg_err_done                ,   
    slot_num_o                  ,   
    dw_com_fault
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   BOARD_TYPE  =   4'd0       ;

//localparam  SF_PERIOD   =   32'd375000 ; // 80ns * 125000 = 10ms
localparam  SF_PERIOD   =   32'd2000 ; // 80ns * 125000 = 10ms
localparam  DLY_US_CNT  =   5'd11      ; 
localparam  DLY_MS_CNT  =   10'd999    ; 
localparam  DLY_S_CNT   =   12'd1999   ; 
localparam  COM_STA_LEN =   16'd16     ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m_n                         ;   
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;

input   wire                    cfg_req_fail                        ;   
input   wire    [1:0]           com_fault                           ; 
input   wire    [3:0]           slot_num                            ;   
input   wire    [31:0]          card_id                             ;   
input   wire    [15:0]          code_version                        ;  
input   wire                    cfg_done                            ;   
input   wire    [1:0]           cfg_enable_slot                     ;   
input   wire    [1:0]           slink_err                           ;   
input   wire                    txsdu_sfm_rdreq                     ;   
input   wire    [1:0]           cfg_slink_chen                      ;   
// declare output signal
output  wire    [3:0]           slot_num_o                          ;   
output  reg                     sfm_txsdu_empty                     ;   
output  reg                     sfm_txsdu_dval                      ;   
output  reg     [17:0]          sfm_txsdu_data                      ;   
output  reg                     self_cfg_err                        ;   
output  reg                     cfg_err_done                        ;   
output  reg                     dw_com_fault                        ;   
output  reg                     self_id_err                         ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [1:0]               io_slink_err                        ;   
wire        [3:0]               self_status                         ;   

// reg signal
reg         [3:0]               slot_num_d1                         ;   
reg         [3:0]               slot_num_d2                         ;   
reg                             slot_num_feedback                   ;   
reg                             board_type_feedback                 ;   
reg                             version_feedback                    ;   
reg         [31:0]              sf_period_cnt                       ;  
reg         [4:0]               sfm_data_addr                       ; 
reg         [1:0]               slink_err_d1                        ;   
reg         [1:0]               slink_err_d2                        ;   
reg         [7:0]               cfg_feedback                        ; 
reg         [4:0]               dly_us                              ;   
reg         [9:0]               dly_ms                              ;   
reg         [11:0]              dly_s                               ;   
reg                             pow_up_en                           ;   
reg         [1:0]               com_fault_d1                        ;   
reg         [1:0]               com_fault_d2                        ;   
reg                             self_cfg_stus_d                     ;   
reg                             cfg_done_d                          ;   
reg                             cfg_done_d1                         ;   
reg                             self_cfg_stus                       ;   
reg         [4:0]               cfg_feedback_info                   ;   
reg         [3:0]               com_err                             ;   
reg                             cfg_req_fail_d1                     ;   
reg                             cfg_req_fail_d                      ;   
reg                             req_fail_en                         ;   


/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

assign  slot_num_o =   slot_num_d2 ;

//----------------------------------------------------------------------------------
// external interface signal delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        slot_num_d1   <=   4'h00 ;
        slot_num_d2   <=   4'h00 ;
    end
    else begin
        slot_num_d1   <=   slot_num ;
        slot_num_d2   <=   slot_num_d1 ;
    end
end


//----------------------------------------------------------------------------------
// processing asynchronous signal of cfg_done
//---------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        cfg_done_d  <=   1'b0 ;
    end
    else begin
        cfg_done_d  <=   cfg_done ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        cfg_done_d1  <=   1'b0 ;
    end
    else begin
        cfg_done_d1  <=   cfg_done_d ;
    end
end

//----------------------------------------------------------------------------------
// processing configuration feedback
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        slot_num_feedback    <=   1'b0 ;
    end
    else if ( card_id[3:0] == slot_num_d2 ) begin
        slot_num_feedback    <=   1'b0 ;
    end
    else begin
        slot_num_feedback    <=   1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        self_id_err <=   1'b0 ;
    end
    else begin
        self_id_err <= slot_num_feedback | version_feedback | board_type_feedback ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        board_type_feedback    <=   1'b0 ;
    end
    else if( card_id[21:18] == BOARD_TYPE ) begin
        board_type_feedback    <=   1'b0 ;
    end
    else begin
        board_type_feedback    <=   1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        version_feedback    <=   1'b0 ;
    end
    else if( code_version == `CODE_VERSION ) begin
        version_feedback    <=   1'b0 ;
    end
    else begin
        version_feedback    <=   1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        cfg_feedback_info    <=   5'd0 ;
    end
    else begin
        if ( cfg_done_d1 == 1'b1 ) begin
            cfg_feedback_info <= { slot_num_feedback, version_feedback, 1'b0, board_type_feedback, 1'b0 } ;
        end
        else begin
            cfg_feedback_info    <=   5'd0 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        cfg_feedback    <=   8'd0 ;
    end
    else begin
        cfg_feedback <= {  ~ cfg_done_d1 , 2'b00 ,cfg_feedback_info } ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        self_cfg_stus    <=   1'b0 ;
    end
    else begin
        self_cfg_stus    <=   | cfg_feedback_info ;
    end
end

//----------------------------------------------------------------------------------
// turn off slink error before cfg_done
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        com_err   <=   4'd0 ;
    end
    else begin
        if ( cfg_done_d1 == 1'b1 ) begin
            com_err   <=   { com_fault_d2, io_slink_err } ;
        end
        else begin
            com_err <=   4'd0 ;
        end
    end
end

//---------------------------------------------------------------------------------
// processing asynchronous signal of self_cfg_err
//---------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        self_cfg_stus_d  <=   1'b0 ;
    end
    else begin
        self_cfg_stus_d  <=   self_cfg_stus ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        self_cfg_err  <=   1'b0 ;
    end
    else begin
        self_cfg_err  <=   self_cfg_stus_d ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_err_done    <=   1'b0 ;
    end
    else begin
        cfg_err_done    <=  ~self_cfg_err && cfg_done ;
    end
end

//----------------------------------------------------------------------------------
// slink diagnose
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m ) begin
    slink_err_d1    <=   slink_err ;
    slink_err_d2    <=   slink_err_d1 ;
end

assign  io_slink_err[0]   =   cfg_enable_slot[0] == 1'b1 ? slink_err_d2[0] : 1'b0 ;   
assign  io_slink_err[1]   =   cfg_enable_slot[1] == 1'b1 ? slink_err_d2[1] : 1'b0 ;   
//----------------------------------------------------------------------------------
// status frame control
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        dly_us  <=   5'd0 ;
    end
    else begin
        if ( dly_us == DLY_US_CNT ) begin
            dly_us  <=   5'd0 ;
        end
        else begin
            dly_us  <=   dly_us + 1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        dly_ms  <=   10'd0 ;
    end
    else begin
        if ( dly_us == DLY_US_CNT ) begin
            if ( dly_ms == DLY_MS_CNT ) begin
                dly_ms  <=   10'd0 ;
            end
            else begin
                dly_ms  <=   dly_ms + 1'b1 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        dly_s  <=   12'd0 ;
    end
    else begin
        if ( dly_us == DLY_US_CNT && dly_ms == DLY_MS_CNT ) begin
            if ( dly_s == DLY_S_CNT ) begin
                dly_s  <=   DLY_S_CNT ;
            end
            else begin
                dly_s  <=   dly_s + 1'b1 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        pow_up_en   <=   1'b1 ;
    end
    else begin
        if ( dly_s == DLY_S_CNT ) begin
            pow_up_en   <=   1'b1 ;
        end
        else ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        cfg_req_fail_d    <=   1'b0 ;
    end
    else begin
        cfg_req_fail_d    <=   cfg_req_fail ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        cfg_req_fail_d1    <=   1'b0 ;
    end
    else begin
        cfg_req_fail_d1    <=   cfg_req_fail_d ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        req_fail_en <=   1'b0 ;
    end
    else begin
        if ( cfg_req_fail_d1 == 1'b1 && sf_period_cnt == SF_PERIOD-32'd15 ) begin
            req_fail_en <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        sf_period_cnt    <=   32'h00 ;
    end
    else begin
        if ( pow_up_en == 1'b1 && req_fail_en == 1'b0 ) begin
            if ( sf_period_cnt == SF_PERIOD  ) begin
                sf_period_cnt    <=   32'h00 ;
            end
            else begin
                sf_period_cnt    <=   sf_period_cnt + 1'b1 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        sfm_txsdu_empty    <=   1'b1 ;
    end
    else begin
        if ( sfm_txsdu_dval == 1'b1 && sfm_txsdu_data[16] == 1'b1 ) begin
            sfm_txsdu_empty    <=   1'b1 ;
        end
        else if ( sf_period_cnt == SF_PERIOD ) begin
            sfm_txsdu_empty    <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        sfm_txsdu_dval    <=   1'b0 ;
    end
    else begin
        if ( sfm_txsdu_dval == 1'b1 && sfm_txsdu_data[16] == 1'b1 ) begin
            sfm_txsdu_dval    <=   1'b0 ;
        end
        else if ( sfm_txsdu_empty == 1'b0 && txsdu_sfm_rdreq == 1'b1 ) begin
            sfm_txsdu_dval    <=   1'b1 ;
        end
        else begin
            sfm_txsdu_dval    <=   1'b0 ;
        end
    end
end

assign  self_status =   4'h0 ;

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        sfm_txsdu_data    <=   18'h00 ;
    end
    else begin
        if( txsdu_sfm_rdreq == 1'b1 ) begin
            case( sfm_data_addr )
                9'd0    :   sfm_txsdu_data <=   { 2'b10 , 4'b0000, 12'd0 } ; // DA Address
                9'd1    :   sfm_txsdu_data <=   { 2'b00 , 2'b00, 1'b1, 5'd0, 5'd0, 1'b1, 2'b00 } ; // DA Address && SA Address
                9'd2    :   sfm_txsdu_data <=   { 2'b00 , 10'd0, slot_num_d2, 2'b00 } ; // SA Address
                9'd3    :   sfm_txsdu_data <=   { 2'b00 , 16'd0 } ; // CYCLE
                9'd4    :   sfm_txsdu_data <=   { 2'b00 , `STA_TYPE } ;
                9'd5    :   sfm_txsdu_data <=   { 2'b00 , 16'h00 } ;
                9'd6    :   sfm_txsdu_data <=   { 2'b00 , COM_STA_LEN } ;
                9'd7    :   sfm_txsdu_data <=   { 2'b00 , cfg_feedback , self_status , 4'h0 } ;
                9'd8    :   sfm_txsdu_data <=   { 2'b00 , 12'h123 , com_err } ;
                9'd14   :   sfm_txsdu_data <=   { 2'b01 , 16'h00 } ;
                default :   sfm_txsdu_data <=   18'h00 ; 
            endcase
        end
        else begin
            sfm_txsdu_data    <=   18'h00 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        sfm_data_addr    <=   5'h00 ;
    end
    else begin
        if ( sfm_txsdu_dval == 1'b1 && sfm_txsdu_data[16] == 1'b1 ) begin
            sfm_data_addr    <=   5'h00 ;
        end
        else if ( txsdu_sfm_rdreq == 1'b1 ) begin
            sfm_data_addr    <=   sfm_data_addr + 1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        com_fault_d1    <=   2'b00 ;
    end
    else begin
        com_fault_d1    <=   com_fault ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        com_fault_d2    <=   2'b00 ;
    end
    else begin
        com_fault_d2    <=   com_fault_d1 ;
    end
end

//----------------------------------------------------------------------------------
// process the communication fault
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dw_com_fault    <=   1'b0 ;
    end
    else begin
        if ( cfg_done == 1'b1 ) begin
            if ( cfg_slink_chen == 2'b11 ) begin
                if ( slink_err == 2'b11 || com_fault != 2'b00 ) begin
                    dw_com_fault    <=   1'b1 ;
                end
                else begin
                    dw_com_fault    <=   1'b0 ;
                end
            end
            else if ( cfg_slink_chen == 2'b01 ) begin
                if ( slink_err[0] == 1'b1 || com_fault != 2'b00 ) begin
                    dw_com_fault    <=   1'b1 ;
                end
                else begin
                    dw_com_fault    <=   1'b0 ;
                end
            end
            else if ( cfg_slink_chen == 2'b10 ) begin
                if ( slink_err[1] == 1'b1 || com_fault != 2'b00  ) begin
                    dw_com_fault    <=   1'b1 ;
                end
                else begin
                    dw_com_fault    <=   1'b0 ;
                end
            end
            else ;
        end
        else begin
            dw_com_fault    <=   1'b0 ;
        end
    end
end

endmodule

