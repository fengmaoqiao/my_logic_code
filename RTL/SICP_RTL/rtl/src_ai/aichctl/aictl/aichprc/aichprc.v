// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-07-06
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-8  YongjunZhang        Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active low
// Clock Domains    :   EMIF_CLK
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"

module AICHPRC 
(
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        
        // input signal
        pw_on_en                ,   
        calf_dgd_mode           ,   
        cal_done                ,   
        cal_model_en            ,   

        adacq_spi_busy          ,   
        adacq_rd_dval           ,   
        adacq_rd_data0          ,   
        adacq_rd_data1          ,   
        adacq_rd_data2          ,   
        adacq_rd_data3          ,   
        adacq_rd_data4          ,   
        adacq_rd_data5          ,   

        calfas_adsb_sel         ,   
        calfas_data_a           ,   
        calfas_data_b           ,   
        calfas_start_trig       ,   
        calfd_data_a            ,   
        calfd_data_b            ,   
        calfd_start_trig        ,   
        calfm_data_a            ,   
        calfm_data_b            ,   
        calfm_start_trig        , 

        b_factor0               ,   
        b_factor1               ,   
        b_factor2               ,   
        b_factor3               ,   
        b_factor4               ,   
        b_factor5               ,

        kqe_factor0             ,   
        kqe_factor1             ,   
        kqe_factor2             ,   
        kqe_factor3             ,   
        kqe_factor4             ,   
        kqe_factor5             ,

        bq_coeff0               ,   
        bq_coeff1               ,   
        bq_coeff2               ,   
        bq_coeff3               ,   
        bq_coeff4               ,   
        bq_coeff5               ,   

        ke_coeff0               ,   
        ke_coeff1               ,   
        ke_coeff2               ,   
        ke_coeff3               ,   
        ke_coeff4               ,   
        ke_coeff5               ,   
        cfg_chn_enable          ,   

        // output signal
        ch_ad_diag              ,
        fas_done                ,   
        fas_result              ,   
        fd_done                 ,   
        fd_result               ,   
        fm_done                 ,   
        fm_result               , 

        state_cal_adde          ,   
        state_cal_addq          , 
        state_cal_dgdt          ,   
        state_cal_done          ,   
        acq_dgdad_en            ,   
        cal_chn_sel             ,   
        adacq_rd_en             ,
        cur_state               ,   
        prc_done_trig 
             
);

/**********************************************************************************\
***************************** declare parameter ************************************/
localparam      CAL_TM_MS       =   11'd2000  ;  // 1000  // 1ms = 100Mhz/100/1000   
localparam      CAL_TM_US       =   7'd124  ;     

localparam      IDLE            = 12'b000000000000 ;
localparam      PRC_RDY         = 12'b000000000001 ;
localparam      CHN_RDY         = 12'b000000000010 ;
localparam      CAL_INT_F       = 12'b000000000100 ;
localparam      CAL_MULK        = 12'b000000001000 ;
localparam      CAL_ADDE        = 12'b000000010000 ;
localparam      CAL_MULQ        = 12'b000000100000 ;
localparam      CAL_ADDQ        = 12'b000001000000 ;
localparam      DGD_TEST        = 12'b000010000000 ;
localparam      DLY_CNT         = 12'b000100000000 ;
localparam      CAL_NEXT        = 12'b001000000000 ;
localparam      PRC_DONE        = 12'b010000000000 ;


/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    pw_on_en                            ;   
input   wire    [5:0]           calf_dgd_mode                       ;   
input   wire    [5:0]           cfg_chn_enable                      ;   
input   wire                    cal_done                            ;   
input   wire                    cal_model_en                        ;   

input   wire    [5:0]           adacq_spi_busy                      ;   
input   wire    [5:0]           adacq_rd_dval                       ;   
input   wire    [15:0]          adacq_rd_data0                      ;   
input   wire    [15:0]          adacq_rd_data1                      ;   
input   wire    [15:0]          adacq_rd_data2                      ;   
input   wire    [15:0]          adacq_rd_data3                      ;   
input   wire    [15:0]          adacq_rd_data4                      ;   
input   wire    [15:0]          adacq_rd_data5                      ;   

input   wire                    calfas_adsb_sel                     ;   
input   wire    [31:0]          calfas_data_a                       ;   
input   wire    [31:0]          calfas_data_b                       ;   
input   wire                    calfas_start_trig                   ;   
input   wire    [31:0]          calfd_data_a                        ;   
input   wire    [31:0]          calfd_data_b                        ;   
input   wire                    calfd_start_trig                    ;
input   wire    [31:0]          calfm_data_a                        ;   
input   wire    [31:0]          calfm_data_b                        ;   
input   wire                    calfm_start_trig                    ;


input   wire    [31:0]          b_factor0                           ;   
input   wire    [31:0]          b_factor1                           ;   
input   wire    [31:0]          b_factor2                           ;   
input   wire    [31:0]          b_factor3                           ;   
input   wire    [31:0]          b_factor4                           ;   
input   wire    [31:0]          b_factor5                           ;     
 
input   wire    [31:0]          kqe_factor0                         ;   
input   wire    [31:0]          kqe_factor1                         ;   
input   wire    [31:0]          kqe_factor2                         ;   
input   wire    [31:0]          kqe_factor3                         ;   
input   wire    [31:0]          kqe_factor4                         ;   
input   wire    [31:0]          kqe_factor5                         ;    
 
input   wire    [31:0]          bq_coeff0                           ;   
input   wire    [31:0]          bq_coeff1                           ;   
input   wire    [31:0]          bq_coeff2                           ;   
input   wire    [31:0]          bq_coeff3                           ;   
input   wire    [31:0]          bq_coeff4                           ;   
input   wire    [31:0]          bq_coeff5                           ;   

input   wire    [31:0]          ke_coeff0                           ;   
input   wire    [31:0]          ke_coeff1                           ;   
input   wire    [31:0]          ke_coeff2                           ;   
input   wire    [31:0]          ke_coeff3                           ;   
input   wire    [31:0]          ke_coeff4                           ;   
input   wire    [31:0]          ke_coeff5                           ;   
// output signal
output  wire    [5:0]           acq_dgdad_en                        ;   
output  wire    [5:0]           adacq_rd_en                         ;   
output  wire    [5:0]           ch_ad_diag                          ;   
output  wire                    fas_done                            ;   
output  wire    [31:0]          fas_result                          ;   
output  wire                    fd_done                             ;   
output  wire    [31:0]          fd_result                           ;   
output  wire                    fm_done                             ;   
output  wire    [31:0]          fm_result                           ; 

output  wire                    state_cal_adde                      ;   
output  wire                    state_cal_addq                      ;   
output  wire                    state_cal_dgdt                      ;   
output  wire                    state_cal_done                      ;   

output  reg     [11:0]          cur_state                           ;   
output  reg     [2:0]           cal_chn_sel                         ;   
output  reg                     prc_done_trig                       ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [31:0]                  f_result                            ;   
wire                            f_done                              ;   

wire                            f_start_trig                        ;   
wire    [23:0]                  f_data_int                          ;   
wire    [31:0]                  fas_data_a                          ;   
wire    [31:0]                  fas_data_b                          ;   
wire                            fas_start_trig                      ;   
wire    [31:0]                  fm_data_a                           ;   
wire    [31:0]                  fm_data_b                           ;   
wire                            fm_start_trig                       ;   
wire    [31:0]                  fd_data_a                           ;   
wire    [31:0]                  fd_data_b                           ;   
wire                            fd_start_trig                       ; 

wire    [5:0]                   ad_acq_cpl                          ;
wire    [15:0]                  adacq_rd_data[5:0]                  ;
wire    [15:0]                  ch_ad_value[5:0]                    ; 
// reg signal
reg     [11:0]                  next_state                          ;   
reg     [15:0]                  prcf_data_int                       ;   
reg                             prcf_start_trig                     ; 
reg                             prcfas_adsb_sel                     ;   
reg     [31:0]                  prcfas_data_a                       ;   
reg     [31:0]                  prcfas_data_b                       ;   
reg                             prcfas_start_trig                   ;   
reg     [31:0]                  prcfm_data_a                        ;   
reg     [31:0]                  prcfm_data_b                        ;   
reg                             prcfm_start_trig                    ;   
reg     [6:0]                   tm_div_us                           ;   
reg     [10:0]                  cal_tm_cnt                          ;   
reg                             cal_trig                            ;   
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/
assign f_data_int       = ( cal_done == 1'b0 ) ? 16'h0000           : prcf_data_int     ;  
assign f_start_trig     = ( cal_done == 1'b0 ) ? 1'b0               : prcf_start_trig   ; 
assign fas_adsb_sel     = ( cal_done == 1'b0 ) ? calfas_adsb_sel    : prcfas_adsb_sel   ; 
assign fas_data_a       = ( cal_done == 1'b0 ) ? calfas_data_a      : prcfas_data_a     ;  
assign fas_data_b       = ( cal_done == 1'b0 ) ? calfas_data_b      : prcfas_data_b     ; 
assign fas_start_trig   = ( cal_done == 1'b0 ) ? calfas_start_trig  : prcfas_start_trig ;
assign fm_data_a        = ( cal_done == 1'b0 ) ? calfm_data_a       : prcfm_data_a      ;
assign fm_data_b        = ( cal_done == 1'b0 ) ? calfm_data_b       : prcfm_data_b      ; 
assign fm_start_trig    = ( cal_done == 1'b0 ) ? calfm_start_trig   : prcfm_start_trig  ; 
assign fd_data_a        = ( cal_done == 1'b0 ) ? calfd_data_a       : 32'h00000000      ; 
assign fd_data_b        = ( cal_done == 1'b0 ) ? calfd_data_b       : 32'h00000000      ; 
assign fd_start_trig    = ( cal_done == 1'b0 ) ? calfd_start_trig   : 1'b0              ;
//----------------------------------------------------------------------------------
// the us count 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tm_div_us  <=  7'd0 ;
    end
    else begin
        if ( tm_div_us == CAL_TM_US ) begin
            tm_div_us  <=  7'd0 ;
        end
        else begin
            tm_div_us  <=  tm_div_us + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// dianoge the time of diagnose acqiration
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_tm_cnt  <=  11'd0 ;
    end
    else begin
        if ( pw_on_en == 1'b1 && tm_div_us == CAL_TM_US ) begin
            if ( cal_tm_cnt == CAL_TM_MS ) begin
                cal_tm_cnt  <=  11'd0 ;
            end
            else begin
                cal_tm_cnt  <=  cal_tm_cnt + 1'b1 ;
            end
        end
        else begin
            cal_tm_cnt  <=  cal_tm_cnt ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_trig    <=   1'b0 ;
    end
    else begin
        if ( cal_tm_cnt == CAL_TM_MS && tm_div_us == CAL_TM_US ) begin
            cal_trig    <=   1'b1 ;
        end
        else begin
            cal_trig    <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// the ctrol state
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state  <=  IDLE ;
    end
    else begin
        cur_state  <=  next_state ;
    end
end

always @ ( * ) begin
    if( rst_sys_n == 1'b0 ) begin
        next_state = IDLE ;
    end
    else begin
        case (cur_state)
            IDLE : begin // 14'h00
                if ( pw_on_en == 1'b1 && cal_done == 1'b1 ) begin
                    next_state = PRC_RDY ;
                end
                else begin
                    next_state = IDLE ;
                end
            end
            PRC_RDY : begin
                if ( cal_trig == 1'b1 ) begin
                    if ( ad_acq_cpl[cal_chn_sel] == 1'b1 && cfg_chn_enable[cal_chn_sel] == 1'b1 ) begin
                        next_state = CHN_RDY ;
                    end
                    else begin
                        next_state = CAL_NEXT ;
                    end
                end
                else begin
                    next_state = PRC_RDY ;
                end
            end
            CHN_RDY : begin // h800
                next_state = CAL_INT_F ;
            end
            CAL_INT_F : begin // 1000
                if ( f_done == 1'b1 ) begin
                    next_state = CAL_MULK ;
                end
                else begin
                    next_state = CAL_INT_F ;
                end
            end
            CAL_MULK : begin // 2000
                if ( fm_done == 1'b1 ) begin
                    next_state = CAL_ADDE ;
                end
                else begin
                    next_state = CAL_MULK ;
                end
            end
            CAL_ADDE : begin // 4000
                if ( fas_done == 1'b1 ) begin
                    next_state = CAL_MULQ ;
                end
                else begin
                    next_state = CAL_ADDE ;
                end
            end
            CAL_MULQ : begin  // 10000
                if ( fm_done == 1'b1 ) begin
                    next_state = CAL_ADDQ ;
                end
                else begin
                    next_state = CAL_MULQ ;
                end
            end
            CAL_ADDQ : begin  // 20000
                if ( fas_done == 1'b1 ) begin
                    next_state = DGD_TEST ;
                end
                else begin
                    next_state = CAL_ADDQ ;
                end
            end
            DGD_TEST : begin
                next_state = DLY_CNT ;
            end
            DLY_CNT : begin
                next_state = CAL_NEXT ;
            end
            CAL_NEXT : begin // 40000
                if ( cal_chn_sel == 3'd5 ) begin
                    next_state =  PRC_DONE ;
                end
                else begin
                    next_state = CHN_RDY ;
                end
            end
            PRC_DONE : begin // 200000
                next_state = IDLE ;
            end
            default : begin
                next_state = IDLE;
            end
        endcase
    end
end

assign state_cal_dgdt = ( cur_state == DGD_TEST ) ? 1'b1 : 1'b0 ;
assign state_cal_adde = ( cur_state == CAL_ADDE ) ? 1'b1 : 1'b0 ;
assign state_cal_addq = ( cur_state == CAL_ADDQ ) ? 1'b1 : 1'b0 ; 
assign state_cal_done = ( cur_state == CAL_ADDQ ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_chn_sel <=   3'd0 ;
    end
    else begin
        if ( cur_state == IDLE ) begin
            cal_chn_sel <=   3'd0 ;
        end
        else if ( cur_state == CAL_NEXT ) begin
            if ( cal_chn_sel == 3'd5 ) begin
                cal_chn_sel <=   3'd0 ;
            end
            else begin
                cal_chn_sel <=   cal_chn_sel + 1'b1 ;
            end
        end
    end
end
  
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prcf_start_trig <=   1'b0 ;
    end
    else begin
        if ( cur_state == CHN_RDY ) begin
            prcf_start_trig <=   1'b1 ;
        end
        else begin
            prcf_start_trig <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prcf_data_int   <=   16'h0000 ;
    end
    else begin
        if ( cur_state == CHN_RDY ) begin
            if ( calf_dgd_mode[cal_chn_sel] == 1'b1 ) begin
                prcf_data_int <= 16'h1051;
            end
            else begin
                prcf_data_int <=  ch_ad_value[cal_chn_sel] ;
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// calculate the formate of k x adc and qkm = kqe x eml
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prcfm_start_trig <=   1'b0 ;
    end
    else begin
        if ( cur_state == CAL_INT_F && f_done == 1'b1 || cur_state == CAL_ADDE && fas_done == 1'b1 ) begin
            prcfm_start_trig <=   1'b1 ;
        end
        else begin
            prcfm_start_trig <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prcfm_data_a   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CAL_INT_F && f_done == 1'b1 ) begin
            prcfm_data_a   <=   f_result ;
        end
        else if ( cur_state == CAL_ADDE && fas_done == 1'b1 ) begin
            case ( cal_chn_sel )
                3'd0 : begin
                    if ( calf_dgd_mode[0] == 1'b1 ) begin
                        prcfm_data_a   <=   32'h40C80000 ;
                    end
                    else begin
                        prcfm_data_a   <=   kqe_factor0 ;
                    end
                end
                3'd1 : begin
                    if ( calf_dgd_mode[1] == 1'b1 ) begin
                        prcfm_data_a   <=   32'h40C80000 ;
                    end
                    else begin
                        prcfm_data_a   <=   kqe_factor1 ;
                    end
                end
                3'd2 : begin
                    if ( calf_dgd_mode[2] == 1'b1 ) begin
                        prcfm_data_a   <=   32'h40C80000 ;
                    end
                    else begin
                        prcfm_data_a   <=   kqe_factor2 ;
                    end
                end
                3'd3 : begin
                    if ( calf_dgd_mode[3] == 1'b1 ) begin
                        prcfm_data_a   <=   32'h40C80000 ;
                    end
                    else begin
                        prcfm_data_a   <=   kqe_factor3 ;
                    end
                end
                3'd4 : begin
                    if ( calf_dgd_mode[4] == 1'b1 ) begin
                        prcfm_data_a   <=   32'h40C80000 ;
                    end
                    else begin
                        prcfm_data_a   <=   kqe_factor4 ;
                    end
                end
                3'd5 : begin
                    if ( calf_dgd_mode[5] == 1'b1 ) begin
                        prcfm_data_a   <=   32'h40C80000 ;
                    end
                    else begin
                        prcfm_data_a   <=   kqe_factor5 ;
                    end
                end
                default : begin
                end
            endcase
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prcfm_data_b   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CAL_INT_F && f_done == 1'b1 ) begin
            case ( cal_chn_sel )
                3'd0 : begin
                    if ( calf_dgd_mode[0] == 1'b1 ) begin
                        prcfm_data_b   <=   32'h3b3c40bf ;
                    end
                    else begin
                        prcfm_data_b   <=   ke_coeff0 ;
                    end
                end
                3'd1 : begin
                    if ( calf_dgd_mode[1] == 1'b1 ) begin
                        prcfm_data_b   <=   32'h3b3c40bf ;
                    end
                    else begin
                        prcfm_data_b   <=   ke_coeff1 ;
                    end
                end
                3'd2 : begin
                    if ( calf_dgd_mode[2] == 1'b1 ) begin
                        prcfm_data_b   <=   32'h3b3c40bf ;
                    end
                    else begin
                        prcfm_data_b   <=   ke_coeff2 ;
                    end
                end
                3'd3 : begin
                    if ( calf_dgd_mode[3] == 1'b1 ) begin
                        prcfm_data_b   <=   32'h3b3c40bf ;
                    end
                    else begin
                        prcfm_data_b   <=   ke_coeff3 ;
                    end
                end
                3'd4 : begin
                    if ( calf_dgd_mode[4] == 1'b1 ) begin
                        prcfm_data_b   <=   32'h3b3c40bf ;
                    end
                    else begin
                        prcfm_data_b   <=   ke_coeff4 ;
                    end
                end
                3'd5 : begin
                    if ( calf_dgd_mode[5] == 1'b1 ) begin
                        prcfm_data_b   <=   32'h3b3c40bf ;
                    end
                    else begin
                        prcfm_data_b   <=   ke_coeff5 ;
                    end
                end
                default : begin
                end
            endcase
        end
        else if ( cur_state == CAL_ADDE && fas_done == 1'b1 ) begin
            prcfm_data_b   <=   fas_result ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prcfas_adsb_sel    <=   1'b0 ;
    end
    else begin
        prcfas_adsb_sel    <=   1'b1 ;
    end
end

//----------------------------------------------------------------------------------
// calculate the formate of k x adc + b
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prcfas_start_trig <=   1'b0 ;
    end
    else begin
        if ( (cur_state == CAL_MULK || cur_state == CAL_MULQ) && fm_done == 1'b1 ) begin
            prcfas_start_trig <=   1'b1 ;
        end
        else begin
            prcfas_start_trig <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prcfas_data_a   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CAL_MULK && fm_done == 1'b1 || cur_state == CAL_MULQ && fm_done == 1'b1 ) begin
            prcfas_data_a   <=   fm_result ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prcfas_data_b   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CAL_MULK && fm_done == 1'b1 ) begin
            case ( cal_chn_sel )
                3'd0 : begin
                    if ( calf_dgd_mode[0] == 1'b1 ) begin
                        prcfas_data_b   <=   32'h00000000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   b_factor0 ;
                    end
                end
                3'd1 : begin
                    if ( calf_dgd_mode[1] == 1'b1 ) begin
                        prcfas_data_b   <=   32'h00000000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   b_factor1 ;
                    end
                end
                3'd2 : begin
                    if ( calf_dgd_mode[2] == 1'b1 ) begin
                        prcfas_data_b   <=   32'h00000000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   b_factor2 ;
                    end
                end
                3'd3 : begin
                    if ( calf_dgd_mode[3] == 1'b1 ) begin
                        prcfas_data_b   <=   32'h00000000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   b_factor3 ;
                    end
                end
                3'd4 : begin
                    if ( calf_dgd_mode[4] == 1'b1 ) begin
                        prcfas_data_b   <=   32'h00000000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   b_factor4 ;
                    end                
                end
                3'd5 : begin
                    if ( calf_dgd_mode[5] == 1'b1 ) begin
                        prcfas_data_b   <=   32'h00000000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   b_factor5 ;
                    end
                end
            endcase
        end
        else if ( cur_state == CAL_MULQ && fm_done == 1'b1 ) begin
            case ( cal_chn_sel )
                3'd0 : begin
                    if (calf_dgd_mode[0] == 1'b1 ) begin
                        prcfas_data_b   <=   32'hC1C80000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   bq_coeff0 ;
                    end
                end
                3'd1 : begin
                   if (calf_dgd_mode[1] == 1'b1 ) begin
                        prcfas_data_b   <=   32'hC1C80000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   bq_coeff1 ;
                    end
                end
                3'd2 : begin
                    if (calf_dgd_mode[2] == 1'b1 ) begin
                        prcfas_data_b   <=   32'hC1C80000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   bq_coeff2 ;
                    end
                end
                3'd3 : begin
                    if (calf_dgd_mode[3] == 1'b1 ) begin
                        prcfas_data_b   <=   32'hC1C80000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   bq_coeff3 ;
                    end
                end
                3'd4 : begin
                    if (calf_dgd_mode[4] == 1'b1 ) begin
                        prcfas_data_b   <=   32'hC1C80000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   bq_coeff4 ;
                    end
                end
                3'd5 : begin
                    if (calf_dgd_mode[5] == 1'b1 ) begin
                        prcfas_data_b   <=   32'hC1C80000 ;
                    end    
                    else begin
                        prcfas_data_b   <=   bq_coeff5 ;
                    end
                end
            endcase
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        prc_done_trig   <=   1'b0 ;
    end
    else begin
        if ( cur_state == PRC_DONE ) begin
            prc_done_trig   <=   1'b1 ;
        end
        else begin
            prc_done_trig   <=   1'b0 ;
        end
    end
end

assign adacq_rd_data[0] = adacq_rd_data0 ;
assign adacq_rd_data[1] = adacq_rd_data1 ;
assign adacq_rd_data[2] = adacq_rd_data2 ;
assign adacq_rd_data[3] = adacq_rd_data3 ;
assign adacq_rd_data[4] = adacq_rd_data4 ;
assign adacq_rd_data[5] = adacq_rd_data5 ;

genvar i ;
generate
for ( i=0; i<6; i=i+1 )
begin : chadacq
    CHADACQ                     U_CHADACQ
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
        // input signal
    .pw_on_en                   ( pw_on_en                  ),
    .cal_model_en               ( cal_model_en              ),
    .cal_done                   ( cal_done                  ),
    .cfg_chn_enable             ( cfg_chn_enable[i]         ),
    .adacq_spi_busy             ( adacq_spi_busy[i]         ),
    .adacq_rd_dval              ( adacq_rd_dval[i]          ),
        
    .adacq_rd_data              ( adacq_rd_data[i]           ),
    .ch_ad_value                ( ch_ad_value[i]            ),
    .ch_ad_diag                 ( ch_ad_diag[i]             ),
    .adacq_rd_en                ( adacq_rd_en[i]            ),
    .acq_dgdad_en               ( acq_dgdad_en[i]           ),
    .ad_acq_cpl                 ( ad_acq_cpl[i]             )
    );
end
endgenerate

    FPAM                        U_FPAM
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .fas_adsb_sel               ( fas_adsb_sel              ),
    .fas_data_a                 ( fas_data_a                ),
    .fas_data_b                 ( fas_data_b                ),
    .fas_start_trig             ( fas_start_trig            ),
    .fm_data_a                  ( fm_data_a                 ),
    .fm_data_b                  ( fm_data_b                 ),
    .fm_start_trig              ( fm_start_trig             ),
    .fd_data_a                  ( fd_data_a                 ),
    .fd_data_b                  ( fd_data_b                 ),
    .fd_start_trig              ( fd_start_trig             ),
                     
    .f_start_trig               ( f_start_trig              ),
    .f_data_int                 ( f_data_int                ),
                     
    .fas_done                   ( fas_done                  ),
    .fas_result                 ( fas_result                ),
    .fm_done                    ( fm_done                   ),
    .fm_result                  ( fm_result                 ),
    .fd_done                    ( fd_done                   ),
    .fd_result                  ( fd_result                 ),
    .f_done                     ( f_done                    ),
    .f_result                   ( f_result                  )

    );

endmodule
