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

module REDUDIAG 
(
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        
        test_rdu_en             ,   
        cal_chn_en              ,   
        fas_done0               ,   
        fas_result0             ,   
        cur_state0              ,   
        state_cal_adde0         ,   
        state_cal_addq0         ,   
        fas_done1               ,   
        fas_result1             ,   
        cur_state1              ,   
        state_cal_adde1         ,   
        state_cal_addq1         ,   
        state_cal_dgdt          ,   
        state_cal_done          ,   
        
        calf_dgd_mode           ,   
        rcy_sel                 ,   
        ch_rdu_fault            ,   
        ch_hw_fault
);

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/


/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   

input   wire                    test_rdu_en                         ;   
input   wire                    fas_done0                           ;   
input   wire    [31:0]          fas_result0                         ;   
input   wire    [11:0]          cur_state0                          ;   
input   wire                    state_cal_adde0                     ;   
input   wire                    state_cal_addq0                     ;   
input   wire                    fas_done1                           ;   
input   wire    [31:0]          fas_result1                         ;   
input   wire    [11:0]          cur_state1                          ;   
input   wire                    state_cal_adde1                     ;   
input   wire                    state_cal_addq1                     ;   
input   wire                    state_cal_done                      ;   
input   wire                    state_cal_dgdt                      ;   
input   wire                    cal_chn_en                          ;   
// output signal
output  reg                     calf_dgd_mode                       ;   
output  reg                     rcy_sel                             ;   
output  reg                     ch_hw_fault                         ;   
output  reg                     ch_rdu_fault                        ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [31:0]                  elec_dgd_test                       ;   
wire    [31:0]                  engn_dgd_test                       ;    
// reg signal
reg                             calf_dgd_en                         ;   
reg                             dgd_engn_err0                       ;   
reg                             dgd_engn_err1                       ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
wire    [31:0]                  test_result                         ;   

/**********************************************************************************\
********************************* main code ****************************************/
assign elec_dgd_test    = 32'h413ff9c7 ;
assign engn_dgd_test    = 32'h4247f646 ;

assign test_result = ( test_rdu_en == 1'b1 ) ? 32'd0 : fas_result0 ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calf_dgd_en <=   1'b0 ;
    end
    else begin
        if ( cal_chn_en == 1'b1 ) begin
            if ( calf_dgd_mode  ==   1'b1 && state_cal_done == 1'b1 ) begin
                calf_dgd_en <=   1'b1 ;
            end
            else if ( calf_dgd_en == 1'b1 && state_cal_done == 1'b1 ) begin
                calf_dgd_en <=   1'b0 ;
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// redundant channel diagnosis
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calf_dgd_mode   <=   1'b0 ;
    end
    else begin
        if ( cal_chn_en == 1'b1 ) begin
            if ( dgd_engn_err0 == 1'b0 && ch_rdu_fault == 1'b0 && cur_state0 == cur_state1 && fas_done0 == 1'b1 && test_result != fas_result1 && state_cal_addq0 == 1'b1 ) begin
                calf_dgd_mode  <=   1'b1 ; 
            end
            else if ( calf_dgd_en == 1'b1 && state_cal_dgdt == 1'b1 ) begin 
                calf_dgd_mode  <=   1'b0 ;
            end
        end
        else ; 
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dgd_engn_err0    <=   1'b0 ;
    end
    else begin
        if ( cal_chn_en == 1'b1 ) begin
            if ( state_cal_addq0 == 1'b1 && fas_done0 == 1'b1 && calf_dgd_mode == 1'b1 ) begin
                if ( test_result != engn_dgd_test ) begin
                    dgd_engn_err0   <=   1'b1 ;
                end
                else begin
                    dgd_engn_err0   <=   1'b0 ;
                end
            end 
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dgd_engn_err1    <=   1'b0 ;
    end
    else begin
        if ( cal_chn_en == 1'b1 ) begin
            if ( state_cal_addq1 == 1'b1 && fas_done1 == 1'b1 && calf_dgd_mode == 1'b1 ) begin
                if ( fas_result1 != engn_dgd_test ) begin
                    dgd_engn_err1   <=   1'b1 ;
                end
                else begin
                    dgd_engn_err1   <=   1'b0 ;
                end
            end 
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rcy_sel <=   1'b1 ;
    end
    else begin
        if ( cal_chn_en == 1'b1 ) begin
            if ( state_cal_dgdt == 1'b1 ) begin
                if ( dgd_engn_err0 == 1'b0 ) begin
                    rcy_sel <=   1'b1 ;
                end
                else if ( dgd_engn_err1 == 1'b0 ) begin
                    rcy_sel <=   1'b0 ;
                end
    
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_hw_fault    <=   1'b0 ;
    end
    else begin
        if ( cal_chn_en == 1'b1 ) begin
            if ( state_cal_dgdt == 1'b1 ) begin
                if ( dgd_engn_err0 == 1'b1 && dgd_engn_err1 == 1'b1 ) begin
                    ch_hw_fault <=   1'b1 ;
                end
                else begin
                    ch_hw_fault <=   1'b0 ;
                end
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_rdu_fault    <=   1'b0 ;
    end
    else begin
        if ( cal_chn_en == 1'b1 ) begin
            if ( state_cal_dgdt == 1'b1 ) begin
                if ( dgd_engn_err0 == 1'b1 || dgd_engn_err1 == 1'b1 ) begin
                    ch_rdu_fault <=   1'b1 ;
                end
                else begin
                    ch_rdu_fault <=   1'b0 ;
                end
            end
            else ;
        end
        else ;
    end
end

endmodule
