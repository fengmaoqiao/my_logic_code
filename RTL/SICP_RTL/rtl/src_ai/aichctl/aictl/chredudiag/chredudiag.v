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

module CHREDUDIAG 
(
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        
        cal_chn_sel             ,   
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

input   wire    [2:0]           cal_chn_sel                         ;   
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
// output signal
output  wire    [5:0]           calf_dgd_mode                       ;   
output  wire    [5:0]           rcy_sel                             ;   
output  wire    [5:0]           ch_rdu_fault                        ;   
output  wire    [5:0]           ch_hw_fault                         ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [31:0]                  elec_dgd_test                       ;   
wire    [31:0]                  engn_dgd_test                       ;    
// reg signal
reg     [5:0]                   calf_dgd_en                         ;   
reg     [5:0]                   dgd_engn_err0                       ;   
reg     [5:0]                   dgd_engn_err1                       ;   
reg     [5:0]                   cal_chn_en                          ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
wire    [5:0]                       test_rdu_en;

/**********************************************************************************\
********************************* main code ****************************************/

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_chn_en  <=   6'b000000 ;
    end
    else begin
        case ( cal_chn_sel )
            3'd0 : begin
                cal_chn_en  <=   6'b000001 ;
            end
            3'd1 : begin
                cal_chn_en  <=   6'b000010 ;
            end
            3'd2 : begin
                cal_chn_en  <=   6'b000100 ;
            end
            3'd3 : begin
                cal_chn_en  <=   6'b001000 ;
            end
            3'd4 : begin
                cal_chn_en  <=   6'b010000 ;
            end
            3'd5 : begin
                cal_chn_en  <=   6'b100000 ;
            end
            default :begin
                cal_chn_en  <=   6'b000000 ;
            end
        endcase
    end
end

assign test_rdu_en = 6'b000000 ;

genvar i ;
generate 
for ( i=0 ;i <6 ;i = i + 1 )
begin : rdudiag
    REDUDIAG  U_REDUDIAG
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    .test_rdu_en                ( test_rdu_en[i]            ),
    .cal_chn_en                 ( cal_chn_en[i]             ),
    .fas_done0                  ( fas_done0                 ),
    .fas_result0                ( fas_result0               ),
    .cur_state0                 ( cur_state0                ),
    .state_cal_adde0            ( state_cal_adde0           ),
    .state_cal_addq0            ( state_cal_addq0           ),
    .fas_done1                  ( fas_done1                 ),
    .fas_result1                ( fas_result1               ),
    .cur_state1                 ( cur_state1                ),
    .state_cal_adde1            ( state_cal_adde1           ),
    .state_cal_addq1            ( state_cal_addq1           ),
    .state_cal_dgdt             ( state_cal_dgdt            ),
    .state_cal_done             ( state_cal_done            ),
        
    .calf_dgd_mode              ( calf_dgd_mode[i]          ),
    .rcy_sel                    ( rcy_sel[i]                ),
    .ch_hw_fault                ( ch_hw_fault[i]            ),
    .ch_rdu_fault               ( ch_rdu_fault[i]           )
    );
end
endgenerate

endmodule
