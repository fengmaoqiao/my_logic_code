// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-09-10
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com.cn
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2018-02-24  Zhang Yongjun       Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active low
// Clock Domains    :   clk_100m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"

module CHLEDCTL 
    (
    // clock & reset
    clk_sys                     ,   
    rst_sys_n                   ,   

    cfg_err                     ,   
    cal_model_en                ,   
    cal_ch_index                ,   
    ch_run_stus                 ,   
    cfg_chn_enable              ,   
    ch_led                        
 
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire                    ch_run_stus                         ;   
input   wire                    cfg_chn_enable                      ;   
input   wire                    cal_model_en                        ;   
input   wire                    cal_ch_index                        ;   
input   wire                    cfg_err                             ;   
// declare output signal
output  reg    [1:0]            ch_led                              ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_led  <=   2'b00 ;
    end
    else begin
        if ( cfg_chn_enable == 1'b1 && cfg_err == 1'b0 ) begin
            if ( ch_run_stus == 1'b0 ) begin
                ch_led  <=   2'b10 ;
            end
            else begin
                ch_led  <=   2'b01 ;
            end
        end
        else if ( cal_model_en == 1'b1 ) begin
            if ( cal_ch_index == 1'b1 ) begin
                ch_led  <=   2'b10 ;
            end
            else begin
                ch_led  <=   2'b01 ;
            end
        end
        else begin
            ch_led  <=   2'b00 ;
        end
    end
end

endmodule


