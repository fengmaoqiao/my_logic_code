// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-12-12
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cgnpc.com.cn
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-12  Zhang Yongjun       Original
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
`timescale 1 ns / 1 ns
`include "DEFINES.v"

module JUG_LESSTHAN 
    (
        rst_sys_n               ,   
        clk_sys                 ,   
  
        chn_dgd_en              ,   
        jug_datastd0            ,   
        jug_data                ,   
        jug_result

    ) ;
    
/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input singal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   

input   wire                    chn_dgd_en                          ;   
input   wire    [15:0]          jug_data                            ;   
input   wire    [15:0]          jug_datastd0                        ;   
// output signal
output  reg                     jug_result                          ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
// reg signal             

/**********************************************************************************\
******************************** debug code ****************************************

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        jug_result <= 1'b0 ;
    end
    else begin
        if ( jug_data < jug_datastd0 && chn_dgd_en == 1'b1 ) begin
            jug_result <= 1'b1 ;
        end
        else begin
            jug_result <= 1'b0 ;
        end
    end
end

endmodule
