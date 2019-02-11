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
module  FLOAT_CMPLT
    (
        rst_sys_n               ,   
        clk_sys                 ,   

        f_data_a                ,   
        f_data_b                ,   
        cmp_lt_en 
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input signal
input                           rst_sys_n                           ;   
input                           clk_sys                             ;   
input   wire    [31:0]          f_data_a                            ;   
input   wire    [31:0]          f_data_b                            ;   

// output signal
output  reg                     cmp_lt_en                          ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/


/**********************************************************************************\
******************************** debug code ****************************************

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// compare f_data_a less than f_data_b
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cmp_lt_en  <=   1'b0 ;
    end
    else begin
        if ( f_data_a[31] == f_data_b[31] && f_data_b[31] == 1'b0 ) begin
            if ( f_data_b[30:23] < f_data_a[30:23] ) begin
                cmp_lt_en  <=   1'b1 ;
            end
            else if ( f_data_b[30:23] == f_data_a[30:23] ) begin
                if ( f_data_b[22:0] < f_data_a[22:0] ) begin
                    cmp_lt_en  <=   1'b1 ;
                end
                else begin
                    cmp_lt_en  <=   1'b0 ;
                end
            end
            else begin
                cmp_lt_en  <=   1'b0 ;
            end
        end
        else if ( f_data_a[31] == f_data_b[31] && f_data_b[31] == 1'b1 ) begin
            if ( f_data_b[30:23] > f_data_a[30:23] ) begin
                cmp_lt_en  <=   1'b1 ;
            end
            else if ( f_data_b[30:23] == f_data_a[30:23] ) begin
                if ( f_data_b[22:0] > f_data_a[22:0] ) begin
                    cmp_lt_en  <=   1'b1 ;
                end
                else begin
                    cmp_lt_en  <=   1'b0 ;
                end
            end
            else begin
                cmp_lt_en  <=   1'b0 ;
            end
        end
        else if ( f_data_a[31] == 1'b0 && f_data_b[31] == 1'b1 ) begin
            cmp_lt_en  <=   1'b1 ;
        end
        else begin
            cmp_lt_en  <=   1'b0 ;
        end
    end
end

endmodule
