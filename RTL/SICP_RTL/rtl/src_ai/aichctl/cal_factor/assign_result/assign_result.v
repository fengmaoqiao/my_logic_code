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
// V100     2017-07-25  YongjunZhang        Original
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

module ASSIGN_RESULT 
(
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        
        data_en                 ,   
        data_sel                ,   
        data_in                 ,   

        result0                 ,   
        result1                 ,   
        result2                 ,   
        result3                 ,   
        result4                 ,   
        result5                    
);

/**********************************************************************************\
***************************** declare parameter ************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input signal

input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   

input   wire                    data_en                             ;   
input   wire    [2:0]           data_sel                            ;   
input   wire    [31:0]          data_in                             ;   

// output signal
output  reg     [31:0]          result0                             ;   
output  reg     [31:0]          result1                             ;   
output  reg     [31:0]          result2                             ;   
output  reg     [31:0]          result3                             ;   
output  reg     [31:0]          result4                             ;   
output  reg     [31:0]          result5                             ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        result0  <=   32'h00000000 ;
    end
    else begin
        if ( data_en == 1'b1 && data_sel == 3'd0 ) begin
            result0 <=   data_in ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        result1  <=   32'h00000000 ;
    end
    else begin
        if ( data_en == 1'b1 && data_sel == 3'd1 ) begin
            result1 <=   data_in ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        result2  <=   32'h00000000 ;
    end
    else begin
        if ( data_en == 1'b1 && data_sel == 3'd2 ) begin
            result2 <=   data_in ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        result3  <=   32'h00000000 ;
    end
    else begin
        if ( data_en == 1'b1 && data_sel == 3'd3 ) begin
            result3 <=   data_in ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        result4  <=   32'h00000000 ;
    end
    else begin
        if ( data_en == 1'b1 && data_sel == 3'd4 ) begin
            result4 <=   data_in ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        result5  <=   32'h00000000 ;
    end
    else begin
        if ( data_en == 1'b1 && data_sel == 3'd5 ) begin
            result5 <=   data_in ;
        end
        else ;
    end
end

endmodule
