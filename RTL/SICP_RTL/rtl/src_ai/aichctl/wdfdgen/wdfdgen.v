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
`timescale 1 ns / 1 ps

module  WDFDGEN 
    (
        rst_sys_n               ,   
        clk_sys                 , 
        fd_trig                 ,   
        fd_en                   ,
        fd_fb                   ,   
        clc_en
    ) ;
    
/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam  TM_CNT_US       = 7'd124 ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input singal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    fd_trig                             ;  
input   wire                    fd_fb                               ;   
// output signal
output  reg                     fd_en                               ;
output  reg                     clc_en                              ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
// reg signal             
reg     [6:0]                   fd_dly_us                           ;   
reg     [6:0]                   dly_us                              ;   
reg     [18:0]                  dly_ms                              ;   
/**********************************************************************************\
******************************** debug code ****************************************

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// generate the signal of feeddog
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fd_en    <=   1'b0 ;
    end
    else begin
        if ( fd_trig == 1'b1 ) begin
            fd_en <=   1'b1 ;
        end
        else if ( fd_dly_us == TM_CNT_US ) begin
            fd_en <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fd_dly_us  <=   7'd0 ;
    end
    else begin
        if ( fd_en == 1'b1 ) begin
            fd_dly_us  <=   fd_dly_us + 1'b1 ;
        end
        else begin
            fd_dly_us  <=   7'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dly_us  <=   7'd0 ;
    end
    else begin
        if ( fd_fb == 1'b1 ) begin
            dly_us  <=   7'd0 ;
        end
        else if ( dly_us == TM_CNT_US ) begin
            dly_us  <=   7'd0 ;
        end
        else begin
            dly_us  <=   dly_us + 1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dly_ms  <=   19'd0 ;
    end
    else begin
        if ( fd_fb == 1'b1 ) begin
            dly_ms  <=   19'd0 ;
        end
        else if ( dly_us == TM_CNT_US ) begin
            if ( dly_ms[18] == 1'b1 ) begin
                dly_ms[18]  <=   1'b1 ;
            end
            else begin
                dly_ms  <=   dly_ms + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        clc_en  <=   1'b0 ;
    end
    else begin
        if ( dly_ms[18] == 1'b1 ) begin
            clc_en  <=   1'b1 ;
        end
        else begin
            clc_en  <=   1'b0 ;
        end
    end
end

endmodule
