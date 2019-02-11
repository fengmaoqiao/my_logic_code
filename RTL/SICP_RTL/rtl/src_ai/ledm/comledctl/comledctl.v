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
// V100     2017-09-10  Zhang Yongjun       Original
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

module COMLEDCTL 
    (
    // clock & reset
    clk_sys                     ,   
    rst_sys_n                   ,   

    self_cfg_err                ,   
    clk_ms_en                   , // the enable of millisecond clock 
    cfg_err                     ,   
    slot_en                     ,   
    com_trig                    , // the trig signal of one communication  
    com_led                       // the led out of communication indicate 
 
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
input   wire                    clk_ms_en                           ;   
input   wire   [1:0]            com_trig                            ; // [1]: data_eop_flag , [0] err
input   wire                    slot_en                             ; 
input   wire                    cfg_err                             ;  
input   wire                    self_cfg_err                        ;   
// declare output signal
output  reg    [1:0]            com_led                             ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// reg signal
reg     [4:0]                   com_cnt                             ;   
reg                             err_d1                              ;   
reg                             err_d2                              ;   
reg                             err_d3                              ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// counting the signal of com_trig 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        com_cnt <=   5'd0;
    end
    else begin
        if( clk_ms_en == 1'b1 ) begin
            com_cnt <=   5'd0 ;
        end
        else if ( com_trig[1] == 1'b1 ) begin
            com_cnt <=   com_cnt + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// the green led flash light in normal communication
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        com_led[0] <=   1'b0 ;
    end
    else begin
        if ( slot_en == 1'b1 && err_d3 == 1'b0 && self_cfg_err == 1'b0 ) begin
            if ( clk_ms_en == 1'b1 ) begin
                if ( com_cnt != 5'd0 ) begin
                    com_led[0]  <=   ~ com_led[0] ;
                end
                else begin
                    com_led[0]  <=   1'b0 ;
                end
            end
            else ;
        end
        else begin
            com_led[0] <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// the red led indicator communication error
//----------------------------------------------------------------------------------

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        err_d1 <=   1'b0 ;
        err_d2 <=   1'b0 ;
        err_d3 <=   1'b0 ;
    end
    else begin
        err_d1 <=   com_trig[0] ;
        err_d2 <=   err_d1 ;
        err_d3 <=   err_d2 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        com_led[1] <=   1'b0;
    end
    else begin
        if ( self_cfg_err == 1'b1 ) begin
            com_led[1]  <=   1'b0 ;
        end
        else if ( err_d3 == 1'b1 && slot_en == 1'b1 ) begin
            com_led[1]  <=   1'b1 ;
        end
        else begin
            com_led[1]  <=   1'b0 ;
        end
    end
end

endmodule


