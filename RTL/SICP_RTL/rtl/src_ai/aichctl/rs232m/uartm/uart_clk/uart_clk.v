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
`define false 1'b 0
`define FALSE 1'b 0
`define true 1'b 1
`define TRUE 1'b 1


module UART_CLK
    (
        clk_sys                 ,   
        rst_sys_n               ,   
        baud_val                ,   
        baud_clock              ,   
        xmit_pulse                 
    ) ;

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   //  system clock
input   wire                    rst_sys_n                           ;   //  active low async reset
input   wire    [8:0]           baud_val                            ;   //  value loaded into cntr  

// declare output signal
output  wire                    baud_clock                          ;   //  16x baud clock pulse
output  wire                    xmit_pulse                          ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
// reg signal

reg     [12:0]                  baud_cntr                           ;   //  16x clock division counter reg.
reg                             baud_clock_int                      ;   //  internal 16x baud clock pulse
reg                             xmit_clock                          ;   
reg     [3:0]                   xmit_cntr                           ;   //  baud tx counter reg.
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

// ------------------------------------------------
//  Sync/Async Reset Mode
// ------------------------------------------------

always @( posedge clk_sys or negedge rst_sys_n ) 
begin : make_baud_cntr
    if ( rst_sys_n == 1'b0 ) begin
        baud_cntr <= 9'b000000000 ;
        baud_clock_int <= 1'b0 ;
    end
    else begin
        if ( baud_cntr == 9'b000000000 ) begin
            baud_cntr <= baud_val ;
            baud_clock_int <= 1'b1 ;
        end
        else begin
            baud_cntr <= baud_cntr - 1'b 1 ;
            baud_clock_int <= 1'b0 ;
        end
    end
end

// --------------------------------------------------
//  generate a transmit clock pulse
// --------------------------------------------------
always @( posedge clk_sys or negedge rst_sys_n )
begin : make_xmit_clock
    if ( rst_sys_n == 1'b0 ) begin
        xmit_cntr <= 4'b0000 ;
        xmit_clock <= 1'b0 ;
    end
    else begin
        if ( baud_clock_int === 1'b1 ) begin
            xmit_cntr <= xmit_cntr + 1'b1 ;
            if ( xmit_cntr === 4'b 1111 ) begin
                xmit_clock <= 1'b1 ;
            end
            else begin
                xmit_clock <= 1'b 0 ;
            end
        end
    end
end

assign xmit_pulse = xmit_clock & baud_clock_int ; 
assign baud_clock = baud_clock_int ; 

endmodule 

