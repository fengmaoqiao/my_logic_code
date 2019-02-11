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

module ADREG
    (	
        clk_sys                 ,   // system clock
        rst_sys_n               ,   // system reset
       
        wr_cnt                  ,
        cur_state               ,   
        wr_trig                 ,   
        rd_trig                 ,   
        rw_len                  ,   
        wr_data
	) ;

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter  CON_CNT         =   5'd16          ;

localparam  CON_RDY         =   8'b00000001    ;
localparam  RD_RDY          =   8'b00100000    ;

localparam CMD_CLRHW    = 7'b1100000;
localparam CMD_RDHW     = 7'b1100100;
localparam CMD_RD       = 7'b0100100;
localparam CMD_WRHW     = 7'b1101000;
localparam CMD_WRMS     = 7'b1101001;
localparam CMD_WRLS     = 7'b1101010;
localparam CMD_SETHW    = 7'b1101100;

localparam DIV_ID_REG   = 9'b000000000;
localparam RST_PWR_REG  = 9'b000000100;
localparam SDI_CTL_REG  = 9'b000001000;
localparam SDO_CTL_REG  = 9'b000001100;
localparam DATOUT_REG   = 9'b000010000;
localparam RANG_SEL_REG = 9'b000010100;
localparam ALARM_REG    = 9'b000100000;
localparam ALARM_H_REG  = 9'b000100100;
localparam ALARM_L_REG  = 9'b000101000;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire    [7:0]           cur_state                           ;   
input   wire    [4:0]           wr_cnt                              ;   
// declare output signal
output  reg     [31:0]          wr_data                             ;   
output  reg                     wr_trig                             ;   
output  reg                     rd_trig                             ;   
output  reg     [5:0]           rw_len                              ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_trig   <=  1'b0 ;
    end
    else begin
        if ( cur_state == CON_RDY ) begin
            case ( wr_cnt )
                5'd0 , 5'd1, 5'd2, 5'd3, 5'd4, 5'd5, 5'd6, 5'd7 : begin
                    wr_trig <=   1'b1 ;
                end
                default : begin
                    wr_trig <=   1'b0 ;
                end
            endcase
        end
        else begin
            wr_trig <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_trig  <=  1'b0 ;
    end
    else begin
        if ( cur_state == RD_RDY && wr_cnt == CON_CNT ) begin
            rd_trig <=   1'b1 ;
        end
        else begin
            rd_trig <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rw_len   <=  6'd0 ;
    end
    else begin
        if ( cur_state == CON_RDY || cur_state == RD_RDY ) begin
            rw_len   <=  6'd32 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_data   <=  32'h000000 ;
    end
    else begin
        if ( cur_state == CON_RDY ) begin
            case ( wr_cnt )
                5'd0 : begin
                    wr_data <=   { CMD_WRHW,DIV_ID_REG,16'h0000 } ;
                end
                5'd1 : begin
                    wr_data   <=  { CMD_WRHW,DIV_ID_REG+9'h002,16'h0003 } ;
                end
                5'd2 : begin
                    wr_data   <=  { CMD_WRHW,RANG_SEL_REG,16'h0000 } ;
                end
                5'd3 : begin
                    wr_data   <=  { CMD_WRHW,RANG_SEL_REG+9'h002,16'h0000 } ;
                end
                5'd4 : begin
                    wr_data   <=  { CMD_WRHW,RANG_SEL_REG,16'h0000 } ;
                end
                5'd5 : begin
                    wr_data   <=  { CMD_WRHW,RANG_SEL_REG+9'h002,16'h0000 } ;
                end
                5'd6 : begin
                    wr_data   <=  { CMD_WRHW,DATOUT_REG,16'h0000 } ;
                end
                5'd7 : begin    
                    wr_data   <=  { CMD_WRHW,DATOUT_REG+9'h002,16'h0000 } ;
                end
                default : begin
                end
            endcase
        end
        else if ( cur_state == RD_RDY && wr_cnt == CON_CNT ) begin
            wr_data <=   32'h00000000 ;
        end
    end
end

endmodule
