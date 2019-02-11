// *********************************************************************************
// Project Name :
// Author       : libing
// Email        : lb891004@163.com
// Creat Time   : 2014/2/19 13:12:31
// File Name    : uart_baud_gen.v
// Module Name  : uart_baud_gen
// Called By    : 
// Abstract     :
//
// CopyRight(c) 2014, Zhimingda digital equipment Co., Ltd.. 
// All Rights Reserved
//
// *********************************************************************************
// Modification History:
// 1. initial
// *********************************************************************************/
// *************************
// MODULE DEFINITION
// *************************
`timescale 1 ns / 1 ps

//H : 1          x  ref_clk   
//L : period_cnt x  ref_clk

module uart_debug_baud_gen(
//-----------------------------------------------------------------------------------
//Golbal System Signals
//-----------------------------------------------------------------------------------
    input               rst_n                   ,   // Reset, Active low 
    input               ref_clk                 ,   // Referrence clock
//-----------------------------------------------------------------------------------
//Other Signals
//-----------------------------------------------------------------------------------
    input [15:0]        period_cnt              ,   // Period parameter
    output reg          baud_out                    // Baud enable output
);

//***********************************************************************************
//Internal Register & Wire Define
//***********************************************************************************
reg [15:0]                      baud_cnt                            ;   
//***********************************************************************************
//Local Parameter Define
//***********************************************************************************
localparam        U_DLY     = 1;

//===================================================================================
//baud_cnt Counter
//===================================================================================
always @ (posedge ref_clk or negedge rst_n)
begin
    if (rst_n == 1'b0)
        baud_cnt <= #U_DLY 16'h0;
    else
        begin
            if (baud_cnt < period_cnt)
                baud_cnt <= #U_DLY baud_cnt + 1;
            else
                baud_cnt <= #U_DLY 16'h0; 
        end
end

//===================================================================================
//baud_out Generate
//===================================================================================
always @ (posedge ref_clk or negedge rst_n)
begin
    if (rst_n == 1'b0)
        baud_out <= #U_DLY 1'b0;
    else
        begin
            if (baud_cnt < period_cnt)
                baud_out <= #U_DLY 1'b0;
            else
                baud_out <= #U_DLY 1'b1;
        end
end

endmodule
