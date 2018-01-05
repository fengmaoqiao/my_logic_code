//**********************************************************
//
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
//
// ProjectName :
// target      :
// FileName    : 
// Author      :fengmaoqiao 
// E_mail      :fengmaoqiao@outwitcom.com 
// Date        :
// Version     :
//
// Modification history
//--------------------------------------------------------
// $Log:$
//
//
//**********************************************************
module(
    //clock and reset
    input             clk                                 ,
    input             rst_n                               ,
    //user port
    input               s_axis_tready,
    output              s_axis_tvalid,
    output  [63:0]      s_axis_tdata,
    output  [7:0]       s_axis_tkeep,
    output              s_axis_tlast,

    output              m_axis_tvalid,
    output              m_axis_tlast,
    output  [7:0]       m_axis_tdata,
    output              m_axis_tkeep,
    input               m_axis_tready

      );

//**********************************************************
//Signal Declation
//**********************************************************
reg [63:0]  pipe_datareg0;
reg [63:0]  pipe_datareg1;
reg [63:0]  pipe_datareg2;
reg [63:0]  pipe_datareg3;
reg [63:0]  pipe_datareg4;
reg [63:0]  pipe_datareg5;
reg
reg

wire
wire
wire
//**********************************************************
//Main Code
//**********************************************************

always @(posedge clk or negedge rst_n)begin
     if(!rst_n) == 1'b0)begin
     end
     else begin
     end
end


endmodule



