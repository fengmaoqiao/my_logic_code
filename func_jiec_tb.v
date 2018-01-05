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

`define clk_cycle 50
`include "funct.v"
module funct_tb(
     //clock and reset
     //user port
    
      );

//**********************************************************
//Signal Declation
//**********************************************************
reg [3:0] n;
reg reset,clk;

wire [31:0] result;
//**********************************************************
//Main Code
//**********************************************************
initial
begin
    n=0;reset=1;clk=0;
    for(n=0;n<=15;n=n+1)
#100
        n=n;
    end

initial $monitor($time,,,"n=%d result=%d",n,result);

always # `clk_cycle clk = ~clk;

funct funct_try
(
    .clk(clk),
    .n(n),
    .result(result),
    .reset(reset)
);

endmodule



