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
//用for语句实现2个8位数相乘,乘法转换为累加
//
//**********************************************************
`define size 8
module(
     //clock and reset
     input  [size:1]        a,b                                       ,
     output [2*size-1]      outcome                                   ,
     //user port

      );

//**********************************************************
//Signal Declation
//**********************************************************
reg
reg
reg

wire
wire
wire

integer i;
//**********************************************************
//Main Code
//**********************************************************


always @(a or b)
begin
    outcome = 0;
    for(i=1;i<=size;i=i+1)
    if(b[i])    
        outcome = outcome + (a << (i-1));       //b作为乘数，当b位数是1时，将a移位相加
    else

    end
endmodule



