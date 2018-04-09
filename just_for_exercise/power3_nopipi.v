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
module power3(
     //clock and reset
     input             clk                                 ,
     input             rst_n                               ,
     //user port
     output [7:0]      XPower                              ,
     output            finished                            ,
     input  [7:0]      X                                   ,
     input             clk,
     input             start
      );

//**********************************************************
//Signal Declation
//**********************************************************
reg     [7:0]   ncount;
reg     [7:0]   XPower;

assign finished = (ncount == 0);
//**********************************************************
//Main Code
//**********************************************************

always @(posedge clk)
  if(start)begin
    XPower  <= X;
    ncount  <= 2;
  end
  else if(!finished) begin
    ncount  <= ncount - 1;
    XPower  <= XPower * X;
  end

endmodule

module power3_pipe(
  output  reg [7:0] XPower,
  input             clk,
  input       [7:0] X
);

reg           [7:0] XPower1,XPower2;
reg           [7:0] X1,X2;

/* X3的最后计算和X下一数值的第一次计算X2二者同时进行 */
always @(posedge clk)
  if(!rst_n)begin
    /* Pipeline stage 1 */
    X1      <= X;
    XPower  <= X;
    /* Pipeline state 2 */
    X2      <= X1;
    XPower2 <= XPower1 * X1;
    /* Pipeline state 3 */
    XPower  <= XPower2 * X2;
end

