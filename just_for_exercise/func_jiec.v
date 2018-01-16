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
module funct(
     //clock and reset
     input             clk                                 ,
     input             rst_n                               ,
     //user port
    output  [31:0]      result,
    input   [3:0]       n,
        
      );

//**********************************************************
//Signal Declation
//**********************************************************

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
         result <= 0;
     end
     else begin
         result <= 2 * factorial(n)
     end
end
endmodule

function [31:0] factorial;
    input   [3:0]  opa;
    reg     [3:0]  i;
    begin
        factorial = opa ? 1:0;
        for(i=2;i<=opa;i=i+1)
            factorial = i * factorial;
    end
endfunction
endmodule



