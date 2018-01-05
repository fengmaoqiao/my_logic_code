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
// $Log:$模为60的BCD码加法计数器
//
//
//**********************************************************
module counter60(
      //clock and reset
      input             clk                                 ,
      input             rst_n                               ,

      input [7:0]       data                                ,
      input             load,
      input             cin,

      output    [7:0]   qout,
      output            cout
      //user port

      );

//**********************************************************
//Signal Declation
//**********************************************************
reg [7:0] qout
//**********************************************************
//Main Code
//**********************************************************
always @(posedge clk)begin
    if(!rst_n) == 1'b0)begin
        //同步复位
       qout <= 0;
       //同步置位
    else if(load)   qout    <=data;
    else if(cin)
    begin
        //低位是否是9
        if(qout[3:0] == 9)      
        begin
            //回0并判断高位是否是5
            qout[3:0]   <= 0;
            if(qout[7:4] == 5)
                qout[7:4]   <= 0;
            else
                //高位不为5，则加1
                qout[7:4]   <= qout[7:4] + 1;
            end
        else
            //低位不为9，则加1
            qout[3:0]   <= qout[3:0] + 1;
    end
end
assign cout = ((qout==8'h59)&cin)?1:0;
endmodule



