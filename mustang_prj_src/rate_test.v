//**********************************************************
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
module ...
(
  /* clock and reset */
  input             clk                                  ,
  input             rst_n                               
  /* user port */
  input     wire    [  31:0]           ...               ,

  output    reg     [  31:0]           ...               ,


);

  /**********************************************************
  * Signal Declation
  **********************************************************/
  reg       [  31:0]                   ...               ;
  reg       [  31:0]                   ...               ;
  reg       [  31:0]                   ...               ;

  wire      [  31:0]                   ...               ;
  wire      [  31:0]                   ...               ;    
  wire      [  31:0]                   ...               ;

  /***********************************************************
  * Combinary logic declation
  ***********************************************************/
  assign
  assign
  /**********************************************************
  * Main Code
  **********************************************************/
  always @(posedge clk or negedge rst_n)begin
    if(!rst_n)begin
      cnt <= 0;
    end
    else if(add_cnt)begin
      if(end_cnt)
         cnt <= 0;
      else
         cnt <= cnt + 1;
    end
endmodule
  end
  assign add_cnt = 1;
  assign end_cnt = add_cnt && cnt == 50_000_000-1;



