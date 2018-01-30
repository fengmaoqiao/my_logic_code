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
  input             clk                                 ,
  input             rst_n                               
  /* user port */

);

  /**********************************************************
  * Signal Declation
  **********************************************************/
  reg
  reg
  reg

  wire
  wire
  wire

  /***********************************************************
  * Combinary logic declation
  ***********************************************************/
  assign
  assign
  /**********************************************************
  * Main Code
  **********************************************************/


  /***********************************************************
  * 求log2(A)即求A除以2有多少次 
  ***********************************************************/
  function integer log2;
    input integer value;
    begin
      value = value - 1;
      for(log2=0;value>0;log2 = log2 + 1)
        value = value >> 1;
    end
  endfunction

endmodule



