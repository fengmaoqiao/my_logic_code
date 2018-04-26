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
);

  /**********************************************************
  * Signal Declation
  **********************************************************/
  reg       [  2:0]                   reg_lfsr               ;

  /***********************************************************
  * Combinary logic declation
  ***********************************************************/
  localparam init_value = 3'b001;
  /**********************************************************
  * Main Code
  **********************************************************/
  
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
    begin
      reg_lfsr  <= init_value;
    end
    else begin
      reg_lfsr[2] <= reg_lfsr[1];
      reg_lfsr[1] <= reg_lfsr[0] ^ reg_lfsr[2];
      reg_lfsr[0] <= reg_lfsr[2];
    end
  end

  reg [15*8:0] str_state;
  always@(*)
  begin
    case(reg_lfsr)
      3'b001:str_state  = "S0";
      3'b010:str_state  = "S1";
      3'b100:str_state  = "S2";
      3'b011:str_state  = "S3";
      3'b110:str_state  = "S4";
      3'b111:str_state  = "S5";
      3'b101:str_state  = "S6";
      default:str_state = "S0";
    endcase
  end
endmodule
/***********************************************************
 * M序列产生器，F(x) = 1 + x + x3
 * M序列特征多项式要满足本原多项式要求
***********************************************************/
module m_sequence
(
  input               clk   ,
  input               rst_n ,
  output              out   ,
  output  reg [3:0]   shift ,

);

reg [3:0] rShift        ;
reg       rOut          ;

wire      feedback;

assign feedback = rShift[0] ^ rShift[3];
assign out      = rOut;
assign Shift    = rShift;

  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      rShift  <= 'b0110;
      rOut    <= 1'b0;
    end
    else begin
      rShift  <= {feedback,rShift[ 3:1 ]};
      rOut    <= rShift[0];
    end
  end

endmodule

module m_sequence_1(
  input           clk       ,
  input           rst_n     ,
  output          m_seq     
);

/* 特征多项式x^8+X^4+x^3+x^2+1  */
parameter POLY  = 8'b10001110;

reg [7:0]   shift_reg;


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      shift_reg <= 8'b11111111;
    end
    else begin
      shift_reg[7]  <=  (shift_reg[0] & POLY[7]) ^
                        (shift_reg[1] & POLY[6]) ^
                        (shift_reg[2] & POLY[5]) ^
                        (shift_reg[3] & POLY[4]) ^
                        (shift_reg[4] & POLY[3]) ^
                        (shift_reg[5] & POLY[2]) ^
                        (shift_reg[6] & POLY[1]) ^
                        (shift_reg[7] & POLY[0]);

      shift_reg[6:0]  <= shift_reg[7:1];
    end
  end
  assign m_seq  = shift_reg[0];
endmodule

