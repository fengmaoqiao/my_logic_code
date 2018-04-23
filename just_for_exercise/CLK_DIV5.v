module CLK_DIV5(
  input   clk_i     ,
  input   rst_n     ,
  output  clk_o     
);

reg [2:0] cnt1,cnt2;
reg       clk_p,clk_n;

always  @(posedge clk_i ,negedge rst_n)
  if(!rst_n) begin
    cnt1  <= 3'b0;
    clk_p <= 1'b0;
  end
  else begin
    if(cnt1 == 3'b100)begin
      cnt1  <= 3'b0;
      clk_p <= 1'b0;
    end
    else begin
      cnt1  <= cnt1 + 1'b1;
      if(cnt == 3'b1 || cnt1 == 3'b11)
        clk_p <= ~clk_p;
    end
  end

always @ (negedge clk_i,negedge rst_n)
  if(!rst_n)begin
    cnt2  <= 3'b0;
    clk_n <= clk_n;
  end
  else begin
    if(cnt2 == 3'b100)begin
      cnt2  <= 3'b0;
      clk_n <= clk_n;
    end
    else begin
      cnt2  <= cnt2 + 1'b1;
      if(cnt2 == 3'b1 || cnt2 == 3'b11)
        clk_n <= ~clk_n;
    end
  end

  assign clk_o  = clk_p | clk_n;
endmodule
