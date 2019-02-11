module counter(irst, iclk, ocnt );
input irst, iclk;
output reg [3:0] ocnt;
always @ (posedge iclk)
if(irst)
ocnt <= 4'b0000;
else
ocnt <= ocnt + 1'b1;
endmodule
