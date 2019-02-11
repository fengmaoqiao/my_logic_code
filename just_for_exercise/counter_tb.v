module counter_tb;
reg irst = 0;
reg iclk = 0;
wire [3:0] ocnt;
initial begin
irst = 1; #100;
irst = 0; #300;
$stop;
#1000;
$finish;
end
always begin #5 iclk = !iclk; end
counter counter_test(
.irst(irst),
.iclk(iclk),
.ocnt(ocnt)
);
initial
$monitor("At time %t, ocnt = %d", $time, ocnt);
initial
begin
$dumpfile("counter_test.vcd");
$dumpvars(0, counter_test);
end
endmodule
