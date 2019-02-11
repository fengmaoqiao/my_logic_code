iverilog -o counter_test counter_tb.v counter.v
vvp -n counter_test -lxt2
cp counter_test.vcd counter_test.lxt
gtkwave counter_test.lxt
