vlib  work
vmap  work  work

vlog  +define+U_DLY=0.5 -timescale 1ns/100ps \
-f filelist.f -incr

vsim  -t  1ps \
-L  "D:/proj_data/libero118" \
work.TB

#run 50ms
run 70ms
quit -f
