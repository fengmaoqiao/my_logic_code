set casepath  "[pwd]"
set workplace "../..sim"

cd  $workpath

file  del -force  output
file  del -force  input
file  del -force  tb
file  del -force  $casepath/output
file  mkdir output

file  copy  -force  $casepath/input ./
file  copy  -force  $casepth/tb ./

exec  modelsim.exe  -do run_mc_all.do

file  copy  -force  output  $casepath
file  copy  -force  transcript  $casepath/transcript

exit
