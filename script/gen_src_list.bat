mode con: cols=160  lines=50
title ZMD
color 0B

@echo off
cls

dir .\src_mc\*.v /b/s/a-b > filelist_tmp.txt

echo set fso  = createobject("scripting.filesystemobject") > a.vbs
echo set file = fso.opentextfile("filelist_tmp.txt") >> a.vbs 
echo s=file_readall >> a.vbs
echo s=replace(s,"\","/") >> a.vbs
echo set file=fso.opentextfile("src_mc.f") >> a.vbs
echo file.write s >> a.vbs
echo file.close >> a.vbs

.\a.vbs
del a.vbs filelist_tmp.txt

::pause
