mode con: cols=160 lines=50
title ZMD Simulation. CopyRight(c) 2016, Zhimingda digital equipment Co., Ltd.. 
color 0B

@echo off
cls

dir .\src_ex\*.v /b /s /a-d >  filelist_tmp.txt

echo set fso = createobject("scripting.filesystemobject") > a.vbs
echo set file=fso.opentextfile("filelist_tmp.txt") >> a.vbs
echo s=file.readall >> a.vbs
echo s=replace(s,"\","/") >> a.vbs
echo set file=fso.createtextfile("src_ex.f") >> a.vbs
echo file.write s >> a.vbs
echo file.close >> a.vbs

:: --------------------------------------------------------------
:: RUN THE SCRIPT AND DELETE TMP FILE
:: --------------------------------------------------------------
.\a.vbs
del a.vbs filelist_tmp.txt

::pause

