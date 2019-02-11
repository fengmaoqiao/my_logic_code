@echo off
set fn=DEFINES.v
for /f "tokens=*" %%i in ('dir/s/b/ad') do copy %fn% "%%i"