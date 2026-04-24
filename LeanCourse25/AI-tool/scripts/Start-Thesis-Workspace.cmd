@echo off
setlocal
"%SystemRoot%\System32\WindowsPowerShell\v1.0\powershell.exe" -ExecutionPolicy Bypass -File "%~dp0Start-Thesis-Workspace.ps1" %*
exit /b %ERRORLEVEL%
