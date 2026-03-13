@echo off
REM Start GearSimulator GUI from the repo root and keep the window open on error.
cd /d "%~dp0"
setlocal

if exist ".venv\Scripts\python.exe" (
    ".venv\Scripts\python.exe" main.py
    goto end
)

py -3.9 main.py
if errorlevel 1 (
    echo.
    echo Failed to start with Python 3.9.
    echo Install dependencies with: py -3.9 -m pip install -r requirements.txt
)

:end
echo.
echo (Press any key to close)
pause >nul
