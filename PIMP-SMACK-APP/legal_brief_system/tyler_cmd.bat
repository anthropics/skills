@echo off
REM ============================================================
REM TYLER'S SHELL COMMANDS
REM Direct commands - no subprocess rewording
REM ============================================================

REM Set paths
set DATA_DIR=D:\SKilz\NINTH CIR5\legal_brief_system\data
set ECF_QUOTES=D:\SKilz\9th_Arch_Angel\9th_Cir_Brief\ECF_QUOTES.csv
set PDF_EXTRACTOR=D:\SKilz\COPILOTS-CLAUDES PILE OF JUNK\Gift_From_ Claude\extract_pdf.py
set OUTPUT_DIR=D:\SKilz\NINTH CIR5\legal_brief_system\output

REM ============================================================
REM COMMANDS
REM ============================================================

if "%1"=="extract" goto extract_pdf
if "%1"=="quotes" goto load_quotes
if "%1"=="validate" goto validate
if "%1"=="build" goto build
if "%1"=="help" goto help
goto help

:extract_pdf
REM Extract text from PDF - exact text, no AI processing
REM Usage: tyler_cmd extract input.pdf output.txt
echo Extracting PDF to text (exact text, no rewording)...
python "%PDF_EXTRACTOR%" "%2" "%3"
goto end

:load_quotes
REM Load and display quotes from ECF_QUOTES.csv
echo Loading exact quotes...
cd /d "D:\SKilz\NINTH CIR5\legal_brief_system"
python exact_quote_loader.py
goto end

:validate
REM Validate brief data
echo Validating brief data...
cd /d "D:\SKilz\NINTH CIR5\legal_brief_system"
python validate_brief.py
goto end

:build
REM Build brief from evidence
echo Building brief from evidence pool...
cd /d "D:\SKilz\NINTH CIR5\legal_brief_system"
python build_from_evidence.py
goto end

:help
echo.
echo ============================================================
echo TYLER'S SHELL COMMANDS
echo ============================================================
echo.
echo Usage: tyler_cmd [command] [args]
echo.
echo Commands:
echo   extract [pdf] [txt]  - Extract text from PDF (exact, no AI)
echo   quotes               - Load and display ECF quotes
echo   validate             - Check brief data for errors
echo   build                - Build brief from evidence pool
echo   help                 - Show this help
echo.
echo Example:
echo   tyler_cmd extract "my_doc.pdf" "my_doc.txt"
echo   tyler_cmd quotes
echo   tyler_cmd validate
echo.
goto end

:end
