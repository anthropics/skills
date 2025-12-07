@echo off
REM Ninth Circuit Opening Brief Assembler
REM Usage: ASSEMBLE_BRIEF.bat [command] [case-no]

cd /d "%~dp0"

if "%1"=="" (
    python assemble_opening_brief.py
    goto end
)

if "%1"=="all" (
    if "%2"=="" (
        python assemble_opening_brief.py --all --case-no DRAFT
    ) else (
        python assemble_opening_brief.py --all --case-no %2
    )
    goto end
)

if "%1"=="validate" (
    python assemble_opening_brief.py --validate
    goto end
)

if "%1"=="wordcount" (
    python assemble_opening_brief.py --word-count
    goto end
)

if "%1"=="toa" (
    python assemble_opening_brief.py --toa
    goto end
)

if "%1"=="toc" (
    python assemble_opening_brief.py --toc
    goto end
)

if "%1"=="extract" (
    python assemble_opening_brief.py --extract-citations
    goto end
)

if "%1"=="list" (
    python assemble_opening_brief.py --list-sections
    goto end
)

REM Assume it's a section name
python assemble_opening_brief.py --section %1 --case-no %2

:end
pause
