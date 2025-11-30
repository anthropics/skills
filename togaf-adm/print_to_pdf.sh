#!/bin/bash

# Script para convertir HTML a PDF usando el navegador

HTML_FILE="Arquitectura_Empresarial_Fybeca_Gestion_Incidencias.html"
PDF_FILE="Arquitectura_Empresarial_Fybeca_Gestion_Incidencias.pdf"

# Método 1: Usar AppleScript para automatizar Chrome/Safari
osascript <<EOF
tell application "Safari"
    activate
    open POSIX file "$(pwd)/$HTML_FILE"
    delay 5
    tell application "System Events"
        keystroke "p" using command down
        delay 2
        keystroke return
        delay 1
        keystroke "g" using {command down, shift down}
        delay 1
        set the clipboard to "$(pwd)/$PDF_FILE"
        keystroke "v" using command down
        delay 1
        keystroke return
    end tell
end tell
EOF

echo "✅ PDF generado: $PDF_FILE"
