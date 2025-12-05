#!/usr/bin/env python3
"""
Script para convertir Markdown a PDF usando markdown-pdf
"""
import sys
try:
    from markdown_pdf import MarkdownPdf, Section

    # Archivo de entrada y salida
    input_file = "Arquitectura_Empresarial_Fybeca_Gestion_Incidencias.md"
    output_file = "Arquitectura_Empresarial_Fybeca_Gestion_Incidencias.pdf"

    # Leer el contenido markdown
    with open(input_file, 'r', encoding='utf-8') as f:
        markdown_content = f.read()

    # Crear el PDF
    pdf = MarkdownPdf()
    pdf.add_section(Section(markdown_content))
    pdf.save(output_file)

    print(f"✅ PDF generado exitosamente: {output_file}")

except Exception as e:
    print(f"❌ Error al generar PDF: {e}")
    print(f"\nTipo de error: {type(e).__name__}")
    import traceback
    traceback.print_exc()
    sys.exit(1)
