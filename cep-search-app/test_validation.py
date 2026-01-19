"""
Script de teste para validação de CEP
Demonstra as funcionalidades de validação implementadas
"""

import sys
import os

# Adiciona o diretório ao path para importar as classes
sys.path.insert(0, os.path.dirname(__file__))

# Importa apenas as classes necessárias para teste sem rodar o Streamlit
import re
from typing import Optional


class CEPValidator:
    """Classe para validação de CEP brasileiro."""

    @staticmethod
    def sanitize_cep(cep: str) -> str:
        """Remove caracteres não numéricos do CEP."""
        return re.sub(r'\D', '', cep)

    @staticmethod
    def validate_format(cep: str) -> bool:
        """Valida o formato do CEP."""
        clean_cep = CEPValidator.sanitize_cep(cep)

        if len(clean_cep) != 8:
            return False

        if not clean_cep.isdigit():
            return False

        if len(set(clean_cep)) == 1:
            return False

        return True

    @staticmethod
    def format_cep(cep: str) -> str:
        """Formata o CEP no padrão XXXXX-XXX."""
        clean_cep = CEPValidator.sanitize_cep(cep)
        return f"{clean_cep[:5]}-{clean_cep[5:]}"


def test_cep_validation():
    """Testa a validação de CEP com vários casos."""

    test_cases = [
        # (CEP de entrada, esperado válido, descrição)
        ("01310-100", True, "CEP válido com hífen"),
        ("01310100", True, "CEP válido sem hífen"),
        ("12345-678", True, "CEP válido formato padrão"),
        ("12345678", True, "CEP válido 8 dígitos"),
        ("1234567", False, "CEP com 7 dígitos"),
        ("123456789", False, "CEP com 9 dígitos"),
        ("00000000", False, "CEP com todos dígitos iguais"),
        ("11111-111", False, "CEP com todos dígitos iguais"),
        ("abcd-efgh", False, "CEP com letras"),
        ("", False, "CEP vazio"),
        ("12345", False, "CEP muito curto"),
        ("20040-020", True, "CEP Rio de Janeiro"),
        ("30130-010", True, "CEP Belo Horizonte"),
    ]

    print("=" * 70)
    print("TESTE DE VALIDAÇÃO DE CEP")
    print("=" * 70)
    print()

    passed = 0
    failed = 0

    for cep, expected_valid, description in test_cases:
        is_valid = CEPValidator.validate_format(cep)
        status = "✅ PASSOU" if is_valid == expected_valid else "❌ FALHOU"

        if is_valid == expected_valid:
            passed += 1
        else:
            failed += 1

        print(f"{status} | {description}")
        print(f"  Entrada: '{cep}'")
        print(f"  Esperado: {'Válido' if expected_valid else 'Inválido'}")
        print(f"  Resultado: {'Válido' if is_valid else 'Inválido'}")

        if is_valid:
            formatted = CEPValidator.format_cep(cep)
            sanitized = CEPValidator.sanitize_cep(cep)
            print(f"  Sanitizado: '{sanitized}'")
            print(f"  Formatado: '{formatted}'")

        print()

    print("=" * 70)
    print(f"RESULTADO FINAL: {passed} passou, {failed} falhou de {len(test_cases)} testes")
    print("=" * 70)

    return failed == 0


if __name__ == "__main__":
    success = test_cep_validation()
    sys.exit(0 if success else 1)
