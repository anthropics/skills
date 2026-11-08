"""
App Streamlit de Busca de CEP
Aplicativo para buscar informações de endereço através do CEP brasileiro
com validação robusta e integração com a API ViaCEP.
"""

import streamlit as st
import requests
import re
from typing import Optional, Dict, Any
import time


class CEPValidator:
    """Classe para validação de CEP brasileiro."""

    @staticmethod
    def sanitize_cep(cep: str) -> str:
        """
        Remove caracteres não numéricos do CEP.

        Args:
            cep: String do CEP a ser sanitizado

        Returns:
            CEP contendo apenas dígitos
        """
        return re.sub(r'\D', '', cep)

    @staticmethod
    def validate_format(cep: str) -> bool:
        """
        Valida o formato do CEP.

        Args:
            cep: String do CEP a ser validado

        Returns:
            True se o formato é válido, False caso contrário
        """
        # Remove caracteres não numéricos
        clean_cep = CEPValidator.sanitize_cep(cep)

        # CEP deve ter exatamente 8 dígitos
        if len(clean_cep) != 8:
            return False

        # Verifica se contém apenas dígitos
        if not clean_cep.isdigit():
            return False

        # Verifica se não é um CEP inválido (todos os dígitos iguais)
        if len(set(clean_cep)) == 1:
            return False

        return True

    @staticmethod
    def format_cep(cep: str) -> str:
        """
        Formata o CEP no padrão XXXXX-XXX.

        Args:
            cep: String do CEP a ser formatado

        Returns:
            CEP formatado
        """
        clean_cep = CEPValidator.sanitize_cep(cep)
        return f"{clean_cep[:5]}-{clean_cep[5:]}"


class ViaCEPAPI:
    """Classe para interação com a API ViaCEP."""

    BASE_URL = "https://viacep.com.br/ws"
    TIMEOUT = 10
    MAX_RETRIES = 3

    @staticmethod
    def search_cep(cep: str) -> Optional[Dict[str, Any]]:
        """
        Busca informações de endereço através do CEP.

        Args:
            cep: String do CEP a ser buscado

        Returns:
            Dicionário com informações do endereço ou None em caso de erro
        """
        clean_cep = CEPValidator.sanitize_cep(cep)
        url = f"{ViaCEPAPI.BASE_URL}/{clean_cep}/json/"

        for attempt in range(ViaCEPAPI.MAX_RETRIES):
            try:
                response = requests.get(url, timeout=ViaCEPAPI.TIMEOUT)
                response.raise_for_status()

                data = response.json()

                # ViaCEP retorna {"erro": true} quando o CEP não existe
                if data.get("erro"):
                    return None

                return data

            except requests.exceptions.Timeout:
                if attempt < ViaCEPAPI.MAX_RETRIES - 1:
                    time.sleep(1)
                    continue
                st.error("⏱️ Tempo de espera excedido. Tente novamente.")
                return None

            except requests.exceptions.ConnectionError:
                if attempt < ViaCEPAPI.MAX_RETRIES - 1:
                    time.sleep(1)
                    continue
                st.error("🔌 Erro de conexão. Verifique sua internet.")
                return None

            except requests.exceptions.HTTPError as e:
                st.error(f"❌ Erro HTTP: {e}")
                return None

            except requests.exceptions.RequestException as e:
                st.error(f"❌ Erro na requisição: {e}")
                return None

            except ValueError:
                st.error("❌ Erro ao processar resposta da API.")
                return None

        return None


def display_address(data: Dict[str, Any]) -> None:
    """
    Exibe as informações de endereço formatadas.

    Args:
        data: Dicionário com informações do endereço
    """
    st.success("✅ CEP encontrado!")

    # Criar colunas para melhor visualização
    col1, col2 = st.columns(2)

    with col1:
        st.markdown("### 📍 Informações do Endereço")
        st.markdown(f"**CEP:** {data.get('cep', 'N/A')}")
        st.markdown(f"**Logradouro:** {data.get('logradouro', 'N/A')}")
        st.markdown(f"**Complemento:** {data.get('complemento', 'N/A')}")
        st.markdown(f"**Bairro:** {data.get('bairro', 'N/A')}")

    with col2:
        st.markdown("### 🏙️ Localização")
        st.markdown(f"**Cidade:** {data.get('localidade', 'N/A')}")
        st.markdown(f"**Estado:** {data.get('uf', 'N/A')}")
        st.markdown(f"**IBGE:** {data.get('ibge', 'N/A')}")
        st.markdown(f"**DDD:** {data.get('ddd', 'N/A')}")

    # Informações adicionais se disponíveis
    if data.get('gia'):
        st.markdown(f"**GIA:** {data.get('gia')}")

    if data.get('siafi'):
        st.markdown(f"**SIAFI:** {data.get('siafi')}")


def main():
    """Função principal do aplicativo."""

    # Configuração da página
    st.set_page_config(
        page_title="Busca de CEP",
        page_icon="📮",
        layout="centered",
        initial_sidebar_state="collapsed"
    )

    # Título e descrição
    st.title("📮 Busca de CEP")
    st.markdown("""
    Busque informações de endereço através do CEP brasileiro.
    Digite um CEP válido no formato **XXXXX-XXX** ou **XXXXXXXX**.
    """)

    # Sidebar com informações
    with st.sidebar:
        st.header("ℹ️ Sobre")
        st.markdown("""
        Este aplicativo permite buscar informações de endereço através do CEP.

        **Recursos:**
        - ✅ Validação robusta de CEP
        - 🔄 Retry automático em caso de falha
        - 📊 Interface intuitiva
        - 🚀 Integração com ViaCEP

        **Formato aceito:**
        - 12345-678
        - 12345678
        """)

        st.header("📋 Exemplos")
        st.code("01310-100  # Av. Paulista, SP")
        st.code("20040-020  # Centro, RJ")
        st.code("30130-010  # Centro, BH")

    # Formulário de busca
    with st.form(key="cep_form", clear_on_submit=False):
        cep_input = st.text_input(
            "Digite o CEP:",
            max_chars=9,
            placeholder="Ex: 01310-100",
            help="Digite o CEP com ou sem hífen"
        )

        col1, col2, col3 = st.columns([1, 1, 2])
        with col1:
            search_button = st.form_submit_button("🔍 Buscar", use_container_width=True)
        with col2:
            clear_button = st.form_submit_button("🗑️ Limpar", use_container_width=True)

    # Processar busca
    if search_button and cep_input:
        # Validar formato
        if not CEPValidator.validate_format(cep_input):
            st.error("❌ CEP inválido! Digite um CEP válido com 8 dígitos.")
            st.info("💡 Exemplos válidos: 01310-100, 01310100")
        else:
            # Mostrar CEP formatado
            formatted_cep = CEPValidator.format_cep(cep_input)
            st.info(f"🔎 Buscando informações para o CEP: **{formatted_cep}**")

            # Buscar na API
            with st.spinner("Consultando API..."):
                result = ViaCEPAPI.search_cep(cep_input)

            # Exibir resultado
            if result:
                display_address(result)
            else:
                st.warning("⚠️ CEP não encontrado. Verifique se o CEP está correto.")

    elif search_button and not cep_input:
        st.warning("⚠️ Por favor, digite um CEP para buscar.")

    # Rodapé
    st.markdown("---")
    st.markdown(
        "<div style='text-align: center; color: gray;'>"
        "Desenvolvido com Streamlit | Dados fornecidos por ViaCEP"
        "</div>",
        unsafe_allow_html=True
    )


if __name__ == "__main__":
    main()
