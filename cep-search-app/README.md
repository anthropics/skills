# 📮 App Streamlit de Busca de CEP

Um aplicativo web profissional desenvolvido com Streamlit para buscar informações de endereço através do CEP brasileiro, com validação robusta e integração com a API ViaCEP.

![Python](https://img.shields.io/badge/Python-3.8+-blue.svg)
![Streamlit](https://img.shields.io/badge/Streamlit-1.31+-red.svg)
![License](https://img.shields.io/badge/License-MIT-green.svg)

## ✨ Recursos

- ✅ **Validação Robusta de CEP**
  - Valida formato (8 dígitos)
  - Remove caracteres especiais automaticamente
  - Detecta CEPs inválidos
  - Aceita formato com ou sem hífen

- 🔄 **Sistema de Retry Automático**
  - Até 3 tentativas em caso de falha
  - Timeout configurável (10 segundos)
  - Tratamento de erros de conexão

- 📊 **Interface Intuitiva**
  - Layout responsivo e moderno
  - Feedback visual em tempo real
  - Exemplos integrados na sidebar
  - Mensagens de erro amigáveis

- 🚀 **Integração com ViaCEP**
  - API pública brasileira
  - Dados completos de endereço
  - Informações de IBGE, DDD, GIA e SIAFI

## 🚀 Início Rápido

### Pré-requisitos

- Python 3.8 ou superior
- pip (gerenciador de pacotes Python)

### Instalação

1. Clone o repositório ou baixe os arquivos

2. Instale as dependências:
```bash
pip install -r requirements.txt
```

### Executar o Aplicativo

```bash
streamlit run app.py
```

O aplicativo será aberto automaticamente no navegador em `http://localhost:8501`

## 📖 Como Usar

1. **Digite um CEP** no campo de entrada
   - Formatos aceitos: `12345-678` ou `12345678`

2. **Clique em "Buscar"** para consultar o endereço

3. **Visualize os resultados** organizados em colunas:
   - Informações do endereço (logradouro, complemento, bairro)
   - Localização (cidade, estado, códigos)

4. **Use "Limpar"** para fazer uma nova busca

## 🎯 Exemplos de CEPs Válidos

| CEP | Endereço |
|-----|----------|
| `01310-100` | Av. Paulista - São Paulo/SP |
| `20040-020` | Centro - Rio de Janeiro/RJ |
| `30130-010` | Centro - Belo Horizonte/MG |
| `40020-000` | Centro - Salvador/BA |
| `80010-000` | Centro - Curitiba/PR |

## 🏗️ Arquitetura

### Classes Principais

#### `CEPValidator`
Responsável pela validação e formatação de CEP:
- `sanitize_cep()`: Remove caracteres não numéricos
- `validate_format()`: Valida formato do CEP
- `format_cep()`: Formata CEP no padrão XXXXX-XXX

#### `ViaCEPAPI`
Gerencia a integração com a API ViaCEP:
- `search_cep()`: Busca informações do endereço
- Sistema de retry automático
- Tratamento completo de erros

### Validações Implementadas

```python
✅ CEP com 8 dígitos
✅ Apenas números após sanitização
✅ Rejeita CEPs com todos dígitos iguais
✅ Aceita formatos: XXXXX-XXX ou XXXXXXXX
```

### Tratamento de Erros

- ⏱️ **Timeout**: Mensagem amigável após timeout de conexão
- 🔌 **Conexão**: Detecção de problemas de rede
- ❌ **HTTP**: Tratamento de erros de status HTTP
- ⚠️ **CEP não encontrado**: Validação de existência do CEP
- 🔧 **Formato inválido**: Validação antes da consulta

## 📊 Dados Retornados

O aplicativo exibe as seguintes informações quando o CEP é encontrado:

- **CEP**: Código postal formatado
- **Logradouro**: Nome da rua/avenida
- **Complemento**: Informações adicionais
- **Bairro**: Nome do bairro
- **Cidade**: Nome da cidade (localidade)
- **Estado**: UF (sigla do estado)
- **IBGE**: Código do município
- **DDD**: Código de área telefônico
- **GIA**: Guia de Informação e Apuração (SP)
- **SIAFI**: Sistema Integrado de Administração Financeira

## 🛠️ Tecnologias

- **[Streamlit](https://streamlit.io/)** - Framework para aplicativos web em Python
- **[Requests](https://requests.readthedocs.io/)** - Biblioteca HTTP para Python
- **[ViaCEP](https://viacep.com.br/)** - API pública de consulta de CEP

## 📝 Estrutura de Arquivos

```
cep-search-app/
├── app.py              # Aplicativo principal
├── requirements.txt    # Dependências do projeto
├── SKILL.md           # Documentação da skill
└── README.md          # Este arquivo
```

## 🔒 Segurança

- Validação de entrada antes de fazer requisições
- Sanitização de dados do usuário
- Timeout para evitar travamentos
- Tratamento seguro de exceções

## 🤝 Contribuindo

Contribuições são bem-vindas! Sinta-se à vontade para:
- Reportar bugs
- Sugerir novas funcionalidades
- Enviar pull requests

## 📄 Licença

Este projeto está sob a licença MIT.

## 🙏 Créditos

- Dados fornecidos pela API [ViaCEP](https://viacep.com.br/)
- Desenvolvido com [Streamlit](https://streamlit.io/)

## 📞 Suporte

Se encontrar algum problema ou tiver dúvidas:
1. Verifique se o CEP está correto
2. Confirme sua conexão com a internet
3. Verifique se as dependências estão instaladas corretamente

---

<div align="center">
Desenvolvido com ❤️ usando Streamlit
</div>
