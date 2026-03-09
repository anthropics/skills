---
name: cep-search-app
description: App Streamlit de busca de CEP com validação robusta e integração com ViaCEP. Use quando precisar criar ou modificar aplicativos de busca de endereço por CEP brasileiro.
---

# App Streamlit de Busca de CEP

Este é um aplicativo Streamlit profissional para busca de informações de endereço através do CEP brasileiro, com validação robusta e integração com a API ViaCEP.

## Recursos

- **Validação Robusta**: Valida formato do CEP, remove caracteres especiais e detecta CEPs inválidos
- **Integração com ViaCEP**: Busca automática de endereços através da API ViaCEP
- **Retry Automático**: Sistema de retry com até 3 tentativas em caso de falha de rede
- **Tratamento de Erros**: Tratamento completo de erros com mensagens amigáveis
- **Interface Intuitiva**: Layout responsivo com feedback visual para o usuário
- **Exemplos Integrados**: Sidebar com exemplos de CEPs válidos

## Como Usar

### Instalação

```bash
pip install -r requirements.txt
```

### Executar o Aplicativo

```bash
streamlit run app.py
```

O aplicativo será aberto automaticamente no navegador em `http://localhost:8501`

## Funcionalidades

### Validação de CEP

O aplicativo valida:
- Formato do CEP (8 dígitos)
- Remove automaticamente caracteres não numéricos
- Detecta CEPs inválidos (ex: 00000000)
- Aceita formato com ou sem hífen (XXXXX-XXX ou XXXXXXXX)

### Busca de Endereço

Retorna informações completas:
- CEP formatado
- Logradouro
- Complemento
- Bairro
- Cidade
- Estado (UF)
- Código IBGE
- DDD
- GIA (se disponível)
- SIAFI (se disponível)

### Tratamento de Erros

- Timeout de conexão
- Erros de rede
- CEP não encontrado
- Validação de formato
- Mensagens de erro amigáveis

## Estrutura do Código

- `CEPValidator`: Classe para validação e formatação de CEP
- `ViaCEPAPI`: Classe para integração com a API ViaCEP
- `display_address()`: Função para exibir informações formatadas
- `main()`: Função principal do aplicativo

## Tecnologias Utilizadas

- **Streamlit**: Framework para criação de aplicativos web
- **Requests**: Biblioteca para requisições HTTP
- **ViaCEP API**: API pública brasileira de consulta de CEP

## Exemplos de CEPs Válidos

- `01310-100` - Av. Paulista, São Paulo/SP
- `20040-020` - Centro, Rio de Janeiro/RJ
- `30130-010` - Centro, Belo Horizonte/MG
- `40020-000` - Centro, Salvador/BA
- `80010-000` - Centro, Curitiba/PR

## Créditos

Dados fornecidos por [ViaCEP](https://viacep.com.br/)
