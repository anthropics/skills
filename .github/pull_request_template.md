# 🎹 Pull Request - Piano Training Platform

## 📝 Descrição

<!-- Descreva o que este PR faz -->

## 🎯 Tipo de Mudança

- [ ] ✨ Nova feature
- [ ] 🐛 Bug fix
- [ ] 🔧 Refatoração
- [ ] 📝 Documentação
- [ ] 🎨 UI/UX
- [ ] ⚡ Performance
- [ ] 🔒 Segurança
- [ ] 🧪 Testes

## 🔍 Checklist de Review

### Obrigatório (Blocking) ⚠️

#### Componentes (se aplicável)
- [ ] Todos os componentes têm PropTypes ou TypeScript types definidos
- [ ] Componentes não contêm lógica de negócio
- [ ] Componentes são testáveis (sem side effects diretos)

#### Áudio/MIDI (se aplicável)
- [ ] Código de áudio inclui tratamento de erros (try-catch)
- [ ] Implementado cleanup de recursos (removeEventListener, disconnect)
- [ ] Latência documentada e testada (< 50ms)
- [ ] Mensagens MIDI validadas antes de processar

#### Estado (se aplicável)
- [ ] Estado é imutável (spread operators ou immer)
- [ ] Sem lógica complexa em reducers/actions
- [ ] Estrutura do estado documentada

#### Testes
- [ ] Nova funcionalidade tem pelo menos 1 teste
- [ ] Coverage mínimo de 70% para novos arquivos
- [ ] Testes são legíveis (padrão AAA)

#### API/Backend (se aplicável)
- [ ] Chamadas API têm timeout configurado
- [ ] Implementado retry logic com exponential backoff
- [ ] Dados da API são validados (schemas)
- [ ] Sem chaves API ou secrets expostos

### Fortemente Recomendado 🟡

#### Qualidade de Código
- [ ] Componentes têm menos de 250 linhas
- [ ] Nomes são descritivos e claros
- [ ] Sem console.logs desnecessários
- [ ] TODOs foram convertidos em issues
- [ ] Commits seguem Conventional Commits

#### Acessibilidade (WCAG 2.1)
- [ ] Botões têm aria-labels descritivos
- [ ] Elementos navegáveis via teclado
- [ ] Contraste mínimo de 4.5:1
- [ ] Estados de foco visíveis
- [ ] Animações respeitam prefers-reduced-motion

#### Performance
- [ ] Usado lazy loading quando apropriado
- [ ] Sem re-renders desnecessários
- [ ] Assets otimizados (imagens, áudio)
- [ ] Bundle size dentro do limite (< 500KB gzipped)

#### Documentação
- [ ] Código complexo está comentado
- [ ] README atualizado se necessário
- [ ] Changelog atualizado
- [ ] JSDoc em funções públicas

### Específico por Área 🎯

#### Teclado Virtual (se aplicável)
- [ ] Suporta toque e mouse
- [ ] Resposta < 100ms
- [ ] Feedback visual imediato
- [ ] Suporta múltiplas teclas (acordes)
- [ ] Funciona em mobile, tablet e desktop

#### Sistema de Avaliação (se aplicável)
- [ ] Feedback construtivo e específico
- [ ] Tolera desvios humanos (±50ms)
- [ ] Progress tracking implementado
- [ ] Métricas documentadas

#### Pedagogia (se aplicável)
- [ ] Objetivos de aprendizado definidos
- [ ] Progressão de dificuldade documentada
- [ ] Feedback imediato ao aluno
- [ ] Sistema motivacional, não punitivo

## 🧪 Como Testar

<!-- Descreva os passos para testar este PR -->

1.
2.
3.

## 📸 Screenshots/Demo

<!-- Se aplicável, adicione screenshots ou GIFs -->

## 📚 Links Relacionados

- Issue: #
- Documentação:
- Design:

## ⚠️ Breaking Changes

<!-- Liste qualquer breaking change -->

- [ ] Não há breaking changes
- [ ] Breaking changes documentados abaixo

## 🎓 Aprendizados

<!-- Compartilhe algo que você aprendeu fazendo este PR -->

---

## ✅ Checklist Final

Antes de submeter:

- [ ] Código revisado localmente
- [ ] Testes passam localmente
- [ ] Lint passa sem erros
- [ ] Build funciona sem warnings
- [ ] Testado em Chrome, Firefox e Safari (se UI)
- [ ] Testado em mobile (se aplicável)
- [ ] Branch está atualizada com main/develop
- [ ] Descrição do PR está completa

## 🙏 Reviewers

<!-- Marque reviewers específicos se necessário -->

@reviewer1 @reviewer2

---

**Nota**: PRs que não atendem aos itens **Obrigatórios (Blocking)** serão retornados para ajustes antes do merge.
