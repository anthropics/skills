# 🎹 Guia de Contribuição - Piano Training Platform

Obrigado por contribuir! Este guia ajudará você a começar.

## 📋 Índice

- [Código de Conduta](#código-de-conduta)
- [Como Contribuir](#como-contribuir)
- [Configuração do Ambiente](#configuração-do-ambiente)
- [Padrões de Código](#padrões-de-código)
- [Regras de Review](#regras-de-review)
- [Processo de Pull Request](#processo-de-pull-request)
- [Testes](#testes)
- [Documentação](#documentação)

---

## 📜 Código de Conduta

- Seja respeitoso e inclusivo
- Forneça feedback construtivo
- Aceite críticas com profissionalismo
- Foque no que é melhor para a comunidade

---

## 🤝 Como Contribuir

### Formas de Contribuir

1. **Reportar Bugs**: Abra uma issue com detalhes
2. **Sugerir Features**: Use o template de feature request
3. **Melhorar Documentação**: PRs de documentação são sempre bem-vindos
4. **Corrigir Bugs**: Veja issues marcadas com `good first issue`
5. **Implementar Features**: Escolha issues do roadmap

### Antes de Começar

1. Verifique se já existe uma issue relacionada
2. Comente na issue que você pretende trabalhar nela
3. Aguarde aprovação do mantenedor antes de começar código grande
4. Para pequenas correções, pode ir direto ao PR

---

## 🛠️ Configuração do Ambiente

### Pré-requisitos

```bash
# Node.js >= 18
node --version

# Python >= 3.10
python --version

# Git
git --version
```

### Instalação

```bash
# 1. Fork o repositório no GitHub

# 2. Clone seu fork
git clone https://github.com/SEU-USERNAME/skills.git
cd skills

# 3. Adicione o upstream
git remote add upstream https://github.com/criptolandiatv/skills.git

# 4. Instale dependências do frontend
npm install

# 5. Instale dependências do backend
cd backend
pip install -r requirements.txt
# ou
poetry install

# 6. Configure variáveis de ambiente
cp .env.example .env
# Edite .env com suas credenciais

# 7. Execute os testes
npm test
cd backend && pytest
```

### Desenvolvimento

```bash
# Terminal 1: Frontend
npm run dev

# Terminal 2: Backend
cd backend
python start_server.py

# Terminal 3: Redis (se necessário)
redis-server

# Terminal 4: Celery (se necessário)
cd backend
celery -A app.celery worker --loglevel=info
```

---

## 🎨 Padrões de Código

### Naming Conventions

**Componentes React**:
```typescript
// PascalCase para componentes
export const PianoKeyboard: React.FC<Props> = ({ ... }) => { ... };

// camelCase para funções e variáveis
const handleNotePress = (note: string) => { ... };

// SCREAMING_SNAKE_CASE para constantes
const MAX_VELOCITY = 127;
```

**Arquivos**:
```
PianoKeyboard.tsx          # Componentes
useGamification.ts         # Hooks
piano-utils.ts             # Utilities
PianoKeyboard.test.tsx     # Testes
PianoKeyboard.css          # Estilos
```

### Estrutura de Componentes

```typescript
import React, { useState, useEffect } from 'react';
import './Component.css';

// 1. Interfaces/Types
interface Props {
  prop1: string;
  prop2?: number;
}

// 2. Componente
export const Component: React.FC<Props> = ({ prop1, prop2 = 0 }) => {
  // 2.1. State
  const [state, setState] = useState<Type>(initialValue);

  // 2.2. Effects
  useEffect(() => {
    // ...
    return () => {
      // Cleanup
    };
  }, [dependencies]);

  // 2.3. Handlers
  const handleEvent = () => {
    // ...
  };

  // 2.4. Render
  return (
    <div className="component">
      {/* JSX */}
    </div>
  );
};
```

### Commits (Conventional Commits)

```bash
feat: adiciona componente de teclado virtual
fix: corrige latência no MIDI input
docs: atualiza README com instruções de setup
refactor: simplifica lógica de gamificação
test: adiciona testes para ScoreFollower
perf: otimiza renderização de partituras
style: formata código com Prettier
chore: atualiza dependências
```

---

## 🔍 Regras de Review

### ⚠️ Bloqueantes (Impedem Merge)

#### Componentes
- [ ] Componentes têm PropTypes ou TypeScript types
- [ ] Sem lógica de negócio dentro de componentes UI
- [ ] Componentes são testáveis

#### Áudio/MIDI
- [ ] Código de áudio tem try-catch
- [ ] Cleanup de recursos implementado (removeEventListener)
- [ ] Latência documentada (alvo: < 50ms)

#### Estado
- [ ] Estado gerenciado de forma imutável
- [ ] Sem lógica complexa em reducers

#### Testes
- [ ] Nova funcionalidade tem ≥ 1 teste
- [ ] Coverage mínimo de 70% em arquivos novos

#### API/Backend
- [ ] Chamadas API têm timeout
- [ ] Retry logic implementado
- [ ] Validação de dados da API
- [ ] Sem secrets expostos

### 🟡 Fortemente Recomendado

- Componentes < 250 linhas
- Acessibilidade (WCAG 2.1)
- Performance otimizada
- Documentação atualizada

### 📝 Verificação Automática

```bash
# Antes de fazer commit:
npm run lint          # ESLint
npm run format:check  # Prettier
npm test             # Testes
npm run type-check   # TypeScript
```

---

## 🔄 Processo de Pull Request

### 1. Crie uma Branch

```bash
git checkout -b feature/nome-da-feature
# ou
git checkout -b fix/nome-do-bug
```

### 2. Faça suas Mudanças

```bash
# Commit frequentemente
git add .
git commit -m "feat: implementa funcionalidade X"
```

### 3. Mantenha Atualizado

```bash
# Periodicamente, sincronize com upstream
git fetch upstream
git rebase upstream/main
```

### 4. Execute Verificações

```bash
# Lint e format
npm run lint
npm run format

# Testes
npm test

# Build
npm run build

# Backend
cd backend
flake8 app/
black app/
pytest
```

### 5. Push e Abra PR

```bash
git push origin feature/nome-da-feature
```

No GitHub:
1. Abra Pull Request
2. Preencha o template completamente
3. Aguarde CI passar
4. Responda a feedbacks de reviewers

### 6. Após Aprovação

```bash
# Squash commits se necessário
git rebase -i HEAD~N

# Force push (cuidado!)
git push --force-with-lease
```

---

## 🧪 Testes

### Frontend

```bash
# Rodar todos os testes
npm test

# Rodar com coverage
npm test -- --coverage

# Rodar em watch mode
npm test -- --watch

# Rodar testes específicos
npm test -- MidiPlayer
```

### Backend

```bash
cd backend

# Rodar todos os testes
pytest

# Com coverage
pytest --cov=app --cov-report=html

# Testes específicos
pytest tests/test_score_following.py

# Com verbosidade
pytest -v
```

### Estrutura de Teste

```typescript
// Component.test.tsx
import { render, screen, fireEvent } from '@testing-library/react';
import { Component } from './Component';

describe('Component', () => {
  it('should render correctly', () => {
    render(<Component prop="value" />);
    expect(screen.getByText('Expected Text')).toBeInTheDocument();
  });

  it('should handle events', () => {
    const handleClick = jest.fn();
    render(<Component onClick={handleClick} />);

    fireEvent.click(screen.getByRole('button'));
    expect(handleClick).toHaveBeenCalledTimes(1);
  });
});
```

---

## 📚 Documentação

### JSDoc

```typescript
/**
 * Converte nota MIDI (0-127) para frequência em Hz
 *
 * @param midiNote - Número da nota MIDI (0-127)
 * @returns Frequência em Hz
 *
 * @example
 * ```ts
 * midiToFrequency(69); // 440 (A4)
 * ```
 */
export const midiToFrequency = (midiNote: number): number => {
  return 440 * Math.pow(2, (midiNote - 69) / 12);
};
```

### README

Ao adicionar nova feature, atualize:
- `README.md` - Overview geral
- `FEATURE_X_README.md` - Documentação específica
- `MVP_TESTING_GUIDE.md` - Se afeta testes

---

## 🎯 Áreas Específicas

### Componentes de Áudio/MIDI

```typescript
// Sempre implemente cleanup
useEffect(() => {
  const audioContext = new AudioContext();

  return () => {
    audioContext.close(); // ✅ Cleanup
  };
}, []);
```

### Teclado Virtual

- Suporte touch + mouse
- Resposta < 100ms
- Feedback visual imediato
- Múltiplas teclas (acordes)

### Sistema de Avaliação

- Feedback construtivo
- Tolerar desvios humanos (±50ms)
- Progress tracking
- Métricas documentadas

---

## 🐛 Reportando Bugs

Use o template de issue com:

1. **Descrição**: O que aconteceu
2. **Esperado**: O que deveria acontecer
3. **Passos para Reproduzir**: 1, 2, 3...
4. **Ambiente**: OS, Browser, versões
5. **Screenshots**: Se aplicável
6. **Logs**: Console errors

---

## 💡 Sugerindo Features

1. Verifique se já não existe issue similar
2. Descreva o problema que resolve
3. Proponha solução
4. Considere alternativas
5. Adicione mockups/wireframes se possível

---

## 🏆 Boas Práticas

### DOs ✅

- Escreva testes antes de implementar (TDD)
- Faça commits pequenos e frequentes
- Mantenha PRs focados (1 feature por PR)
- Documente decisões arquiteturais importantes
- Peça ajuda quando travar

### DON'Ts ❌

- Não commite código comentado
- Não deixe console.log em produção
- Não faça PRs gigantes (> 500 linhas)
- Não ignore warnings do linter
- Não pule testes

---

## 📞 Contato

- **Issues**: https://github.com/criptolandiatv/skills/issues
- **Discussions**: https://github.com/criptolandiatv/skills/discussions
- **Email**: [seu-email]

---

## 🙏 Reconhecimentos

Obrigado a todos os contribuidores que tornam este projeto possível!

---

**Última atualização**: 2025-10-25
**Versão**: 1.0.0
