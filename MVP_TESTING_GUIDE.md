# MVP Testing Guide - Piano Training Platform

## 🎯 Objetivo

Este guia fornece instruções passo a passo para testar o MVP da plataforma de treinamento de piano com IA.

## ✅ Funcionalidades Prontas para Teste

### Frontend (React + TypeScript)
- [x] Modo MIDI com detecção de teclado
- [x] Renderização de partituras (OSMD)
- [x] MIDI Player com controle de velocidade
- [x] Practice Mode com feedback em tempo real
- [x] Dashboard de gamificação
- [x] Sistema de conquistas
- [x] Leaderboard competitivo
- [x] Metrônomo interativo
- [x] Sistema de loop de estudo
- [x] Interface responsiva

### Backend (Python + FastAPI)
- [x] API REST completa
- [x] Transcrição de áudio para MIDI
- [x] Análise de performance musical
- [x] Processamento assíncrono (Celery)
- [x] Integração com Supabase
- [x] Geração de relatórios
- [x] Webhooks para n8n

## 📦 Pré-requisitos

### Sistema
```bash
# Node.js >= 18
node --version

# Python >= 3.10
python --version

# Redis (para Celery)
redis-cli --version

# Git
git --version
```

### Hardware (Opcional)
- Teclado MIDI (USB) para melhor experiência
- Microfone para modo de áudio
- GPU (opcional, para transcrição rápida)

## 🚀 Instalação Rápida

### 1. Clone o Repositório

```bash
git clone https://github.com/criptolandiatv/skills.git
cd skills
```

### 2. Setup Frontend

```bash
# Instalar dependências
npm install

# Instalar bibliotecas essenciais
npm install tone @tonejs/midi opensheetmusicdisplay

# Iniciar servidor de desenvolvimento
npm run dev
```

Acesse: http://localhost:3000

### 3. Setup Backend

```bash
cd backend

# Criar ambiente virtual
python -m venv venv
source venv/bin/activate  # Linux/Mac
# ou
venv\Scripts\activate  # Windows

# Instalar dependências
pip install -r requirements.txt
# ou
poetry install

# Configurar variáveis de ambiente
cp .env.example .env
# Editar .env com suas credenciais

# Iniciar servidor
python start_server.py
# ou
uvicorn app.main:app --reload
```

Acesse: http://localhost:8000/docs

### 4. Setup Redis & Celery (Opcional)

```bash
# Terminal 1: Iniciar Redis
redis-server

# Terminal 2: Iniciar Celery Worker
cd backend
celery -A app.celery.celery_app worker --loglevel=info
```

## 🧪 Testes por Feature

### Teste 1: MIDI Input & Score Display ✅

**O que testar:**
- Conexão do teclado MIDI
- Renderização de partitura
- Detecção de notas tocadas

**Passos:**
1. Conecte um teclado MIDI via USB
2. Acesse http://localhost:3000
3. Na página principal, clique em "Modo MIDI"
4. Verifique se o status mostra "Conectado"
5. Toque algumas notas no teclado
6. Confirme que as notas aparecem na tela

**Resultado Esperado:**
- ✅ Teclado detectado automaticamente
- ✅ Notas aparecem em tempo real
- ✅ Partitura renderiza corretamente

### Teste 2: MIDI Player ✅

**O que testar:**
- Reprodução de arquivos MIDI
- Controle de velocidade
- Controle de volume

**Passos:**
1. Navegue até a página de "Practice Mode"
2. Carregue um arquivo MIDI (ou use o demo)
3. Clique em "Play" ▶️
4. Ajuste a velocidade (0.5x, 1x, 2x)
5. Ajuste o volume
6. Use a barra de progresso para navegar

**Resultado Esperado:**
- ✅ MIDI reproduz corretamente
- ✅ Velocidade ajusta o playback
- ✅ Controles respondem imediatamente

### Teste 3: Practice Mode ✅

**O que testar:**
- Feedback em tempo real
- Sistema de pontuação
- Detecção de notas corretas/incorretas

**Passos:**
1. Acesse "Practice Mode"
2. Clique em "Iniciar Prática"
3. Toque as notas indicadas na partitura
4. Observe o feedback visual (✓ ou ✗)
5. Verifique a pontuação em tempo real
6. Tente alcançar um combo alto

**Resultado Esperado:**
- ✅ Feedback instantâneo nas notas
- ✅ Pontuação atualiza corretamente
- ✅ Combo aumenta com notas corretas
- ✅ Grade (S, A, B, C, D) é calculada

### Teste 4: Gamification System ✅

**O que testar:**
- Sistema de streaks
- Conquistas
- Leaderboard
- Níveis e pontos

**Passos:**
1. Acesse o "Dashboard do Aluno"
2. Complete uma sessão de prática
3. Verifique se o streak aumentou
4. Confira conquistas desbloqueadas
5. Veja sua posição no leaderboard
6. Observe o progresso de nível

**Resultado Esperado:**
- ✅ Streak atualiza diariamente
- ✅ Conquistas desbloqueiam automaticamente
- ✅ Leaderboard mostra rankings
- ✅ Níveis calculados corretamente

### Teste 5: Tools (Metronome & Loop) ✅

**O que testar:**
- Metrônomo funcional
- Sistema de loop de estudo
- Controles de BPM

**Passos:**
1. Acesse a aba "Ferramentas"
2. Inicie o metrônomo
3. Ajuste o BPM (40-240)
4. Teste diferentes compassos (2/4, 3/4, 4/4, 6/8)
5. Use o "Tap Tempo" para detectar BPM
6. Configure um loop de compassos
7. Inicie o loop e pratique

**Resultado Esperado:**
- ✅ Metrônomo toca em BPM correto
- ✅ Tap tempo funciona
- ✅ Loop repete compassos selecionados
- ✅ Indicadores visuais funcionam

### Teste 6: Backend API ✅

**O que testar:**
- Endpoints REST
- Transcrição de áudio
- Análise de performance

**Passos:**
1. Acesse http://localhost:8000/docs
2. Teste o endpoint `/health`
3. Upload de arquivo de áudio:
```bash
curl -X POST "http://localhost:8000/api/v1/transcription/transcribe/upload" \
  -F "file=@piano_audio.wav"
```
4. Crie job de análise:
```bash
curl -X POST "http://localhost:8000/api/v1/analysis/analyze" \
  -H "Content-Type: application/json" \
  -d '{
    "score_midi_url": "path/to/score.mid",
    "performance_midi_url": "path/to/performance.mid"
  }'
```
5. Verifique status do job
6. Obtenha resultados da análise

**Resultado Esperado:**
- ✅ API responde corretamente
- ✅ Transcrição processa áudio
- ✅ Análise gera métricas
- ✅ Jobs assíncronos funcionam

## 🐛 Resolução de Problemas

### Problema: MIDI não detecta teclado

**Solução:**
```javascript
// Verificar suporte do navegador
if (!navigator.requestMIDIAccess) {
  console.error('Use Chrome, Edge ou Opera para MIDI support');
}

// Testar conexão
navigator.requestMIDIAccess()
  .then(access => console.log('MIDI OK!', access))
  .catch(err => console.error('MIDI Error:', err));
```

### Problema: Áudio não funciona

**Solução:**
```javascript
// Web Audio Context precisa de interação do usuário
import * as Tone from 'tone';

document.addEventListener('click', async () => {
  await Tone.start();
  console.log('Audio context ready!');
});
```

### Problema: Redis Connection Error

**Solução:**
```bash
# Verificar se Redis está rodando
redis-cli ping
# Deve responder: PONG

# Se não estiver rodando:
redis-server
```

### Problema: Backend não inicia

**Solução:**
```bash
# Verificar dependências
pip list | grep fastapi
pip list | grep celery

# Reinstalar se necessário
pip install -r requirements.txt --force-reinstall

# Verificar variáveis de ambiente
cat .env
```

### Problema: GPU não disponível

**Solução:**
```python
# No .env, forçar uso de CPU
USE_GPU=false
TORCH_DEVICE=cpu
```

## 📊 Métricas de Sucesso

### Testes Essenciais (Must Pass)
- [ ] Frontend carrega sem erros
- [ ] MIDI input funciona
- [ ] Partitura renderiza
- [ ] MIDI player reproduz
- [ ] Practice mode dá feedback
- [ ] Backend API responde
- [ ] Gamificação persiste dados

### Testes Desejáveis (Should Pass)
- [ ] Transcrição de áudio funciona
- [ ] Análise de performance funciona
- [ ] Supabase conecta
- [ ] Celery processa jobs
- [ ] Webhooks disparam

### Testes Opcionais (Nice to Have)
- [ ] GPU acelera transcrição
- [ ] Real-time score following
- [ ] Auto-accompaniment
- [ ] Social features

## 🎯 Critérios de Aprovação do MVP

### ✅ Aprovado se:
1. Frontend carrega e renderiza
2. MIDI input detecta notas
3. Practice mode funciona
4. Gamificação persiste
5. Backend API responde
6. Pelo menos 1 feature avançada funciona (transcrição OU análise)

### ⚠️ Revisão Necessária se:
- Frontend tem erros críticos
- MIDI não detecta em nenhum browser
- Backend não inicia
- Nenhuma feature avançada funciona

### ❌ Não Aprovado se:
- Frontend não carrega
- Erros impedem uso básico
- Backend completamente quebrado
- Nenhum teste essencial passa

## 📝 Relatório de Teste

### Template

```markdown
# Teste MVP - [Data]

## Configuração
- SO: [Windows/Linux/Mac]
- Node: [versão]
- Python: [versão]
- Browser: [Chrome/Edge/Firefox]
- MIDI: [Sim/Não, modelo do teclado]

## Resultados

### Frontend
- [ ] MIDI Input: ✅ / ⚠️ / ❌
- [ ] Score Display: ✅ / ⚠️ / ❌
- [ ] MIDI Player: ✅ / ⚠️ / ❌
- [ ] Practice Mode: ✅ / ⚠️ / ❌
- [ ] Gamification: ✅ / ⚠️ / ❌
- [ ] Tools: ✅ / ⚠️ / ❌

### Backend
- [ ] API Health: ✅ / ⚠️ / ❌
- [ ] Transcription: ✅ / ⚠️ / ❌
- [ ] Analysis: ✅ / ⚠️ / ❌
- [ ] Celery: ✅ / ⚠️ / ❌

## Problemas Encontrados
[Listar problemas]

## Sugestões
[Listar sugestões]

## Conclusão
[Aprovado / Revisão / Não Aprovado]
```

## 🚀 Próximos Passos Após Testes

### Se Aprovado:
1. Deploy em staging
2. Testes com usuários reais
3. Ajustes de UX
4. Performance optimization
5. Preparar para produção

### Se Revisão Necessária:
1. Corrigir bugs críticos
2. Melhorar features problemáticas
3. Re-testar
4. Documentar workarounds

### Se Não Aprovado:
1. Análise profunda dos problemas
2. Refatoração necessária
3. Testes unitários
4. Novo ciclo de teste

## 📞 Suporte

### Documentação
- [Frontend README](./src/README.md)
- [Backend README](./backend/README.md)
- [Feature 4 - Score Following](./backend/FEATURE_4_README.md)
- [Feature 7 - Gamification](./FEATURE_7_README.md)

### Problemas Comuns
- WebMIDI só funciona em Chrome/Edge/Opera
- iOS tem limitações de áudio
- GPU é opcional mas recomendado
- Redis necessário apenas para Celery

## ✅ Checklist Final

Antes de considerar o MVP pronto:

- [ ] Todos os testes essenciais passaram
- [ ] Documentação está atualizada
- [ ] Erros críticos foram corrigidos
- [ ] Performance é aceitável
- [ ] UX é intuitiva
- [ ] Código está versionado
- [ ] Deploy é reproduzível

---

**Versão:** 1.0.0
**Última Atualização:** 2025-10-25
**Autor:** Piano Training Platform Team
