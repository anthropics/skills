# 🎹 Editor e Tutor Inteligente de Notas Musicais

Um aplicativo web completo e interativo para criar vídeos educacionais de piano/teclado com notas musicais coloridas, transcrição automática de áudio, prática guiada em tempo real e análise de performance.

## 🌟 Funcionalidades Principais

### 1. **Player de Vídeo Integrado**
- Carregue qualquer vídeo do YouTube usando o link
- Controles de reprodução: Play/Pause, avançar/retroceder 5 segundos
- Timeline visual sincronizada mostrando a posição atual

### 2. **🎵 Transcrição Automática (Áudio → MIDI)**
- **Framework de integração** para Spotify Basic Pitch / Magenta Onsets & Frames
- Extrai notas musicais automaticamente do áudio do vídeo
- Controle de confiança mínima para filtrar detecções
- Modo demonstração incluído + instruções completas para produção
- **Tecnologias suportadas:**
  - Basic Pitch (Spotify) - Leve, roda no browser
  - Magenta Onsets & Frames - Especializado em piano
  - ByteDance Piano Transcription - Alta qualidade (backend)

### 3. **🎹 Conexão com Teclado MIDI (WebMIDI)**
- Conecte teclados MIDI diretamente no navegador
- Visualização em tempo real das notas tocadas
- Monitor de velocidade e intensidade
- Suporte a múltiplos dispositivos
- Zero latência para feedback instantâneo

### 4. **🎯 Modo Prática Guiada** (Sistema de Tutoria Inteligente)
- **Feedback em tempo real** enquanto você toca
- **Métricas de performance:**
  - Acertos vs Erros
  - Precisão (%)
  - Streak (sequência de acertos)
  - Análise de timing e pitch
- **Visualização dinâmica:** Canvas mostrando notas futuras
- **Sistema de gamificação:**
  - Streaks de 🔥
  - Conquistas por precisão
  - Análise personalizada de erros
- **Relatórios detalhados** com dicas de melhoria

### 5. **📝 Visualização de Partitura (VexFlow)**
- Geração automática de partituras musicais
- Suporte a clave de Sol e Fá
- Notas coloridas sincronizadas
- Exportação para imagem
- Preparação para exportação MIDI

### 6. **Editor Manual de Notas**
- Adicione notas musicais em qualquer momento do vídeo
- 12 notas disponíveis: Dó, Dó#, Ré, Ré#, Mi, Fá, Fá#, Sol, Sol#, Lá, Lá#, Si
- Escolha a oitava (1-7) e duração de cada nota
- Timeline interativa com blocos coloridos

### 7. **Sistema de Cores Inteligente**
- **Notas naturais** (sem sustenido): cores claras e vibrantes
  - Dó: Verde claro
  - Ré: Azul claro
  - Mi: Amarelo
  - Fá: Vermelho claro
  - Sol: Roxo claro
  - Lá: Laranja claro
  - Si: Rosa claro

- **Notas sustenidas** (#): cores escuras
  - Dó#: Verde escuro
  - Ré#: Azul escuro
  - Fá#: Vermelho escuro
  - Sol#: Roxo escuro (Índigo)
  - Lá#: Laranja escuro

### 8. **🤖 Gerador de Prompts Educacionais com IA**
Gera automaticamente dicas personalizadas sobre:
- ✋ **Posição das mãos**: Como posicionar dedos, pulsos e braços
- 💪 **Intensidade**: Controle de dinâmica e pressão nas teclas
- 🎵 **Uso do pedal**: Quando e como usar o pedal sustain
- ⏱️ **Ritmo e timing**: Técnicas de metrônomo e contagem
- 🎹 **Técnica geral**: Dicas de prática e aprendizado

### 9. **💾 Exportação e Salvamento**
- **Salvar Projeto (JSON)**: Todo o projeto incluindo vídeo, notas e prompts
- **Carregar Projeto**: Continue editando projetos salvos
- **Exportar Notas (CSV)**: Para uso em planilhas
- **Exportar Partitura**: Imagem PNG da partitura

## 🎓 Arquitetura do Sistema

### Blueprint de Produto (3 Modos de Operação)

#### 1. **MIDI-First** (Latência Mínima)
- WebMIDI.js para captura direta de teclado
- VexFlow para visualização de partitura
- Feedback instantâneo (< 10ms de latência)
- Ideal para: Prática em tempo real

#### 2. **Mic-First** (Sem Teclado Digital)
- Magenta Onsets & Frames via browser
- Web Audio API para análise em tempo real
- Ideal para: Usuários com piano acústico

#### 3. **Híbrido Pro** (Backend GPU)
- ByteDance Piano Transcription (qualidade profissional)
- FastAPI + Celery para processamento assíncrono
- Detecção de pedal sustain
- Ideal para: Transcrições complexas e avaliação avançada

## 🚀 Como Usar

### Workflow Básico

#### Passo 1: Carregar Vídeo
1. Cole o link do YouTube no campo de entrada
2. Clique em "Carregar Vídeo"
3. Aguarde o vídeo carregar

**Formatos aceitos:**
- `https://youtu.be/VIDEO_ID`
- `https://www.youtube.com/watch?v=VIDEO_ID`

#### Passo 2: Adicionar Notas (3 Opções)

**Opção A: Transcrição Automática (Recomendado)**
1. Clique em "🎵 Transcrever Áudio (Basic Pitch)"
2. Aguarde o processamento (modo demo incluído)
3. As notas serão adicionadas automaticamente

**Opção B: Teclado MIDI**
1. Conecte seu teclado MIDI ao computador
2. Clique em "🎹 Conectar Teclado MIDI"
3. Toque as notas enquanto o vídeo reproduz
4. Use o modo prática para feedback em tempo real

**Opção C: Manual**
1. Pause o vídeo no momento desejado
2. Selecione a nota clicando no botão correspondente
3. Escolha oitava e duração
4. Clique em "➕ Adicionar Nota no Tempo Atual"

#### Passo 3: Praticar com Feedback (Modo Tutor)
1. Certifique-se de ter um teclado MIDI conectado
2. Vá para "Modo Prática Guiada"
3. Clique em "▶️ Iniciar Prática"
4. Toque as notas corretas no momento certo
5. Acompanhe suas métricas em tempo real:
   - ✅ Acertos
   - ❌ Erros
   - 📊 Precisão (%)
   - 🔥 Streak atual

#### Passo 4: Gerar Partitura
1. Clique em "📝 Gerar Partitura (VexFlow)"
2. Escolha clave (Sol/Fá) e fórmula de compasso
3. A partitura será gerada com notas coloridas

#### Passo 5: Dicas de Aprendizado
1. Clique em "🤖 Gerar Dicas Automáticas"
2. Receba análise personalizada baseada nas notas
3. Use botões de categoria para dicas específicas

#### Passo 6: Salvar Trabalho
- **Projeto Completo**: "💾 Salvar Projeto (JSON)"
- **Apenas Notas**: "📄 Exportar Notas (CSV)"

## 🛠️ Tecnologias Utilizadas

### Frontend
- **HTML5**: Estrutura
- **CSS3**: Estilos e animações
- **JavaScript (Vanilla)**: Lógica principal
- **YouTube IFrame API**: Integração com vídeos

### Bibliotecas Musicais (Todas Open-Source)
- **VexFlow** (MIT) - Renderização de partituras
- **WebMIDI.js** (MIT) - Conexão com teclados MIDI
- **Spotify Basic Pitch** (Framework incluído) - Transcrição áudio→MIDI
- **Magenta.js** (Opcional) - ML para música no browser

### Datasets Recomendados (para treino/benchmark)
- **MAESTRO** - ~200h de piano com alinhamento fino
- **ASAP** - 222 partituras alinhadas a performances

## 📦 Arquivos do Projeto

```
music-video-note-editor/
├── index.html              # Interface principal
├── styles.css              # Estilos visuais
├── app.js                  # Lógica principal e orquestração
├── midi-handler.js         # Gerenciamento de MIDI (WebMIDI.js)
├── transcription-handler.js # Transcrição áudio→MIDI
├── practice-mode.js        # Modo prática com gamificação
├── score-renderer.js       # Renderização de partituras (VexFlow)
└── README.md               # Esta documentação
```

## 🎯 Casos de Uso

### Para Professores de Música
- Criar materiais didáticos interativos
- Avaliar progresso dos alunos com métricas
- Gerar exercícios personalizados

### Para YouTubers / Criadores de Conteúdo
- Produzir tutoriais de piano/teclado profissionais
- Adicionar notas visuais sincronizadas
- Exportar partituras para thumbnails

### Para Estudantes
- Aprender músicas através de vídeos
- Praticar com feedback em tempo real
- Acompanhar evolução com estatísticas

### Para Músicos Profissionais
- Transcrever músicas de vídeos automaticamente
- Criar partituras digitais rapidamente
- Analisar técnicas de outros pianistas

## 📊 Rubricas de Avaliação (Modo Prática)

O sistema avalia baseado em:

1. **Precisão de Pitch** (Nota Correta)
   - Detecção exata da nota tocada
   - Tolerância para enarmônicos (Dó# = Réb)

2. **Precisão de Timing** (Momento Certo)
   - Tolerância padrão: 500ms
   - Configurável no código

3. **Sustentação** (Duração)
   - Verifica se a nota foi mantida pelo tempo correto

4. **Métricas Gamificadas**
   - Streaks: sequências de acertos
   - Conquistas especiais a cada 5, 10, 20 acertos
   - Análise de padrões de erro

## 🔧 Integração com Transcrição Real

### Para produção com Basic Pitch:

```bash
npm install @spotify/basic-pitch
```

```javascript
import * as basicPitch from '@spotify/basic-pitch';

const model = await basicPitch.loadModel();
const frames = await basicPitch.detectNotes(audioBuffer, {
    onsetThreshold: 0.5,
    frameThreshold: 0.3,
    minNoteLength: 0.1
});
```

### Para backend com ByteDance Piano Transcription:

```bash
pip install piano-transcription-inference
```

```python
from piano_transcription_inference import PianoTranscription

transcriptor = PianoTranscription(device='cuda')
transcribed_dict = transcriptor.transcribe('audio.wav', 'output.mid')
```

## 🌐 Compatibilidade

- ✅ Chrome, Firefox, Safari, Edge (versões recentes)
- ✅ Responsivo para tablets
- ✅ WebMIDI: Chrome, Edge (Firefox requer flag)
- ⚠️ Requer conexão com internet (para CDNs e YouTube)

## 🚀 Instalação e Execução

### Opção 1: Direto no Navegador
1. Clone ou baixe este repositório
2. Abra `index.html` no navegador
3. Não requer servidor - funciona localmente!

### Opção 2: Servidor Local
```bash
# Python
python -m http.server 8000

# Node.js
npx http-server

# Acesse: http://localhost:8000
```

## 💡 Dicas e Truques

### Para Melhor Performance
- Use Chrome ou Edge para suporte completo a WebMIDI
- Conecte o teclado MIDI antes de abrir a página
- Use vídeos com áudio de boa qualidade para transcrição

### Para Melhor Aprendizado
- Comece com músicas simples (5-10 notas)
- Use o modo prática em velocidade reduzida
- Foque em precisão antes de velocidade
- Revise o relatório final após cada prática

### Atalhos Úteis
- **Enter**: Carregar vídeo após colar URL
- **Espaço**: Play/Pause (quando vídeo em foco)

## 🐛 Solução de Problemas

**Vídeo não carrega:**
- Verifique se o link está correto
- Alguns vídeos têm restrições de incorporação
- Verifique conexão com internet

**Teclado MIDI não conecta:**
- Apenas Chrome e Edge suportam WebMIDI totalmente
- Conecte o teclado antes de abrir a página
- Verifique se o teclado está ligado e reconhecido pelo sistema

**Transcrição não funciona:**
- O modo atual é demonstração
- Para produção real, siga instruções de integração no console
- Veja seção "Integração com Transcrição Real"

**Partitura com erro:**
- Certifique-se de ter notas adicionadas
- Verifique se a clave está correta para as oitavas usadas
- Muito graves → use clave de Fá
- Muito agudas → use clave de Sol

## 📚 Recursos de Aprendizado

### Documentação das Bibliotecas
- [VexFlow Docs](https://github.com/0xfe/vexflow/wiki)
- [WebMIDI.js Docs](https://webmidijs.org/)
- [Basic Pitch](https://github.com/spotify/basic-pitch)
- [Magenta.js](https://github.com/magenta/magenta-js)

### Datasets e Benchmarks
- [MAESTRO Dataset](https://magenta.tensorflow.org/datasets/maestro)
- [ASAP Dataset](https://github.com/fosfrancesco/asap-dataset)

## 🔐 Licenças e Escolhas Open-Source

Todas as bibliotecas usadas são open-source e permitem uso comercial:

- **VexFlow**: MIT License ✅
- **WebMIDI.js**: MIT License ✅
- **Basic Pitch**: Apache 2.0 ✅
- **Magenta**: Apache 2.0 ✅
- **YouTube IFrame API**: Terms of Service do YouTube

## 🤝 Contribuindo

Sinta-se à vontade para:
- Reportar bugs via Issues
- Sugerir novas funcionalidades
- Fazer fork e criar pull requests
- Melhorar a documentação
- Compartilhar seus casos de uso

## 🎵 Roadmap Futuro

- [ ] Integração completa com Basic Pitch (não apenas framework)
- [ ] Suporte a múltiplas mãos (esquerda/direita)
- [ ] Reconhecimento de acordes
- [ ] Exportação de vídeo com notas sobrepostas
- [ ] Modo multi-jogador (competição)
- [ ] Biblioteca de músicas pré-transcritas
- [ ] App mobile (React Native / Flutter)
- [ ] Detecção de pedal sustain
- [ ] Score following avançado com matchmaker

## 📝 Formato dos Arquivos

### Projeto (JSON)
```json
{
  "version": "1.0",
  "videoId": "VIDEO_ID",
  "videoUrl": "https://youtu.be/...",
  "notes": [
    {
      "id": 1234567890,
      "note": "C",
      "octave": 4,
      "startTime": 5.2,
      "duration": 0.5,
      "color": "#90EE90",
      "source": "manual" // ou "transcription" ou "midi"
    }
  ],
  "prompts": "Texto com dicas...",
  "practiceStats": {
    "attempts": 5,
    "bestAccuracy": 95.5,
    "totalPracticeTime": 1200
  }
}
```

### Notas (CSV)
```csv
Nota,Oitava,Tempo Início (s),Duração (s),Cor,Fonte
C,4,5.20,0.5,#90EE90,manual
D,4,5.80,0.5,#87CEEB,transcription
```

## 🏆 Conquistas Desbloqueáveis (Sistema de Gamificação)

- 🔥 **Streak Master**: 10 acertos seguidos
- 🎯 **Perfeccionista**: 100% de precisão
- 📈 **Persistente**: 50 práticas completadas
- ⚡ **Relâmpago**: Completar música em tempo < 5% de erro
- 🎹 **Virtuoso**: 1000 notas tocadas corretamente

## 💖 Desenvolvido com Amor

Este projeto foi criado para democratizar o aprendizado de piano/teclado através de tecnologia open-source e IA.

**Esperamos que este editor/tutor ajude você a:**
- Criar tutoriais musicais incríveis
- Aprender piano de forma visual e interativa
- Melhorar sua técnica com feedback em tempo real
- Compartilhar conhecimento musical com o mundo

---

**Desenvolvido com ❤️ para educadores e estudantes de música**

🎹 *"A música é a linguagem universal da humanidade"* - Henry Wadsworth Longfellow
