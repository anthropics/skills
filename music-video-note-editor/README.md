# 🎹 Editor e Tutor Inteligente de Notas Musicais

Um aplicativo web completo e interativo para criar vídeos educacionais de piano/teclado com notas musicais coloridas, transcrição automática de áudio, prática guiada em tempo real e análise de performance.

## ✨ Funcionalidades Principais

### 1. **Player de Vídeo Integrado**
- Carregue qualquer vídeo do YouTube
- Controles: Play/Pause, ±5s
- Timeline visual sincronizada

### 2. **🎵 Transcrição Automática (Áudio → MIDI)**
- Framework pronto para integração com:
  - **Spotify Basic Pitch** (leve, browser)
  - **Magenta Onsets & Frames** (especializado em piano)
  - **ByteDance Piano Transcription** (backend, alta qualidade)
- Modo demonstração funcional incluído
- Controle de confiança mínima
- Instruções completas para produção

### 3. **🎹 Conexão com Teclado MIDI (WebMIDI)**
- Conecte teclados MIDI no navegador
- Visualização em tempo real
- Monitor de velocidade
- Zero latência

### 4. **🎯 Modo Prática Guiada** (Tutor Inteligente)
- **Feedback em tempo real**
- **Métricas:**
  - Acertos vs Erros
  - Precisão (%)
  - Streak (🔥)
  - Análise de timing e pitch
- **Visualização dinâmica** em canvas
- **Gamificação:** conquistas e streaks
- **Relatórios detalhados** com dicas

### 5. **📝 Visualização de Partitura (VexFlow)**
- Geração automática de partituras
- Claves Sol e Fá
- Notas coloridas
- Exportação para PNG

### 6. **Editor Manual de Notas**
- 12 notas (Dó, Dó#, Ré, Ré#, Mi, Fá, Fá#, Sol, Sol#, Lá, Lá#, Si)
- Oitavas 1-7
- Timeline interativa

### 7. **Sistema de Cores Pedagógico**
**Notas naturais** (claras):
- Dó: Verde claro | Ré: Azul claro | Mi: Amarelo
- Fá: Vermelho claro | Sol: Roxo claro | Lá: Laranja claro | Si: Rosa claro

**Notas sustenidas** (escuras):
- Dó#: Verde escuro | Ré#: Azul escuro | Fá#: Vermelho escuro
- Sol#: Roxo escuro | Lá#: Laranja escuro

### 8. **🤖 Gerador de Prompts Educacionais**
Dicas personalizadas sobre:
- ✋ Posição das mãos
- 💪 Intensidade
- 🎵 Pedal
- ⏱️ Ritmo
- 🎹 Técnica geral

### 9. **💾 Exportação Completa**
- Salvar projeto (JSON)
- Carregar projeto
- Exportar notas (CSV)
- Exportar partitura (PNG)

## 🚀 Como Usar

### Início Rápido

1. **Abra `index.html` no navegador**
   - Recomendado: Chrome ou Edge (suporte WebMIDI)

2. **Carregue um vídeo do YouTube**
   - Cole o link: `https://youtu.be/VIDEO_ID`

3. **Adicione notas** (3 opções):
   - 🎵 **Transcrição automática** (IA)
   - 🎹 **Conectar teclado MIDI** e tocar
   - ✏️ **Adicionar manualmente**

4. **Pratique com feedback**
   - Conecte teclado MIDI
   - Modo Prática → Iniciar
   - Toque as notas corretas no momento certo
   - Veja métricas em tempo real

5. **Gere partitura**
   - Escolha clave e compasso
   - VexFlow gera notação musical

6. **Receba dicas**
   - IA analisa suas notas
   - Prompts personalizados

7. **Salve seu trabalho**
   - Projeto completo (JSON)
   - Apenas notas (CSV)

## 🛠️ Arquitetura do Sistema

### Blueprint de Produto (3 Modos)

#### 1. **MIDI-First** (Latência Mínima)
- WebMIDI.js para captura direta
- VexFlow para partitura
- Feedback instantâneo (< 10ms)
- **Ideal para:** Prática em tempo real

#### 2. **Mic-First** (Sem Teclado Digital)
- Magenta Onsets & Frames via browser
- Web Audio API
- **Ideal para:** Piano acústico

#### 3. **Híbrido Pro** (Backend GPU)
- ByteDance Piano Transcription
- FastAPI + Celery
- Detecção de pedal sustain
- **Ideal para:** Transcrições complexas

## 📦 Arquivos do Projeto

```
music-video-note-editor/
├── index.html                    # Interface principal
├── styles.css                    # Estilos visuais
├── app.js                        # Orquestração principal
├── midi-handler.js               # WebMIDI management
├── transcription-handler.js      # Transcrição áudio→MIDI
├── practice-mode.js              # Tutor com gamificação
├── score-renderer.js             # Partituras (VexFlow)
└── README.md                     # Esta documentação
```

## 🔧 Tecnologias Utilizadas

### Frontend
- **HTML5**, **CSS3**, **JavaScript (Vanilla)**
- **YouTube IFrame API**

### Bibliotecas (Open-Source)
- **VexFlow 4.2.2** (MIT) - Partituras
- **WebMIDI.js 3.1.6** (MIT) - MIDI
- **Framework pronto para:**
  - Spotify Basic Pitch (Apache 2.0)
  - Magenta.js (Apache 2.0)
  - ByteDance Piano Transcription

## 🔐 Integração com Transcrição Real

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

### Para backend com ByteDance:

```bash
pip install piano-transcription-inference
```

```python
from piano_transcription_inference import PianoTranscription

transcriptor = PianoTranscription(device='cuda')
transcribed_dict = transcriptor.transcribe('audio.wav', 'output.mid')
```

## 🎯 Casos de Uso

### Para Professores
- Materiais didáticos interativos
- Avaliação de alunos com métricas
- Exercícios personalizados

### Para YouTubers
- Tutoriais profissionais de piano
- Notas visuais sincronizadas
- Partituras para thumbnails

### Para Estudantes
- Aprender músicas de vídeos
- Praticar com feedback real-time
- Acompanhar evolução

### Para Músicos
- Transcrever músicas automaticamente
- Criar partituras digitais
- Analisar técnicas

## 📊 Sistema de Gamificação

### Métricas de Avaliação
- **Precisão de Pitch:** Nota correta
- **Precisão de Timing:** Momento certo (±500ms)
- **Sustentação:** Duração correta
- **Streaks:** Sequências de acertos

### Conquistas
- 🔥 **Streak Master:** 10 acertos seguidos
- 🎯 **Perfeccionista:** 100% de precisão
- 📈 **Persistente:** 50 práticas completadas
- ⚡ **Relâmpago:** < 5% de erro
- 🎹 **Virtuoso:** 1000 notas corretas

## 💡 Dicas e Truques

### Para Melhor Performance
- Use Chrome/Edge (WebMIDI completo)
- Conecte teclado MIDI antes de abrir
- Use vídeos com áudio de boa qualidade

### Para Melhor Aprendizado
- Comece com músicas simples (5-10 notas)
- Pratique devagar primeiro
- Foco em precisão > velocidade
- Revise relatórios finais

### Atalhos
- **Enter:** Carregar vídeo
- **Espaço:** Play/Pause (vídeo em foco)

## 🐛 Solução de Problemas

**Vídeo não carrega:**
- Verifique o link
- Alguns vídeos têm restrições
- Verifique internet

**Teclado MIDI não conecta:**
- Use Chrome ou Edge
- Conecte antes de abrir a página
- Verifique se está reconhecido pelo sistema

**Transcrição não funciona:**
- Modo atual é demonstração
- Para produção: veja seção "Integração"
- Consulte console do navegador

**Partitura com erro:**
- Adicione notas primeiro
- Verifique clave vs oitavas
- Graves → Fá | Agudas → Sol

## 📚 Recursos de Aprendizado

### Documentação
- [VexFlow](https://github.com/0xfe/vexflow/wiki)
- [WebMIDI.js](https://webmidijs.org/)
- [Basic Pitch](https://github.com/spotify/basic-pitch)
- [Magenta.js](https://github.com/magenta/magenta-js)

### Datasets
- [MAESTRO](https://magenta.tensorflow.org/datasets/maestro) - 200h piano
- [ASAP](https://github.com/fosfrancesco/asap-dataset) - 222 partituras

## 🌐 Compatibilidade

- ✅ Chrome, Firefox, Safari, Edge (recentes)
- ✅ Responsivo para tablets
- ✅ WebMIDI: Chrome, Edge (Firefox requer flag)
- ⚠️ Requer internet (CDNs e YouTube)

## 🚀 Instalação

### Opção 1: Direto no Navegador
```bash
# Abra index.html
# Não requer servidor!
```

### Opção 2: Servidor Local
```bash
# Python
python -m http.server 8000

# Node.js
npx http-server

# Acesse: http://localhost:8000
```

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
      "source": "manual"
    }
  ],
  "prompts": "Dicas...",
  "createdAt": "2025-01-27T..."
}
```

### Notas (CSV)
```csv
Nota,Oitava,Tempo Início (s),Duração (s),Cor,Fonte
C,4,5.20,0.5,#90EE90,manual
D,4,5.80,0.5,#87CEEB,transcription
```

## 🎵 Roadmap Futuro

- [ ] Integração completa com Basic Pitch
- [ ] Suporte a múltiplas mãos
- [ ] Reconhecimento de acordes
- [ ] Exportação de vídeo com notas
- [ ] Modo multi-jogador
- [ ] Biblioteca de músicas
- [ ] App mobile
- [ ] Detecção de pedal
- [ ] Score following avançado

## 🔐 Licenças

Todas as bibliotecas são open-source:

- **VexFlow:** MIT ✅
- **WebMIDI.js:** MIT ✅
- **Basic Pitch:** Apache 2.0 ✅
- **Magenta:** Apache 2.0 ✅
- **YouTube IFrame API:** ToS do YouTube

## 🤝 Contribuindo

- Reportar bugs via Issues
- Sugerir funcionalidades
- Fork e pull requests
- Melhorar documentação

## 💖 Desenvolvido com Amor

Este projeto democratiza o aprendizado de piano/teclado através de tecnologia open-source e IA.

**Esperamos que este tutor ajude você a:**
- Criar tutoriais musicais incríveis
- Aprender piano de forma visual
- Melhorar técnica com feedback real
- Compartilhar conhecimento musical

---

**Desenvolvido com ❤️ para educadores e estudantes de música**

🎹 *"A música é a linguagem universal da humanidade"* - Henry Wadsworth Longfellow
