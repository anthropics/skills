---
name: audio-transcriber
description: "Transcribes audio/video/YouTube to professional Markdown with speaker diarization and visual context detection. Accepts local files (MP3, MP4, WAV, M4A, etc.) or YouTube links. For YouTube, uses MCP youtube-transcript for instant captions; if unavailable, downloads audio with yt-dlp. For local files, uses MLX Whisper (Apple Silicon GPU) + SpeechBrain for lightweight diarization. Automatically detects moments where speakers reference visual elements (demos, screens, slides) and allows on-demand frame extraction via FFmpeg for analysis with Claude. Supports model selection (tiny/base/small/medium). Generates meeting minutes automatically."
license: Complete terms in LICENSE.txt
---

## Purpose

Transcreve áudios, vídeos e vídeos do YouTube para texto em Markdown profissional com:
- **YouTube** — extrai transcrição/legendas instantaneamente via MCP `youtube-transcript` (sem baixar vídeo)
- **Transcrição local otimizada para Apple Silicon** via MLX Whisper (GPU/Neural Engine do Mac)
- **Diarização leve** via SpeechBrain ECAPA-TDNN (identificação de locutores sem HuggingFace token)
- **Identificação interativa de locutores** — após diarizar, pergunta ao usuário quem é cada SPEAKER
- Metadados ricos (duração, idioma, locutores, timestamps)
- **Detecção de contexto visual** — identifica momentos onde locutores referenciam elementos visuais (telas, cliques, slides, demos) e marca timestamps para extração de frames sob demanda
- Geração de ata/resumo via LLM

## When to Use

Invoke this skill when:

- User needs to transcribe audio/video files to text
- User shares a **YouTube link** and wants the transcript/transcription
- User wants meeting minutes automatically generated from recordings
- User requires speaker identification (diarization) in conversations
- User wants executive summaries of long audio content
- User asks variations of "transcribe this audio", "convert audio to text", "generate meeting notes from recording", "transcrever vídeo", "tirar texto do áudio", "gerar ata", "quem fala no áudio", "transcrever esse vídeo do YouTube", "pega a transcrição desse link"
- User has audio files in common formats (MP3, MP4, WAV, M4A, OGG, FLAC, WEBM)
- User has YouTube URLs (youtube.com, youtu.be)
- User wants to understand what was being shown/demonstrated during a video call or screen share
- User asks to "extract frames", "show what they were looking at", "visual context" from a video transcription

## Fontes de Entrada

| Fonte | Método | Velocidade | Requisitos |
|-------|--------|-----------|------------|
| **YouTube URL** | MCP `youtube-transcript` (legendas) | **Instantâneo** | MCP instalado |
| **YouTube URL (sem legenda)** | `yt-dlp` + MLX Whisper | Moderado | `yt-dlp` instalado |
| **Arquivo local (áudio)** | MLX Whisper + SpeechBrain | Rápido | Dependências Python |
| **Arquivo local (vídeo)** | MLX Whisper + SpeechBrain + Visual Cues | Rápido | Dependências Python + FFmpeg |

## Engines (Priority Order)

| Engine | Plataforma | Diarização | Velocidade | Instalação |
|--------|-----------|-----------|------------|------------|
| **MCP youtube-transcript** | Qualquer | Não nativa | Instantâneo | `claude mcp add youtube-transcript -- npx -y @sinco-lab/mcp-youtube-transcript` |
| **MLX Whisper** (padrão) | Apple Silicon | Via SpeechBrain | Muito rápido | `pip install mlx-whisper` |
| WhisperX | Qualquer (CPU/GPU) | Via pyannote | Moderado | `pip install whisperx` |
| Faster-Whisper | Qualquer | Não nativa | Rápido | `pip install faster-whisper` |
| Whisper | Qualquer | Não nativa | Baseline | `pip install openai-whisper` |

## Modelos Disponíveis (MLX Whisper)

| Modelo | Tamanho | RAM necessária | Qualidade | Repo HuggingFace |
|--------|---------|---------------|-----------|-------------------|
| `tiny` | ~75 MB | ~500 MB | Básica | `mlx-community/whisper-tiny-mlx` |
| `base` | ~140 MB | ~800 MB | Boa | `mlx-community/whisper-base-mlx` |
| **`small`** (padrão) | **~460 MB** | **~1.5 GB** | **Muito boa** | **`mlx-community/whisper-small-mlx`** |
| `medium` | ~1.5 GB | ~3 GB | Excelente | `mlx-community/whisper-medium-mlx` |
| `large-v3-turbo` | ~1.5 GB | ~4 GB | Superior | `mlx-community/whisper-large-v3-turbo` |

**Nota:** modelos `medium` e `large-v3-turbo` requerem Macs com 16GB+ de RAM.

## Diarização (Identificação de Locutores)

Usa **SpeechBrain ECAPA-TDNN** (~80 MB) com clustering aglomerativo:
- Não requer token do HuggingFace
- ~3 min para 85 min de áudio (CPU)
- Gera etiquetas SPEAKER_00, SPEAKER_01, etc.
- Após diarização, o skill **pergunta interativamente** ao usuário o nome de cada locutor

Dependências: `pip install speechbrain scikit-learn soundfile`

## Workflow

### Step 0: Saudação e Escolha do Modelo

**Objetivo:** Permitir que o usuário escolha o modelo de transcrição via menu interativo.

**Ações:**

1. Se o usuário passou `--model <nome>` nos argumentos, usar esse modelo diretamente (pular menu)
2. Se não especificou modelo, usar `AskUserQuestion` para apresentar as opções:

```
Usar AskUserQuestion com:
  question: "Qual modelo de transcrição usar?"
  header: "Modelo"
  options:
    - label: "small (Recomendado)"
      description: "~460 MB, ~1.5 GB RAM — Muito boa qualidade, melhor custo-benefício"
    - label: "base"
      description: "~140 MB, ~800 MB RAM — Boa qualidade, mais rápido"
    - label: "medium"
      description: "~1.5 GB, ~3 GB RAM — Excelente qualidade (requer 16GB+ RAM)"
    - label: "tiny"
      description: "~75 MB, ~500 MB RAM — Qualidade básica, o mais rápido"
```

3. O `small` deve ser a primeira opção (aparece como padrão no menu)
4. Se o usuário pediu "modelo mais simples" ou similar na mensagem original, usar `tiny` ou `base` sem perguntar

### Step Y: YouTube — Transcrição via MCP (se input for URL)

**Objetivo:** Extrair transcrição de vídeos do YouTube sem baixar o vídeo.

**Quando usar:** Se o input do usuário for um link do YouTube (youtube.com, youtu.be).

**Fluxo de decisão:**

```
Input é URL do YouTube?
  ├── SIM → Tentar MCP youtube-transcript (get_transcript)
  │     ├── Sucesso → Formatar markdown (pular Steps 1-4)
  │     │     └── Se múltiplos locutores → Diarização manual ou pedir ao usuário
  │     └── Falha (sem legendas) → Baixar áudio com yt-dlp → Seguir Steps 1-6
  └── NÃO → Seguir Steps 1-6 (arquivo local)
```

**Ações (caminho MCP):**

1. Detectar que o input é uma URL do YouTube
2. Usar a tool MCP `get_transcript` com o URL e idioma desejado:
   - Tentar primeiro com `lang: "pt"` (português)
   - Se falhar, tentar sem especificar idioma (pega a legenda padrão)
3. Se a transcrição vier com timestamps, preservá-los no markdown
4. Se o vídeo tiver múltiplos locutores e o usuário pediu identificação:
   - Perguntar ao usuário se quer diarização
   - Se sim: baixar áudio com yt-dlp, converter para WAV 16kHz, rodar SpeechBrain (Step 4)
5. Gerar markdown final (Step 6)

**Ações (fallback yt-dlp — quando MCP falhar ou não houver legendas):**

```bash
# Verificar se yt-dlp está instalado
which yt-dlp || python3 -m yt_dlp --version  # binário pode estar fora do PATH

# Tentar baixar legendas existentes primeiro (em /tmp/)
yt-dlp --write-auto-subs --sub-lang pt --skip-download --convert-subs srt -o "/tmp/youtube-sub" "URL"

# Se não houver legendas, baixar apenas o áudio (em /tmp/)
yt-dlp -x --audio-format wav --audio-quality 0 -o "/tmp/youtube-audio.%(ext)s" "URL"

# Converter para 16kHz mono (para diarização, em /tmp/)
ffmpeg -i "/tmp/youtube-audio.wav" -ar 16000 -ac 1 -f wav "/tmp/youtube-audio-16k.wav" -y
```

Após baixar o áudio, seguir o fluxo normal (Steps 3-6).

**Template de saída YouTube:**

```markdown
# Transcrição de Vídeo (YouTube)

## Metadados

| Campo | Valor |
|-------|-------|
| **Título** | {titulo_do_video} |
| **URL** | {youtube_url} |
| **Duração** | {duration} |
| **Idioma** | {language} |
| **Data** | {date} |
| **Fonte** | YouTube (legendas automáticas/manuais) |

---

## Transcrição

{conteudo_da_transcricao}
```

### Step 1: Discovery e Instalação Automática

**Objetivo:** Detectar ferramentas instaladas e instalar automaticamente as que faltam. O usuário NÃO precisa instalar nada manualmente.

**Ações:**

1. Verificar cada dependência e instalar automaticamente se faltar:

```bash
# Verificar e instalar MLX Whisper (engine principal)
python3 -c "import mlx_whisper" 2>/dev/null || pip install mlx-whisper

# Verificar e instalar SpeechBrain + dependências de diarização
python3 -c "from speechbrain.inference.speaker import EncoderClassifier" 2>/dev/null || pip install speechbrain scikit-learn soundfile

# Verificar e instalar FFmpeg (necessário para vídeo, conversão e frames)
which ffmpeg >/dev/null 2>&1 || brew install ffmpeg

# Para YouTube (se input for URL):
# yt-dlp só é necessário como fallback quando não houver legendas
which yt-dlp >/dev/null 2>&1 || pip install yt-dlp
```

2. **IMPORTANTE:** Executar as instalações silenciosamente sem perguntar ao usuário. Se alguma instalação falhar, informar o erro e sugerir correção.

3. Após instalar, verificar novamente:

```python
import mlx_whisper  # Engine de transcrição
from speechbrain.inference.speaker import EncoderClassifier  # Diarização
import shutil
ffmpeg_available = shutil.which("ffmpeg") is not None
```

### Step 2: Validar Arquivo e Extrair Metadados

**Objetivo:** Verificar arquivo, formato e duração.

**IMPORTANTE — Arquivos intermediários:**
- Todos os arquivos temporários (WAV convertido, JSONs de transcrição/diarização) devem ser gravados em `/tmp/`, NUNCA no diretório do arquivo original.
- O único arquivo que deve ser salvo no diretório do arquivo original é o **markdown final** (transcript + ata).
- Ao final do processo, **limpar todos os arquivos temporários** de `/tmp/`.

**Ações:**

1. Verificar se o arquivo existe
2. Extrair metadados via ffprobe (duração, formato, tamanho)
3. Se formato não é WAV e diarização está ativada, converter para WAV 16kHz mono **em /tmp/**:

```bash
ffmpeg -i "input.mp4" -ar 16000 -ac 1 -f wav "/tmp/input-16k.wav" -y
```

4. JSONs intermediários também em `/tmp/`:
   - `/tmp/transcription.json`
   - `/tmp/diarization.json`

### Step 3: Transcrição com MLX Whisper

**Objetivo:** Transcrever áudio usando Apple Silicon GPU.

```python
import mlx_whisper

# Mapa de modelos
MODELS = {
    "tiny": "mlx-community/whisper-tiny-mlx",
    "base": "mlx-community/whisper-base-mlx",
    "small": "mlx-community/whisper-small-mlx",
    "medium": "mlx-community/whisper-medium-mlx",
    "large": "mlx-community/whisper-large-v3-turbo",
}

result = mlx_whisper.transcribe(
    audio_file,
    path_or_hf_repo=MODELS[model_name],
    language="pt",  # ou None para auto-detect
    word_timestamps=True
)
```

### Step 4: Diarização com SpeechBrain

**Objetivo:** Identificar locutores usando embeddings + clustering.

**Método:**
1. Carregar áudio WAV 16kHz mono
2. Extrair embeddings em janelas de 3 segundos (hop de 1.5s) usando SpeechBrain ECAPA-TDNN
3. Normalizar embeddings
4. Agrupar com AgglomerativeClustering (n_clusters=5 por padrão, ou distance_threshold se desconhecido)
5. Mapear cada segmento da transcrição ao speaker mais próximo por timestamp

```python
from speechbrain.inference.speaker import EncoderClassifier
from sklearn.cluster import AgglomerativeClustering
from sklearn.preprocessing import normalize
import soundfile as sf
import torch
import numpy as np

# Carregar modelo (~80 MB)
classifier = EncoderClassifier.from_hparams(
    source="speechbrain/spkrec-ecapa-voxceleb",
    savedir="/tmp/speechbrain_spkrec"
)

# Carregar áudio WAV
signal_np, sr = sf.read("input-16k.wav")
signal = torch.tensor(signal_np, dtype=torch.float32).unsqueeze(0)

# Extrair embeddings em janelas de 3s
window_size = 3 * sr
hop_size = int(1.5 * sr)
embeddings, window_times = [], []

pos = 0
while pos + window_size < signal.shape[1]:
    chunk = signal[:, pos:pos+window_size]
    with torch.no_grad():
        emb = classifier.encode_batch(chunk)
        embeddings.append(emb.squeeze().numpy())
        window_times.append(pos / sr)
    pos += hop_size

# Clustering
emb_matrix = normalize(np.array(embeddings))
clustering = AgglomerativeClustering(n_clusters=5, metric="cosine", linkage="average")
labels = clustering.fit_predict(emb_matrix)

# Mapear speaker para cada segmento da transcrição
speaker_map = {t: f"SPEAKER_{labels[i]:02d}" for i, t in enumerate(window_times)}
for seg in segments:
    seg_mid = (seg["start"] + seg["end"]) / 2
    best_t = min(window_times, key=lambda t: abs(t - seg_mid))
    seg["speaker"] = speaker_map[best_t]
```

### Step 5: Identificação Interativa de Locutores

**Objetivo:** Perguntar ao usuário o nome real de cada locutor.

**IMPORTANTE: Este passo é OBRIGATÓRIO quando diarização está ativada.**

**Ações:**

1. Contar segmentos por speaker e mostrar um trecho representativo de cada um
2. Perguntar ao usuário usando AskUserQuestion, listando cada SPEAKER com quantidade de segmentos
3. O usuário responde com os nomes reais (ex: "SPEAKER_00 é o João, SPEAKER_01 é o Felipe")
4. Fazer find/replace de todas as etiquetas SPEAKER_XX pelos nomes reais no markdown final

**Exemplo de interação:**

```
👥 Locutores identificados:

  SPEAKER_00 (1320 segmentos) — Locutor principal
    Trecho: "...eu sou arquiteto de software, engenheiro de requisitos..."

  SPEAKER_01 (61 segmentos) — Segundo mais ativo
    Trecho: "...eu não conheço, não sei se o Prisma faz parte do Adonis..."

  SPEAKER_02 (27 segmentos)
    Trecho: "...está subindo..."

Quem é cada locutor? (ex: "SPEAKER_00 é João, SPEAKER_01 é Felipe")
```

5. Após receber os nomes, substituir no markdown:
   - `### SPEAKER_00` → `### João (Arquiteto)`
   - Nos metadados, listar participantes com nomes reais

### Step 6: Gerar Markdown Final

**Objetivo:** Criar arquivo markdown formatado com transcrição, speakers e metadados.

**Template:**

```markdown
# Transcrição de Áudio

## Metadados

| Campo | Valor |
|-------|-------|
| **Arquivo** | {filename} |
| **Duração** | {duration} |
| **Idioma** | {language} |
| **Data** | {date} |
| **Engine** | MLX Whisper (modelo: {model}) |
| **Diarização** | SpeechBrain ECAPA-TDNN |
| **Locutores** | {n_speakers} |

## Participantes

- **{nome_real_1}** ({n} segmentos) — papel/descrição
- **{nome_real_2}** ({n} segmentos)

---

## Transcrição

### {nome_real_1}

**[00:02 → 00:14]** texto do segmento...

### {nome_real_2}

**[13:01 → 13:07]** texto do segmento...
```

**Naming:** `transcript-YYYYMMDD-HHMMSS.md`

### Step 6.5: Detecção de Contexto Visual (apenas para vídeos)

**Objetivo:** Identificar momentos na transcrição onde locutores referenciam elementos visuais — telas, cliques, demos, slides, reações a algo visível — e marcar esses timestamps para possível extração de frames sob demanda.

**Quando executar:** SEMPRE que o arquivo de entrada for um **vídeo** (MP4, MOV, WEBM, MKV, AVI). NÃO executar para arquivos apenas de áudio (MP3, WAV, M4A, OGG, FLAC).

**Custo:** Zero adicional — é apenas análise de texto nos segmentos já transcritos.

**Padrões de detecção (Visual Cues):**

Os seguintes padrões indicam que o locutor está referenciando algo visual. Classificados por categoria:

| Categoria | Exemplos de padrões | Regex sugerido |
|-----------|-------------------|----------------|
| **Referência dêitica** (apontar) | "aqui", "ali", "isso aqui", "essa parte", "nessa tela", "esse botão", "esse campo" | `\b(aqui|ali|isso aqui|essa? parte|nessa? tela|essa? (botão\|campo\|menu\|aba\|página\|seção))\b` |
| **Ação de demonstração** | "cliquei aqui", "vou clicar", "tô clicando", "arrasta pra cá", "abre isso", "fecha isso", "rola pra baixo", "scrolla" | `\b(clic(ar\|ou\|a\|ando\|quei)\|arrastar?\|abr(e\|ir\|iu)\|fech(a\|ar\|ou)\|rol(a\|ar)\|scrolla)\b` |
| **Convite a observar** | "olha", "olha só", "viu?", "tá vendo?", "percebe?", "repara", "nota que", "presta atenção" | `\b(olha( só)?\|viu\?\|t[aá] vendo\|percebe\|repara\|nota que\|presta atenção)\b` |
| **Reação visual/espanto** | "vixe", "nossa", "eita", "opa", "uai", "caramba", "poxa", "puts", "ué", "ih" | `\b(vixe\|nossa\|eita\|opa\|uai\|caramba\|poxa\|puts\|u[ée]\|ih)\b` |
| **Referência a slides/apresentação** | "próximo slide", "slide anterior", "nesse slide", "na apresentação", "nesse gráfico", "nessa tabela" | `\b(pr[oó]ximo slide\|slide (anterior\|seguinte)\|nessa? (slide\|gráfico\|tabela\|imagem\|figura\|apresentação))\b` |
| **Resultado/mudança na tela** | "apareceu", "sumiu", "mudou", "carregou", "atualizou", "travou", "bugou", "quebrou", "deu erro", "funcionou" | `\b(apareceu\|sumiu\|mudou\|carregou\|atualizou\|travou\|bugou\|quebrou\|deu erro\|funcionou)\b` |
| **Navegação** | "entra em", "vai em", "acessa", "volta pra", "navega até" | `\b(entra em\|vai em\|acessa\|volta (pra\|para)\|navega)\b` |
| **Digitação/input** | "digita", "escreve", "preenche", "seleciona", "marca", "desmarca" | `\b(digit[ao]\|escreve\|preenche\|seleciona\|marca\|desmarca)\b` |

**Também detectar em inglês** (comum em reuniões técnicas):

| Categoria | Exemplos | Regex sugerido |
|-----------|----------|----------------|
| **Dêitico** | "right here", "this one", "over here", "this part" | `\b(right here\|this one\|over here\|this (part\|button\|field\|screen))\b` |
| **Demonstração** | "let me click", "I'll click", "click here", "scroll down" | `\b(click(ed\|ing)?\s*(here\|on\|this)\|scroll\s*(down\|up)\|drag)\b` |
| **Observação** | "see?", "you see", "look at", "notice", "watch this" | `\b(see\?\|you see\|look at\|notice\|watch this)\b` |
| **Reação** | "whoa", "oh", "wow", "oops", "huh" | `\b(whoa\|oh\b\|wow\|oops\|huh)\b` |

**Algoritmo:**

```python
import re

VISUAL_CUE_PATTERNS = {
    "deictic": r'\b(aqui|ali|isso aqui|essa? parte|nessa? tela|essa? (?:botão|campo|menu|aba|página|seção)|right here|this one|over here|this (?:part|button|field|screen))\b',
    "demonstration": r'\b(clic(?:ar|ou|a|ando|quei)|arrastar?|abr[eiu]r?|fech[aou]r?|rol[ao]r?|scrolla|click(?:ed|ing)?\s*(?:here|on|this)|scroll\s*(?:down|up)|drag)\b',
    "observation": r'\b(olha(?: só)?|viu\?|t[aá] vendo|percebe|repara|nota que|presta atenção|see\?|you see|look at|notice|watch this)\b',
    "reaction": r'\b(vixe|nossa|eita|opa|uai|caramba|poxa|puts|u[ée]|ih|whoa|oh\b|wow|oops|huh)\b',
    "slides": r'\b(pr[oó]ximo slide|slide (?:anterior|seguinte)|nessa? (?:slide|gráfico|tabela|imagem|figura|apresentação))\b',
    "screen_change": r'\b(apareceu|sumiu|mudou|carregou|atualizou|travou|bugou|quebrou|deu erro|funcionou)\b',
    "navigation": r'\b(entra em|vai em|acessa|volta (?:pra|para)|navega)\b',
    "input": r'\b(digit[ao]|escreve|preenche|seleciona|marca|desmarca)\b',
}

def detect_visual_cues(segments):
    """Detecta segmentos com referências visuais e retorna lista de visual cues."""
    visual_cues = []
    for seg in segments:
        text_lower = seg["text"].lower()
        matched_categories = []
        matched_words = []
        for category, pattern in VISUAL_CUE_PATTERNS.items():
            matches = re.findall(pattern, text_lower, re.IGNORECASE)
            if matches:
                matched_categories.append(category)
                matched_words.extend(matches if isinstance(matches[0], str) else [m[0] for m in matches])
        if matched_categories:
            visual_cues.append({
                "start": seg["start"],
                "end": seg["end"],
                "timestamp": format_timestamp(seg["start"]),
                "speaker": seg.get("speaker", "unknown"),
                "text": seg["text"],
                "categories": matched_categories,
                "matched_words": matched_words,
            })
    return visual_cues
```

**Saída:**

1. Adicionar marcadores inline no markdown da transcrição:

```markdown
**[00:05:23] João** 👁️
Cliquei aqui no botão de configurações e olha o que apareceu
```

O emoji 👁️ indica que esse segmento tem referência visual. É sutil e não polui a leitura.

2. Salvar metadados de visual cues em JSON separado: `visual-cues-YYYYMMDD-HHMMSS.json`

```json
{
  "source_video": "reuniao.mp4",
  "total_cues": 15,
  "cues": [
    {
      "start": 323.5,
      "end": 328.1,
      "timestamp": "00:05:23",
      "speaker": "João",
      "text": "Cliquei aqui no botão de configurações e olha o que apareceu",
      "categories": ["demonstration", "observation", "screen_change"],
      "matched_words": ["cliquei", "aqui", "olha", "apareceu"],
      "frame_extracted": false
    }
  ]
}
```

3. Ao final da transcrição, a LLM **sugere proativamente** a extração de frames ao usuário, mostrando o que detectou. Usar `AskUserQuestion` com o seguinte formato:

```
👁️ Detectei 15 momentos no vídeo onde os locutores parecem estar referenciando
algo visual na tela (demos, cliques, reações). Extrair frames nesses pontos
pode me ajudar a entender melhor o contexto da conversa.

Resumo do que encontrei:
   6x demonstração — "cliquei aqui", "vou abrir", "arrasta pra cá"
   4x referência a tela — "essa parte aqui", "nesse botão"
   3x reação/espanto — "nossa!", "vixe", "opa"
   2x mudança na tela — "apareceu", "deu erro"

Exemplos dos momentos mais relevantes:
  [00:05:23] João: "Cliquei aqui no botão de configurações e olha o que apareceu"
  [00:12:45] Maria: "Vixe, bugou! Tá vendo isso?"
  [00:18:02] João: "Entra em Plugins e seleciona esse aqui"

Quer que eu extraia frames desses momentos para entender melhor o que
estava sendo mostrado na tela?

Opções:
  1. Sim, todos os 15 momentos
  2. Só os mais importantes (demonstrações e mudanças na tela)
  3. Não, a transcrição já está boa assim
```

**Regras da sugestão:**
- Sempre mostrar a **contagem por categoria** para o usuário ter noção do volume
- Sempre mostrar **2-4 exemplos concretos** (os mais representativos, priorizando demonstration > screen_change > deictic)
- Se houver **poucos cues (≤ 3)**, sugerir extrair todos diretamente
- Se houver **muitos cues (> 20)**, sugerir o modo seletivo como padrão
- Se o arquivo for **apenas áudio** (sem vídeo), NÃO sugerir extração — apenas manter os marcadores 👁️ no markdown como informação

### Step 9: Extração e Análise de Frames Visuais (após confirmação do usuário)

**Objetivo:** Após o usuário confirmar no Step 6.5, extrair frames do vídeo nos timestamps marcados como visual cues e analisá-los com Claude para enriquecer a transcrição com contexto visual.

**Quando executar:** Quando o usuário confirmar a sugestão do Step 6.5 (opção 1 ou 2). Se o usuário escolher opção 3, pular este step.

**Pré-requisitos:**
- Arquivo de vídeo original ainda acessível
- Lista de visual cues detectados no Step 6.5
- FFmpeg instalado

**Modos de operação (baseado na resposta do usuário):**

| Resposta | Modo | Descrição |
|----------|------|-----------|
| **Opção 1 / "todos"** | Completo | Extrair frames de todos os visual cues |
| **Opção 2 / "importantes"** | Seletivo | Priorizar: demonstration > screen_change > deictic > observation. Ignorar reaction isoladas |
| **Resposta específica** | Específico | Se o usuário mencionar momentos específicos ("só o do minuto 5 e 12"), extrair apenas esses |

**Extração de frames com FFmpeg:**

Os frames devem ser salvos **SEMPRE numa pasta local** no mesmo diretório do vídeo original, para que o usuário possa conferir as imagens. A pasta segue o padrão `frames-{nome_do_video}/`.

```bash
# Criar pasta local para frames (no diretório do vídeo)
mkdir -p "/caminho/do/video/frames-reuniao/"

# Frame único — para cues simples (observation, reaction, deictic)
ffmpeg -ss 00:05:23 -i "reuniao.mp4" -frames:v 1 -q:v 2 "/caminho/do/video/frames-reuniao/frame-00-05-23.jpg" -y

# Sequência de 3 frames — para cues de ação (demonstration, screen_change, navigation, input)
# Captura antes/durante/depois para mostrar a transição
ffmpeg -ss 00:05:22 -i "reuniao.mp4" -frames:v 1 -q:v 2 "/caminho/do/video/frames-reuniao/frame-00-05-22-before.jpg" -y
ffmpeg -ss 00:05:23 -i "reuniao.mp4" -frames:v 1 -q:v 2 "/caminho/do/video/frames-reuniao/frame-00-05-23-action.jpg" -y
ffmpeg -ss 00:05:24 -i "reuniao.mp4" -frames:v 1 -q:v 2 "/caminho/do/video/frames-reuniao/frame-00-05-24-after.jpg" -y
```

**Naming da pasta:** `frames-{nome_base_do_video}/` — onde `nome_base_do_video` é o nome do arquivo sem extensão, em slug (lowercase, hífens no lugar de espaços). Exemplo: vídeo `Alinhamento Octos - 2026_03_10.mp4` → pasta `frames-alinhamento-octos/`.

**Regras de extração:**
- Categorias de **ação** (demonstration, screen_change, navigation, input) → 3 frames (antes, durante, depois — 1s de intervalo)
- Categorias **estáticas** (observation, deictic, slides, reaction) → 1 frame no timestamp exato
- **Deduplicar:** se dois cues estão a menos de 3 segundos de distância, extrair frames apenas do primeiro (evita imagens duplicadas)

**Análise com Claude:**

Após extrair os frames, usar a ferramenta Read do Claude Code para ler cada imagem (Claude é multimodal) e gerar descrição do contexto visual:

```
Para cada frame extraído:
1. Ler a imagem com Read tool
2. Analisar o que está visível na tela (UI, elementos, texto, ações)
3. Correlacionar com o texto da transcrição naquele timestamp
4. Gerar descrição contextualizada
```

**Saída — Atualização do JSON de visual cues:**

Após análise, salvar `visual-cues-YYYYMMDD-HHMMSS.json` com os resultados:

```json
{
  "source_video": "reuniao.mp4",
  "total_cues": 15,
  "extracted": 10,
  "cues": [
    {
      "start": 323.5,
      "end": 328.1,
      "timestamp": "00:05:23",
      "speaker": "João",
      "text": "Cliquei aqui no botão de configurações e olha o que apareceu",
      "categories": ["demonstration", "observation", "screen_change"],
      "matched_words": ["cliquei", "aqui", "olha", "apareceu"],
      "frame_extracted": true,
      "visual_description": "O speaker está no painel de Configurações do Figma. Na tela, é visível o menu lateral com opções de 'Geral', 'Plugins' e 'Notificações'. O cursor está sobre o botão 'Plugins'. No frame seguinte, um modal de gerenciamento de plugins aparece."
    }
  ]
}
```

**Saída — Enriquecimento do Markdown (com links de imagem para VS Code):**

SEMPRE inserir as descrições visuais inline no markdown da transcrição quando frames forem extraídos. O formato usa **links relativos** para que o VS Code (e qualquer visualizador de Markdown) renderize as imagens inline e permita clicar para abrir.

**Formato para segmentos COM frame extraído:**

```markdown
**[00:05:23]** [👁️](frames-video/frame-00-05-23-action.jpg) Cliquei aqui no botão de configurações e olha o que apareceu

> 📸 **Contexto visual:** O speaker está no painel de Configurações do Figma.
>
> ![frame-00:05:23](frames-video/frame-00-05-23-action.jpg)
> [antes](frames-video/frame-00-05-23-before.jpg) | [depois](frames-video/frame-00-05-23-after.jpg)
```

**Regras do formato:**

1. O `👁️` vira um **link clicável**: `[👁️](caminho/para/frame.jpg)` — ao clicar no VS Code, abre a imagem
2. A imagem é renderizada **inline** com `![frame-TIMESTAMP](caminho/para/frame.jpg)` dentro do blockquote
3. Para frames de ação (3 frames: before/action/after), mostrar o `action` como imagem principal e links textuais `[antes]` e `[depois]`
4. Para frames estáticos (1 frame), mostrar apenas a imagem principal sem links extras
5. **Paths relativos**: usar caminhos relativos ao diretório do markdown (ex: `frames-video/frame.jpg`), NÃO absolutos — assim funciona em qualquer máquina
6. Segmentos com `👁️` que **NÃO tiveram frame extraído** mantêm o emoji sem link: `**[00:10:00]** 👁️ texto...`

**Formato para segmentos SEM frame (apenas marcador):**

```markdown
**[00:10:00]** 👁️ Aí aqui a gente coloca as etapas.
```

**Frames ficam localmente:** Os frames são salvos SEMPRE na pasta local `frames-{video}/` no diretório do vídeo. Isso permite que o usuário confira visualmente o que a IA interpretou. Os frames NÃO são salvos em `/tmp/` — vão direto para a pasta local.

**Estrutura final de saída:**

```
/diretorio/do/video/
├── video-original.mp4
├── transcript-20260312-143000.md          (transcrição com 👁️ e 📸 inline)
├── ata-20260312-143000.md                 (ata/resumo)
├── visual-cues-20260312-143000.json       (metadados dos visual cues)
└── frames-video-original/                 (pasta com frames extraídos)
    ├── frame-00-05-22-before.jpg
    ├── frame-00-05-23-action.jpg
    ├── frame-00-05-24-after.jpg
    ├── frame-00-07-12-action.jpg
    └── ...
```

Ao final, informar ao usuário quantos frames foram salvos e onde:
```
📁 18 frames salvos em: /diretorio/do/video/frames-video-original/
   Você pode abrir a pasta para conferir as imagens que a IA analisou.
```

### Step 7: Gerar Ata/Resumo

**SEMPRE gerar a ata automaticamente** após a transcrição (não precisa perguntar ao usuário).

1. Ler a transcrição gerada
2. Usar a própria LLM (Claude) para gerar:
   - Contexto e objetivo da reunião
   - Participantes e papéis
   - Tópicos discutidos
   - Decisões tomadas
   - Ações definidas (action items)
3. Salvar como `ata-YYYYMMDD-HHMMSS.md` **no mesmo diretório do arquivo original**

### Step 8: Limpeza de Arquivos Temporários

**OBRIGATÓRIO:** Ao final de todo o processo, remover todos os arquivos intermediários:

```bash
rm -f /tmp/transcription.json /tmp/diarization.json /tmp/*-16k.wav /tmp/youtube-audio.*
```

**Regra geral de saída:**
- No diretório do arquivo original, ficam:
  - `transcript-YYYYMMDD-HHMMSS.md` (transcrição com locutores, 👁️ e 📸 inline)
  - `ata-YYYYMMDD-HHMMSS.md` (resumo/ata)
  - `visual-cues-YYYYMMDD-HHMMSS.json` (metadados de contexto visual, apenas para vídeos)
  - `frames-{video}/` (pasta com frames extraídos, quando o usuário confirmar extração)
- Tudo mais (WAV convertido, JSONs intermediários, SRT) vai para `/tmp/` e é apagado no final
- **Frames NÃO vão para `/tmp/`** — são salvos direto na pasta local para conferência do usuário

## Benchmarks (Apple M2, 8GB RAM)

Áudio de teste: ~85 min de reunião

| Engine + Modelo | Transcrição | Diarização | Total | Qualidade |
|----------------|------------|-----------|-------|-----------|
| WhisperX tiny (CPU) | ~7 min | ~84 min (pyannote) | **~91 min** | Ruim |
| MLX Whisper base (GPU) | ~5.7 min | ~3 min (SpeechBrain) | **~9 min** | Boa |
| **MLX Whisper small (GPU)** | **~6.5 min** | **~3 min (SpeechBrain)** | **~9.5 min** | **Muito boa** |

## Requisitos

```bash
# Engine principal (Apple Silicon)
pip install mlx-whisper

# Diarização leve
pip install speechbrain scikit-learn soundfile

# Conversão de formatos + extração de frames visuais (obrigatório)
brew install ffmpeg

# YouTube (transcrição via legendas)
# MCP já configurado: claude mcp add youtube-transcript -- npx -y @sinco-lab/mcp-youtube-transcript

# YouTube (fallback — baixar áudio quando não houver legendas)
pip install yt-dlp
# ou: brew install yt-dlp
```

## Fallback (não-Apple Silicon)

Se não estiver em Apple Silicon, o skill usa automaticamente:
1. WhisperX (se instalado) — com pyannote para diarização
2. Faster-Whisper
3. OpenAI Whisper

Para WhisperX com diarização, é necessário token HuggingFace:
1. Criar conta em https://huggingface.co
2. Gerar token em https://huggingface.co/settings/tokens
3. Aceitar termos em https://huggingface.co/pyannote/speaker-diarization-community-1
4. Salvar token: `echo "hf_xxx" > ~/.hftoken`
