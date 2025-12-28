# Music Production Toolkit
## APIs, MCPs, and Tools to Augment Claude for Hit Song Production

---

## Quick Reference: The Stack

```
┌─────────────────────────────────────────────────────────────────┐
│                    HIT SONG PRODUCTION PIPELINE                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ANALYSIS          GENERATION           POST-PRODUCTION        │
│  ─────────         ──────────           ───────────────        │
│  Essentia          Suno API             LALAL.AI               │
│  (audio features)  (full songs)         (stem separation)      │
│                                                                 │
│  Librosa           Udio                 Kits.AI                │
│  (spectrograms)    (iterative beats)    (voice conversion)     │
│                                                                 │
│                    ElevenLabs           Demucs                  │
│                    (vocals/music)       (open source stems)     │
│                                                                 │
│                    Mureka               Audio-separator         │
│                    (lyrics + music)     (Python package)        │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                         MCP SERVERS                             │
│  ─────────────────────────────────────────────────────────────  │
│  MusicMCP.AI    Strudel MCP    ElevenLabs MCP    Mureka MCP    │
│  (generation)   (live coding)  (voice/music)    (lyrics+song)  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Part 1: MCP Servers (Direct Claude Integration)

These give me direct control to generate music from our conversation.

### 1. MusicMCP.AI (aimusic-mcp-tool) ⭐ RECOMMENDED
**What it does**: AI music generation through natural language
**GitHub**: https://github.com/amCharlie/aimusic-mcp-tool

```json
// Claude Desktop config
{
  "mcpServers": {
    "musicmcp": {
      "command": "npx",
      "args": ["-y", "aimusic-mcp-tool"]
    }
  }
}
```

**Capabilities**:
- Generate full songs with vocals or instrumentals
- Dual modes: "inspiration" (AI decides) and "custom" (you specify)
- Direct download links for generated music

---

### 2. ElevenLabs MCP ⭐ RECOMMENDED
**What it does**: Voice cloning, TTS, singing, full song generation
**Docs**: https://elevenlabs.io/blog/introducing-elevenlabs-mcp

```json
{
  "mcpServers": {
    "elevenlabs": {
      "command": "npx",
      "args": ["-y", "@elevenlabs/mcp-server"]
    }
  }
}
```

**Capabilities**:
- Text-to-speech in 73 languages, 420+ dialects
- Voice cloning (instant + professional)
- **Eleven Music**: Full song generation with vocals
- Whisper mode, singing, humming support
- Commercial licensing via Merlin Network & Kobalt partnerships

---

### 3. Strudel MCP Server
**What it does**: Live coding music generation & algorithmic composition
**GitHub**: https://github.com/williamzujkowski/strudel-mcp-server

**Capabilities**:
- 52 MCP tools for music creation
- Pattern generation across 8+ genres
- Music theory engine (scales, chords, progressions, euclidean rhythms)
- Live audio analysis via Web Audio API

---

### 4. Mureka MCP Server
**What it does**: Lyrics + song + background music generation
**Glama**: https://glama.ai/mcp/servers/@SkyworkAI/Mureka-mcp

**Capabilities**:
- Lyrics generation
- Full song creation
- Background/instrumental music
- 4 MCP tools available

---

### 5. YourMusic MCP
**GitHub**: https://github.com/puyue-ai/yourmusic-mcp

**Capabilities**:
- 5 MCP tools for AI music
- Auto-generates title, lyrics, and style from text descriptions

---

## Part 2: Music Generation APIs

### Tier 1: Full Song Generation

#### Suno API (Unofficial)
**Best for**: Complete songs with vocals, any genre
**GitHub**: https://github.com/gcui-art/suno-api
**Wrapper Services**: https://sunoapi.com, https://sunoapi.org

```python
# Example via wrapper
import requests

response = requests.post("https://api.sunoapi.com/generate", json={
    "prompt": "2Pac storytelling flow, violin and piano beat, raindrop ambience, female chorus hook, motivational theme",
    "style": "hip-hop",
    "instrumental": False
})
```

**Key Features**:
- V4.5 model (latest): better vocals, genre accuracy, "Personas" for consistent style
- Stems + WAV export for DAW integration
- Commercial rights included

---

#### Udio
**Best for**: Iterative refinement, radio-ready pop/hip-hop
**Website**: https://udio.com

**Key Features**:
- Iterative workflow: regenerate sections until perfect
- Best-in-class vocal realism and lyrical flow
- Strong on pop and hip-hop specifically

---

#### ElevenLabs Eleven Music
**Best for**: Human-sounding vocals on custom songs
**API Docs**: https://elevenlabs.io/docs

```python
from elevenlabs import generate_music

song = generate_music(
    prompt="Epic hip-hop track, violin strings, piano chords, rain atmosphere, powerful female chorus",
    genre="hip-hop",
    mood="triumphant",
    tempo=90
)
```

**Key Features**:
- Same vocal quality as their TTS (industry-leading)
- Real-time streaming
- Section-level editing (intro, verse, chorus)
- Commercial licensing

---

#### Soundverse API
**Best for**: Building your own music generation platform
**Docs**: https://www.soundverse.ai/blog/article/how-to-build-your-own-soundverse-suno-and-udio-with-soundverse-ai-song-generation-api

**Capabilities**:
- AI Song Generator (full tracks with vocals)
- Text to Music (instrumentals)
- Lyrics generation
- Vocal generation

---

### Tier 2: Lyrics Generation

#### Mureka
**Website**: https://www.mureka.ai
**Best for**: Lyrics + vocal synthesis together

#### TopMediai API
**Website**: https://www.topmediai.com/api/ai-music-generator-api/
**Features**: Lyric writing, customizable singer voices, reference audio input

#### Jarvis Lyrics
**Website**: https://www.jarvis-lyrics.com
**Features**: 40+ languages, specify artist/genre/topic/mood/year

---

## Part 3: Voice & Vocal Tools

### Kits.AI ⭐ HIGHLY RECOMMENDED FOR YOUR USE CASE
**Website**: https://www.kits.ai
**API Docs**: https://www.kits.ai/api

**Why this matters for you**: Convert YOUR voice (or any voice) into different AI singers

```python
# Kits.AI API example
import requests

# Voice conversion
response = requests.post("https://api.kits.ai/voice/convert",
    headers={"Authorization": "Bearer YOUR_KEY"},
    json={
        "audio_url": "your_vocal_recording.wav",
        "voice_id": "ethereal_female_001",  # From their 150+ royalty-free library
        "pitch_shift": 0
    }
)
```

**Capabilities**:
- Voice conversion (singing + speech → new voice)
- 150+ royalty-free voices (male, female, various styles)
- Custom voice cloning
- Vocal separation (extract vocals from instrumentals)
- Voice blending (mix characteristics of multiple voices)
- **Built specifically for music** (unlike ElevenLabs which started with TTS)

---

### ElevenLabs Voice Cloning
**Docs**: https://elevenlabs.io/docs/product-guides/voices/voice-cloning

**Modes**:
- **Instant Clone**: 1-2 min audio → basic clone
- **Professional Clone**: 30 min - 3 hours → captures tone shifts, emotional nuances

**2025 Features**:
- Whisper mode
- Singing, humming, controlled shouting
- Cross-lingual cloning (one voice → 73 languages)

---

### ACE Studio
**Docs**: https://docs.acestudio.ai/voice-cloning/

**Capabilities**:
- Clone voice for Vocal Synth
- Voice Changer functionality

---

## Part 4: Audio Analysis (Spotify API Replacement)

⚠️ **Important**: Spotify deprecated Audio Features & Audio Analysis APIs for new apps (Nov 2024)

### Essentia (Open Source) ⭐ RECOMMENDED
**Website**: https://essentia.upf.edu
**Docs**: https://essentia.upf.edu/documentation.html

```python
import essentia.standard as es

# Load audio
audio = es.MonoLoader(filename='song.mp3')()

# BPM detection
rhythm_extractor = es.RhythmExtractor2013(method="multifeature")
bpm, beats, beats_confidence, _, _ = rhythm_extractor(audio)

# Key detection
key_extractor = es.KeyExtractor()
key, scale, strength = key_extractor(audio)

# Full music extraction
extractor = es.MusicExtractor()
features, features_frames = extractor('song.mp3')
```

**What you get**:
- BPM & beat detection
- Key & scale detection
- Pitch/melody extraction
- Chords
- Danceability
- Dynamic complexity
- Spectral features (for ML training)
- TensorFlow model support for deep learning

---

### Librosa (Python)
**Docs**: https://librosa.org

```python
import librosa

# Load audio
y, sr = librosa.load('song.mp3')

# Mel spectrogram (for ResNet embedding extraction)
mel_spec = librosa.feature.melspectrogram(y=y, sr=sr, n_mels=256)

# Tempo
tempo, beats = librosa.beat.beat_track(y=y, sr=sr)

# Chroma features
chroma = librosa.feature.chroma_stft(y=y, sr=sr)
```

---

### Essentia.js (Browser-based)
**For web apps**: https://mtg.github.io/essentia.js/

---

## Part 5: Stem Separation

### LALAL.AI API ⭐ BEST QUALITY
**Website**: https://www.lalal.ai
**API Docs**: https://www.lalal.ai/tools-and-api/
**Business API**: https://www.lalal.ai/business-solutions/

**Separates into**:
- Vocals
- Instrumental
- Drums
- Bass
- Piano
- Electric Guitar
- Acoustic Guitar
- Synthesizer

**Neural Networks**:
- Perseus (2024) - transformer-based, best quality
- Phoenix (2022) - state-of-the-art
- Cassiopeia (2021) - reduced artifacts

---

### Demucs / python-audio-separator (Open Source)
**GitHub**: https://github.com/nomadkaraoke/python-audio-separator

```bash
pip install audio-separator[gpu]

# CLI usage
audio-separator song.mp3 --model_filename htdemucs_ft.yaml
```

```python
from audio_separator.separator import Separator

separator = Separator()
separator.load_model("htdemucs_ft")
stems = separator.separate("song.mp3")
# Returns: vocals, drums, bass, other
```

**Models**:
- `htdemucs_ft`: Best quality (vocals 10.8 SDR)
- `htdemucs_6s`: 6 stems (vocals, drums, bass, guitar, piano, other)

---

## Part 6: Complete Workflow Integration

### Option A: MCP-First Approach (Fastest)

```
1. Install MCP servers in Claude Desktop:
   - MusicMCP.AI (generation)
   - ElevenLabs MCP (vocals/music)

2. Workflow:
   You: "Create a beat with violin, piano, and rain sounds, 85 BPM, dark but triumphant"
   Claude: [Uses MusicMCP to generate instrumental]

   You: "Add a female chorus hook singing 'we rise from the ashes'"
   Claude: [Uses ElevenLabs to generate vocals]

   You: "Now analyze the audio features"
   Claude: [Uses Essentia integration to extract BPM, key, etc.]
```

---

### Option B: API Pipeline (More Control)

```python
# full_pipeline.py

from audio_separator.separator import Separator
import essentia.standard as es
import requests

class HitSongPipeline:
    def __init__(self):
        self.suno_api = "YOUR_SUNO_WRAPPER_KEY"
        self.kits_api = "YOUR_KITS_KEY"
        self.lalal_api = "YOUR_LALAL_KEY"

    def generate_beat(self, prompt, style="hip-hop"):
        """Generate instrumental using Suno"""
        response = requests.post(
            "https://api.sunoapi.com/generate",
            json={"prompt": prompt, "style": style, "instrumental": True}
        )
        return response.json()["audio_url"]

    def analyze_audio(self, audio_path):
        """Extract features using Essentia"""
        extractor = es.MusicExtractor()
        features, _ = extractor(audio_path)
        return {
            "bpm": features["rhythm.bpm"],
            "key": features["tonal.key_edma.key"],
            "scale": features["tonal.key_edma.scale"],
            "danceability": features["rhythm.danceability"]
        }

    def convert_voice(self, vocal_path, target_voice_id):
        """Convert vocals using Kits.AI"""
        response = requests.post(
            "https://api.kits.ai/voice/convert",
            headers={"Authorization": f"Bearer {self.kits_api}"},
            json={"audio_url": vocal_path, "voice_id": target_voice_id}
        )
        return response.json()["output_url"]

    def separate_stems(self, audio_path):
        """Separate stems using Demucs"""
        separator = Separator()
        separator.load_model("htdemucs_6s")
        return separator.separate(audio_path)

# Usage
pipeline = HitSongPipeline()

# 1. Generate beat
beat_url = pipeline.generate_beat(
    "dark violin melody, piano chords, rain ambience, trap drums, 85 BPM"
)

# 2. Analyze it
features = pipeline.analyze_audio("beat.mp3")
print(f"BPM: {features['bpm']}, Key: {features['key']} {features['scale']}")

# 3. Convert your vocals to ethereal female voice for chorus
chorus = pipeline.convert_voice("my_chorus_recording.wav", "ethereal_female_001")

# 4. Separate stems for mixing
stems = pipeline.separate_stems("full_mix.mp3")
```

---

## Part 7: Setup Checklist

### MCP Servers to Install

```json
// ~/.config/claude/claude_desktop_config.json (Linux)
// ~/Library/Application Support/Claude/claude_desktop_config.json (Mac)

{
  "mcpServers": {
    "musicmcp": {
      "command": "npx",
      "args": ["-y", "aimusic-mcp-tool"]
    },
    "elevenlabs": {
      "command": "npx",
      "args": ["-y", "@elevenlabs/mcp-server"],
      "env": {
        "ELEVENLABS_API_KEY": "your_key_here"
      }
    },
    "mureka": {
      "command": "npx",
      "args": ["-y", "@skyworkai/mureka-mcp"]
    }
  }
}
```

### API Keys to Get

| Service | Sign Up | Free Tier? | What For |
|---------|---------|------------|----------|
| [Suno](https://suno.com) | Via wrapper APIs | Limited | Full song generation |
| [Udio](https://udio.com) | Direct | Yes | Iterative beat refinement |
| [ElevenLabs](https://elevenlabs.io) | Direct | Yes (10k chars/mo) | Vocals, voice cloning, Eleven Music |
| [Kits.AI](https://kits.ai) | Direct | Limited | Voice conversion for singing |
| [LALAL.AI](https://lalal.ai) | Direct | 10 min free | Stem separation |
| [Mureka](https://mureka.ai) | Direct | Yes | Lyrics + music generation |

### Python Packages to Install

```bash
pip install essentia librosa audio-separator[gpu] requests
```

---

## Part 8: Your Dream Artist Stack

Based on your preferences (2Pac + Neffex + Wiz + Akon hard + Sidney Sheldon stories + KPHK beats + violins + pianos + rain + female chorus):

```
RECOMMENDED STACK:
─────────────────

BEAT GENERATION:
├── Udio (iterative refinement for that perfect KPHK-inspired beat)
└── Suno (quick full-track generation with violin/piano/rain)

VOCALS:
├── Your voice → Kits.AI → Convert to various styles
├── Female chorus → Kits.AI voice library OR ElevenLabs clone
└── ElevenLabs for any spoken word intros

LYRICS:
├── Claude (me!) for Sidney Sheldon-style narrative structure
├── Mureka for melody-matched lyrics
└── Jarvis for quick alternatives

ANALYSIS:
└── Essentia for feature extraction (feed into hit prediction model)

STEMS:
└── LALAL.AI API for professional separation

POST-PRODUCTION:
└── Export to DAW (Ableton, FL Studio, Logic) for final polish
```

---

## Sources

**Music Generation:**
- [Suno API (unofficial)](https://github.com/gcui-art/suno-api)
- [Suno Hub - Best AI Music Generators](https://suno.com/hub/best-ai-music-generator)
- [Soundverse API](https://www.soundverse.ai/blog/article/how-to-build-your-own-soundverse-suno-and-udio-with-soundverse-ai-song-generation-api)

**MCP Servers:**
- [MusicMCP.AI](https://github.com/amCharlie/aimusic-mcp-tool)
- [Strudel MCP](https://github.com/williamzujkowski/strudel-mcp-server)
- [ElevenLabs MCP](https://elevenlabs.io/blog/introducing-elevenlabs-mcp)
- [Mureka MCP](https://glama.ai/mcp/servers/@SkyworkAI/Mureka-mcp)

**Voice/Vocals:**
- [Kits.AI API](https://www.kits.ai/api)
- [ElevenLabs Voice Cloning](https://elevenlabs.io/docs/product-guides/voices/voice-cloning)
- [ACE Studio Docs](https://docs.acestudio.ai/voice-cloning/)

**Audio Analysis:**
- [Essentia](https://essentia.upf.edu/)
- [Spotify API Changes (Nov 2024)](https://developer.spotify.com/blog/2024-11-27-changes-to-the-web-api)

**Stem Separation:**
- [LALAL.AI API](https://www.lalal.ai/tools-and-api/)
- [python-audio-separator](https://github.com/nomadkaraoke/python-audio-separator)

---

*Ready to make bangers. Let's go.* 🎵
