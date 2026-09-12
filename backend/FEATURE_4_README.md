# Feature 4: Score Following & Avaliação

## Visão Geral

Esta feature implementa um sistema completo de análise musical e avaliação de performance, incluindo:

- **Score Following em Tempo Real** usando Dynamic Time Warping (DTW)
- **Métricas Musicais Abrangentes** (onset, pitch, ritmo, expressividade)
- **Análise por Compasso** com identificação de problemas e sugestões
- **WebSocket para Real-Time** seguimento da partitura durante performance
- **Processamento Assíncrono** com Celery para análises pesadas

## Estrutura de Arquivos

```
backend/app/
├── analysis/
│   ├── __init__.py
│   ├── score_following.py      # Score following com DTW
│   ├── metrics.py               # Cálculo de métricas musicais
│   └── measure_analysis.py      # Análise por compasso
├── schemas/
│   ├── __init__.py
│   └── analysis.py              # Schemas Pydantic para análise
├── api/
│   └── endpoints/
│       ├── __init__.py
│       └── analysis.py          # Endpoints REST e WebSocket
├── celery/
│   ├── __init__.py
│   └── tasks.py                 # Tasks assíncronas
└── main.py                      # FastAPI app principal
```

## Componentes Principais

### 1. ScoreFollower (score_following.py)

Classe responsável pelo seguimento da partitura em tempo real:

```python
from app.analysis.score_following import ScoreFollower

# Inicializar com MIDI da partitura
follower = ScoreFollower(score_midi_path="score.mid")

# Alinhamento completo
alignment = follower.align_performance(performance_notes)

# Atualização em tempo real
update = follower.update_real_time(current_notes, window_size=10)
```

**Características:**
- Extração de features musicais (pitch class vectors)
- Alinhamento usando DTW (Dynamic Time Warping)
- Tracking de posição em tempo real
- Cálculo de confiança baseado em pitch matching

### 2. PerformanceMetrics (metrics.py)

Cálculo de métricas musicais detalhadas:

```python
from app.analysis.metrics import PerformanceMetrics

metrics = PerformanceMetrics(score_notes, performance_notes)
assessment = metrics.compute_overall_assessment(alignment)
```

**Métricas Calculadas:**

#### Onset Metrics
- **F1-score**: Precisão de detecção de onsets
- **Precision/Recall**: Detecção de notas
- **Accuracy**: Precisão temporal (timing)

#### Pitch Metrics
- **Pitch Accuracy**: Notas corretas (0-1)
- **Pitch Precision**: Precisão de afinação
- **Intonation Deviation**: Desvio de afinação em semitons

#### Rhythm Metrics
- **Tempo Accuracy**: Consistência de tempo
- **Rhythmic Precision**: Correlação de IOIs (Inter-Onset Intervals)
- **Timing Consistency**: Consistência de timing

#### Expressivity Metrics
- **Dynamic Range**: Variação de dinâmica (0-1)
- **Articulation Variety**: Variedade de articulação
- **Phrasing Consistency**: Consistência de frasear

#### Overall Score
Score geral ponderado (0-1) com classificação:
- **Expert**: ≥ 0.9
- **Advanced**: ≥ 0.7
- **Intermediate**: ≥ 0.5
- **Beginner**: < 0.5

### 3. MeasureAnalyzer (measure_analysis.py)

Análise detalhada por compasso:

```python
from app.analysis.measure_analysis import MeasureAnalyzer

analyzer = MeasureAnalyzer(score_notes)
measure_results = analyzer.analyze_measure_performance(
    performance_notes,
    alignment
)

# Identificar compassos problemáticos
problems = analyzer.get_problem_measures(measure_results, threshold=0.7)
```

**Funcionalidades:**
- Agrupamento de notas por compasso
- Métricas específicas por compasso
- Identificação automática de problemas
- Sugestões de prática personalizadas

## API Endpoints

### POST /api/v1/analysis/analyze

Criar job de análise assíncrona:

```bash
curl -X POST "http://localhost:8000/api/v1/analysis/analyze" \
  -H "Content-Type: application/json" \
  -d '{
    "score_midi_url": "s3://bucket/score.mid",
    "performance_midi_url": "s3://bucket/performance.mid",
    "user_id": "user123",
    "session_id": "session456",
    "analysis_type": "full"
  }'
```

**Response:**
```json
{
  "job_id": "uuid-here",
  "status": "pending",
  "message": "Analysis job started",
  "created_at": "2025-10-25T10:00:00Z"
}
```

### GET /api/v1/analysis/analyze/{job_id}

Obter status e resultado da análise:

```bash
curl "http://localhost:8000/api/v1/analysis/analyze/uuid-here"
```

**Response (completed):**
```json
{
  "job_id": "uuid-here",
  "status": "completed",
  "performance_metrics": {
    "overall_score": 0.85,
    "performance_level": "Advanced",
    "onset_metrics": {...},
    "pitch_metrics": {...},
    "rhythm_metrics": {...},
    "expressivity_metrics": {...}
  },
  "measure_metrics": {...},
  "problem_measures": [...]
}
```

### WebSocket /api/v1/analysis/ws/realtime/{session_id}

Conexão WebSocket para score following em tempo real:

```javascript
const ws = new WebSocket('ws://localhost:8000/api/v1/analysis/ws/realtime/session123');

// Inicializar
ws.send(JSON.stringify({
  type: 'initialize',
  score_url: 'path/to/score.mid'
}));

// Enviar notas de performance
ws.send(JSON.stringify({
  type: 'performance_notes',
  notes: [
    {onset: 0.5, pitch: 60, velocity: 80, duration: 0.4},
    {onset: 1.0, pitch: 62, velocity: 75, duration: 0.3}
  ]
}));

// Receber atualizações
ws.onmessage = (event) => {
  const data = JSON.parse(event.data);
  if (data.type === 'realtime_update') {
    console.log('Current measure:', data.data.current_measure);
    console.log('Confidence:', data.data.confidence);
    console.log('Expected notes:', data.data.expected_notes);
  }
};
```

### POST /api/v1/analysis/analyze/batch

Análise em lote de múltiplas performances:

```bash
curl -X POST "http://localhost:8000/api/v1/analysis/analyze/batch" \
  -H "Content-Type: application/json" \
  -d '[
    {
      "score_midi_url": "s3://bucket/score1.mid",
      "performance_midi_url": "s3://bucket/perf1.mid"
    },
    {
      "score_midi_url": "s3://bucket/score2.mid",
      "performance_midi_url": "s3://bucket/perf2.mid"
    }
  ]'
```

### GET /api/v1/analysis/sessions/{session_id}/measures

Obter estrutura de compassos para uma sessão:

```bash
curl "http://localhost:8000/api/v1/analysis/sessions/session123/measures"
```

## Celery Tasks

### analyze_performance_task

Task assíncrona para análise completa de performance:

```python
from app.celery.tasks import analyze_performance_task

# Disparar task
result = analyze_performance_task.delay(
    job_id="uuid",
    score_midi_url="path/to/score.mid",
    performance_midi_url="path/to/performance.mid",
    analysis_type="full"
)

# Checar status
print(result.status)
print(result.info)
```

**Estados da Task:**
- `PENDING`: Aguardando processamento
- `PROCESSING`: Em processamento (com progresso 0-100)
- `SUCCESS`: Completo com sucesso
- `FAILURE`: Erro durante processamento

## Schemas Pydantic

### AnalysisRequest
```python
{
  "score_midi_url": str,
  "performance_midi_url": str,
  "user_id": Optional[str],
  "session_id": Optional[str],
  "analysis_type": str  # "full", "basic", "measures"
}
```

### AnalysisResult
```python
{
  "job_id": str,
  "status": AnalysisStatus,
  "performance_metrics": Optional[PerformanceMetrics],
  "measure_metrics": Optional[Dict[int, MeasureMetrics]],
  "problem_measures": Optional[List[Dict]],
  "alignment_data": Optional[List[Dict]]
}
```

### RealTimeUpdate
```python
{
  "current_measure": int,
  "confidence": float,
  "expected_notes": List[int],
  "played_notes": List[int],
  "timing_deviation": float,
  "position": float
}
```

## Dependências

### Core Libraries
- **partitura**: Análise de partituras MIDI/MusicXML
- **mir-eval**: Métricas de Music Information Retrieval
- **librosa**: Processamento de áudio
- **scipy**: Computação científica
- **dtaidistance**: Dynamic Time Warping

### Backend Framework
- **FastAPI**: API REST e WebSocket
- **Celery**: Tasks assíncronas
- **Redis**: Message broker e backend do Celery
- **Pydantic**: Validação de dados

### Deep Learning (Opcional)
- **torch**: PyTorch para modelos de ML
- **torchaudio**: Processamento de áudio com PyTorch

## Instalação

```bash
# Navegar para o diretório backend
cd backend

# Instalar dependências com Poetry
poetry install

# Ou com pip
pip install -r requirements.txt

# Iniciar Redis (requerido para Celery)
redis-server

# Iniciar Celery worker
celery -A app.celery worker --loglevel=info

# Iniciar FastAPI
uvicorn app.main:app --reload
```

## Exemplos de Uso

### Análise Completa

```python
import requests

# Criar job de análise
response = requests.post(
    "http://localhost:8000/api/v1/analysis/analyze",
    json={
        "score_midi_url": "path/to/score.mid",
        "performance_midi_url": "path/to/performance.mid",
        "analysis_type": "full"
    }
)
job = response.json()

# Aguardar e obter resultado
import time
while True:
    result = requests.get(
        f"http://localhost:8000/api/v1/analysis/analyze/{job['job_id']}"
    ).json()

    if result['status'] == 'completed':
        print(f"Overall Score: {result['performance_metrics']['overall_score']}")
        print(f"Level: {result['performance_metrics']['performance_level']}")
        break

    time.sleep(2)
```

### Score Following em Tempo Real

```python
import asyncio
import websockets
import json

async def realtime_analysis():
    uri = "ws://localhost:8000/api/v1/analysis/ws/realtime/my-session"

    async with websockets.connect(uri) as websocket:
        # Inicializar
        await websocket.send(json.dumps({
            "type": "initialize",
            "score_url": "path/to/score.mid"
        }))

        # Simular notas de performance
        for i in range(10):
            await websocket.send(json.dumps({
                "type": "performance_notes",
                "notes": [
                    {
                        "onset": i * 0.5,
                        "pitch": 60 + i,
                        "velocity": 80,
                        "duration": 0.4
                    }
                ]
            }))

            # Receber atualização
            response = await websocket.recv()
            data = json.loads(response)
            print(f"Measure: {data['data']['current_measure']}, "
                  f"Confidence: {data['data']['confidence']:.2f}")

            await asyncio.sleep(0.5)

asyncio.run(realtime_analysis())
```

## Testes

```bash
# Executar testes
pytest tests/test_analysis.py -v

# Com cobertura
pytest tests/test_analysis.py --cov=app.analysis --cov-report=html
```

## Próximos Passos

1. ✅ Score Following implementado
2. ✅ Métricas musicais completas
3. ✅ Análise por compasso
4. ✅ WebSocket para real-time
5. 🔄 Integração com storage service (S3/GCS)
6. 🔄 Integração com banco de dados
7. 🔄 Dashboard de visualização de métricas
8. 🔄 Feature 5: Automação n8n & Relatórios

## Referências

- [partitura Documentation](https://partitura.readthedocs.io/)
- [mir_eval Documentation](https://craffel.github.io/mir_eval/)
- [FastAPI WebSockets](https://fastapi.tiangolo.com/advanced/websockets/)
- [Celery Documentation](https://docs.celeryproject.org/)
- [DTW Algorithm](https://en.wikipedia.org/wiki/Dynamic_time_warping)
