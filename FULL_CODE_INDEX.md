# Complete Code Index - Piano Training Platform

## 📋 Quick Navigation

**Jump to**: [Frontend](#frontend-code) | [Backend](#backend-code) | [Documentation](#documentation) | [Configuration](#configuration)

---

## Frontend Code

### 🎮 Gamification System

#### StreakCounter.tsx
**Path**: `src/components/Gamification/StreakCounter.tsx`
**Lines**: 100
**Purpose**: Track daily practice streaks with visual feedback
**Key Features**:
- Flame intensity based on streak (cool/warm/hot/inferno)
- Best streak tracking
- Today's practice status
- Motivational messages

**Code Preview**:
```typescript
const getFlameIntensity = (streak: number) => {
  if (streak >= 30) return 'inferno';
  if (streak >= 14) return 'hot';
  if (streak >= 7) return 'warm';
  return 'cool';
};
```

#### AchievementSystem.tsx
**Path**: `src/components/Gamification/AchievementSystem.tsx`
**Lines**: 120
**Purpose**: Manage achievements and level progression
**Key Features**:
- Achievement unlocking logic
- Progress tracking
- Level calculation (100 points = 1 level)
- Visual badges

**Code Preview**:
```typescript
const getLevelProgress = () => {
  const pointsForNextLevel = level * 100;
  return Math.min((totalPoints % 100) / 100, 1);
};
```

#### Leaderboard.tsx
**Path**: `src/components/Gamification/Leaderboard.tsx`
**Lines**: 150
**Purpose**: Competitive ranking system
**Key Features**:
- Multiple timeframes (daily/weekly/monthly/all-time)
- Expandable user details
- Current user highlighting
- Rank medals (🥇🥈🥉)

**Code Preview**:
```typescript
const getRankIcon = (rank: number) => {
  switch (rank) {
    case 1: return '🥇';
    case 2: return '🥈';
    case 3: return '🥉';
    default: return `#${rank}`;
  }
};
```

#### useGamification.ts
**Path**: `src/hooks/useGamification.ts`
**Lines**: 250
**Purpose**: Gamification state management with persistence
**Key Features**:
- LocalStorage persistence
- Streak calculation
- Achievement unlocking
- Session recording

**Code Preview**:
```typescript
const recordSession = useCallback((sessionData: {
  duration: number;
  accuracy: number;
  hasErrors: boolean;
}) => {
  updateStreak();
  updateAchievementProgress('first_session', 1);
  if (sessionData.accuracy >= 95) {
    updateAchievementProgress('accuracy_master', sessionData.accuracy);
  }
}, [updateStreak, updateAchievementProgress]);
```

### 🛠️ Practice Tools

#### Metronome.tsx
**Path**: `src/components/Tools/Metronome.tsx`
**Lines**: 200
**Purpose**: Interactive metronome with audio
**Key Features**:
- BPM control (40-240)
- Multiple time signatures
- Tap tempo detection
- Web Audio API sound generation

**Code Preview**:
```typescript
const createOscillator = (frequency: number, duration: number) => {
  const osc = audioContext.createOscillator();
  const gainNode = audioContext.createGain();
  osc.frequency.value = frequency;
  osc.type = 'sine';
  gainNode.gain.setValueAtTime(0.3, audioContext.currentTime);
  osc.start(audioContext.currentTime);
  osc.stop(audioContext.currentTime + duration);
};
```

#### StudyLoop.tsx
**Path**: `src/components/Tools/StudyLoop.tsx`
**Lines**: 180
**Purpose**: Practice loop for specific measures
**Key Features**:
- Measure range selection
- Repetition counting
- Progress tracking
- Auto-pause on completion

**Code Preview**:
```typescript
const handleStartLoop = () => {
  const loopMeasures = Array.from(
    { length: loopEnd - loopStart + 1 },
    (_, i) => loopStart + i
  );
  setIsLooping(true);
  onLoopChange(loopMeasures, true);
};
```

### 🎹 MIDI Player & Practice

#### MidiPlayer.tsx
**Path**: `src/components/Player/MidiPlayer.tsx`
**Lines**: 300
**Purpose**: Full-featured MIDI playback
**Key Features**:
- Speed control (0.25x - 2x)
- Volume control
- Seek/progress bar
- Tone.js integration

**Code Preview**:
```typescript
const scheduleMidi = (midi: Midi) => {
  midi.tracks.forEach(track => {
    track.notes.forEach(note => {
      Tone.Transport.schedule((time) => {
        synth.triggerAttackRelease(
          note.name,
          note.duration,
          time,
          note.velocity
        );
      }, note.time);
    });
  });
};
```

#### PracticeMode.tsx
**Path**: `src/components/Practice/PracticeMode.tsx`
**Lines**: 400
**Purpose**: Real-time practice with feedback
**Key Features**:
- Note detection from MIDI
- Instant correct/incorrect feedback
- Combo tracking
- Grade calculation (S/A/B/C/D)
- Score statistics

**Code Preview**:
```typescript
const handleNotePlay = (note: string, velocity: number) => {
  const expectedNote = expectedNotes[currentNoteIndex.current];
  const isCorrect = expectedNote && note === expectedNote.name;

  if (isCorrect) {
    setScore(prev => ({ ...prev, correct: prev.correct + 1 }));
    setCombo(prev => prev + 1);
    setFeedback('✓ Correto!');
  } else {
    setScore(prev => ({ ...prev, incorrect: prev.incorrect + 1 }));
    setCombo(0);
    setFeedback('✗ Incorreto');
  }
};
```

### 📊 Dashboard

#### StudentDashboard.tsx
**Path**: `src/pages/StudentDashboard.tsx`
**Lines**: 250
**Purpose**: Main student interface
**Key Features**:
- Tab navigation (Progress/Tools/Community)
- Stats overview
- Session history
- Practice goals

**Code Preview**:
```typescript
const handleSessionComplete = () => {
  gamification.recordSession({
    duration: 25,
    accuracy: 0.87,
    hasErrors: true
  });
};
```

---

## Backend Code

### 🎯 Score Following & Analysis

#### score_following.py
**Path**: `backend/app/analysis/score_following.py`
**Lines**: 250
**Purpose**: Real-time score following with DTW
**Key Features**:
- MIDI score loading
- Feature extraction (pitch class vectors)
- DTW alignment
- Real-time position tracking

**Code Preview**:
```python
def align_performance(self, performance_notes: List[Dict]) -> Dict[str, Any]:
    # Extract performance features
    perf_features = self._extract_features(performance_notes)

    # Compute DTW alignment
    distance = dtw.distance(perf_features, self.score_features)
    path = dtw.warping_path(perf_features, self.score_features)

    # Convert to alignment mapping
    alignment = self._create_alignment_mapping(path, perf_onsets, score_onsets)

    return {
        'success': True,
        'alignment': alignment,
        'dtw_distance': distance
    }
```

#### metrics.py
**Path**: `backend/app/analysis/metrics.py`
**Lines**: 300
**Purpose**: Calculate performance metrics
**Key Features**:
- Onset detection (F1, precision, recall)
- Pitch accuracy
- Rhythm analysis
- Expressivity metrics

**Code Preview**:
```python
def compute_overall_assessment(self, alignment: List[Dict]) -> Dict[str, Any]:
    onset_metrics = self.compute_onset_metrics(alignment)
    pitch_metrics = self.compute_pitch_metrics(alignment)
    rhythm_metrics = self.compute_rhythm_metrics(alignment)
    expressivity_metrics = self.compute_expressivity_metrics()

    # Weighted overall score
    overall_score = (
        onset_metrics['onset_f1'] * 0.3 +
        pitch_metrics['pitch_accuracy'] * 0.3 +
        rhythm_metrics['tempo_accuracy'] * 0.25 +
        expressivity_metrics['dynamic_range'] * 0.15
    )

    return {
        'overall_score': float(overall_score),
        'performance_level': self._determine_level(overall_score),
        ...
    }
```

#### measure_analysis.py
**Path**: `backend/app/analysis/measure_analysis.py`
**Lines**: 200
**Purpose**: Measure-by-measure analysis
**Key Features**:
- Group notes by measure
- Calculate measure metrics
- Identify problem areas
- Generate practice suggestions

**Code Preview**:
```python
def get_problem_measures(self, measure_results: Dict[int, Dict],
                        threshold: float = 0.7) -> List[Dict]:
    problem_measures = []
    for measure, results in measure_results.items():
        if results['accuracy'] < threshold:
            problem_measures.append({
                'measure': measure,
                'accuracy': results['accuracy'],
                'issues': self._identify_issues(results),
                'suggestions': self._generate_suggestions(results)
            })
    return sorted(problem_measures, key=lambda x: x['accuracy'])
```

### 🌐 API Layer

#### analysis.py (endpoints)
**Path**: `backend/app/api/endpoints/analysis.py`
**Lines**: 250
**Purpose**: REST API + WebSocket for analysis
**Key Features**:
- POST /analyze - Create analysis job
- GET /analyze/{job_id} - Get results
- WebSocket /ws/realtime - Real-time following
- POST /analyze/batch - Batch processing

**Code Preview**:
```python
@router.post("/analyze", response_model=AnalysisResponse)
async def create_analysis(request: AnalysisRequest, background_tasks: BackgroundTasks):
    job_id = str(uuid.uuid4())
    analysis_jobs[job_id] = {
        "status": AnalysisStatus.PENDING,
        "created_at": datetime.utcnow(),
        "request": request.dict()
    }

    # Start async task
    analyze_performance_task.delay(
        job_id=job_id,
        score_midi_url=request.score_midi_url,
        performance_midi_url=request.performance_midi_url
    )

    return AnalysisResponse(job_id=job_id, status=AnalysisStatus.PENDING)
```

### ⚙️ Async Processing

#### tasks.py
**Path**: `backend/app/celery/tasks.py`
**Lines**: 200
**Purpose**: Celery tasks for heavy processing
**Key Features**:
- analyze_performance_task - Full analysis
- Progress tracking
- Error handling
- Result storage

**Code Preview**:
```python
@celery_app.task(bind=True, name="analyze_performance_task")
def analyze_performance_task(self, job_id: str, score_midi_url: str,
                            performance_midi_url: str):
    try:
        # Update progress
        self.update_state(state='PROCESSING', meta={'current': 20, 'total': 100})

        # Load and analyze
        score_follower = ScoreFollower(score_midi_path=score_path)
        alignment = score_follower.align_performance(performance_notes)

        # Compute metrics
        self.update_state(state='PROCESSING', meta={'current': 80, 'total': 100})
        metrics = PerformanceMetrics(score_notes, performance_notes)
        assessment = metrics.compute_overall_assessment(alignment['alignment'])

        return {'success': True, 'assessment': assessment}
    except Exception as e:
        return {'success': False, 'error': str(e)}
```

### 📦 Schemas

#### analysis.py (schemas)
**Path**: `backend/app/schemas/analysis.py`
**Lines**: 150
**Purpose**: Pydantic models for validation
**Key Features**:
- AnalysisRequest/Response
- PerformanceMetrics
- MeasureMetrics
- RealTimeUpdate

**Code Preview**:
```python
class PerformanceMetrics(BaseModel):
    overall_score: float = Field(..., description="Overall score (0-1)")
    performance_level: str = Field(..., description="Level (Expert/Advanced/...)")
    onset_metrics: Dict[str, float]
    pitch_metrics: Dict[str, float]
    rhythm_metrics: Dict[str, float]
    expressivity_metrics: Dict[str, float]
```

### 🚀 Application Entry

#### main.py
**Path**: `backend/app/main.py`
**Lines**: 70
**Purpose**: FastAPI application setup
**Key Features**:
- CORS configuration
- Router inclusion
- Health check endpoint
- Lifespan management

**Code Preview**:
```python
app = FastAPI(
    title="Music Training Platform API",
    description="Backend for Score Following & Analysis",
    version="0.1.0",
    lifespan=lifespan
)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

app.include_router(analysis.router, prefix="/api/v1/analysis", tags=["analysis"])
```

---

## Documentation

### Main Guides
- `README.md` - Project overview
- `MVP_TESTING_GUIDE.md` - Complete testing guide (2000+ lines)
- `TESTING_READINESS.md` - Feature status and libraries
- `PROJECT_STRUCTURE.md` - Detailed file structure
- `AUDIT_SUMMARY.md` - Audit priorities and checklist

### Feature Documentation
- `FEATURE_7_README.md` - Gamification & UX (3000+ lines)
- `backend/FEATURE_4_README.md` - Score Following (2500+ lines)

---

## Configuration

### Frontend
**File**: `package.json`
**Key Dependencies**:
```json
{
  "tone": "^14.7.77",
  "@tonejs/midi": "^2.0.28",
  "opensheetmusicdisplay": "^1.8.6",
  "react": "^18.2.0"
}
```

### Backend
**File**: `backend/pyproject.toml`
**Key Dependencies**:
```toml
[tool.poetry.dependencies]
fastapi = "^0.104.0"
celery = "^5.3.4"
partitura = "^1.5.0"
mir-eval = "^0.7"
librosa = "^0.10.1"
dtaidistance = "^2.3.12"
```

---

## Quick File Access

### For Security Audit
1. `backend/app/api/endpoints/analysis.py` - API security
2. `src/hooks/useGamification.ts` - LocalStorage usage
3. `backend/app/main.py` - CORS configuration

### For Performance Audit
1. `src/components/Practice/PracticeMode.tsx` - State updates
2. `backend/app/celery/tasks.py` - Async processing
3. `src/components/Player/MidiPlayer.tsx` - Audio performance

### For Functionality Audit
1. `backend/app/analysis/score_following.py` - Core algorithm
2. `src/components/Practice/PracticeMode.tsx` - User interaction
3. `backend/app/analysis/metrics.py` - Metric calculation

---

**Total Files**: 26
**Total Lines**: ~4,500
**Documentation**: ~7,500 lines
**Last Updated**: 2025-10-25
