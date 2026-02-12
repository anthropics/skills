# Model Training System

**NO subprocesses. NO Claude changing stuff on the fly. Pure Python scripts.**

## Files

| File | Purpose | Difficulty to Run |
|------|---------|-------------------|
| `session_state.json` | Persistent model memory | ✅ Ready - just JSON |
| `eval_logger.py` | Log exchanges to SQLite | ✅ Ready - `python eval_logger.py` |
| `validate_evidence_card.py` | Deterministic card validation | ✅ Ready - `python validate_evidence_card.py card.json` |
| `challenge_generator.py` | Generate adaptive prompts | ✅ Ready - `python challenge_generator.py` |
| `evidence_graph.py` | Build UID relationship graph | ✅ Ready - `python evidence_graph.py` |
| `reflection_processor.py` | Convert logs to memory | ✅ Ready - `python reflection_processor.py --export` |

## What Models Need to Run Without Digging

### ✅ Self-Contained (No External Dependencies)
- All Python scripts use standard library only
- SQLite is built into Python
- JSON parsing is built into Python
- No pip install required

### ⚠️ Needs Data Directory Setup
Create these folders once:
```
data/
├── evidence/       # Put UID-*.json files here
├── logs/           # CSV routing logs go here
└── json/           # Output JSON files
```

### ⚠️ Needs Your Evidence Cards
The scripts look for evidence cards in `data/evidence/UID-*.json`
Format: `UID-1224.json`, `UID-334.json`, etc.

## Quick Start

```bash
# 1. Test the validator
python validate_evidence_card.py path/to/UID-1224.json

# 2. Generate a challenge
python challenge_generator.py

# 3. Start logging
python eval_logger.py  # Creates test entry

# 4. Build evidence graph
python evidence_graph.py

# 5. Process reflections
python reflection_processor.py --export
```

## Integration Points

### For ollama_runner.sh (or any model runner):
1. **Before prompt**: Read `session_state.json` 
2. **After response**: Update `session_state.json` with decisions
3. **Log everything**: Call `eval_logger.log_exchange()`
4. **Validate outputs**: Call `validate_evidence_card.py`

### For inception (multi-model):
1. Worker generates → Critic reviews → Worker revises → Judge validates
2. Each model reads/writes its own `session_state_worker.json`, `session_state_critic.json`
3. All exchanges logged to same `eval_log.db`
