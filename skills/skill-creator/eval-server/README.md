# skill-creator eval dashboard

Interactive web dashboard for running Phase-3 trigger optimization on a skill.
Replaces the static `report.html` auto-refresh page with a Server-Sent Events
stream so iterations land in the browser as they complete instead of forcing
a full page reload every 5 seconds.

## Stack

- **Backend:** FastAPI + uvicorn. Spawns `run_loop()` in a thread, streams
  iteration events to subscribers over SSE.
- **Frontend:** vanilla HTML/CSS/JS. No build step. SSE consumer renders the
  results table incrementally.
- **Hosting:** [`portless`](https://github.com/portless/portless) wraps the
  uvicorn process and exposes it at `http://eval.localhost:1355` (or the
  configured proxy port).

## Run it

```bash
# from this directory
portless eval ./start.sh
```

That bootstraps `.venv`, installs `fastapi` + `uvicorn` if missing, picks an
ephemeral port, and proxies `eval.localhost` to it. Open the printed URL
(typically `http://eval.localhost:1355`).

If you don't use portless:

```bash
./start.sh
# then open http://127.0.0.1:8765
```

## Use it

1. Pick a skill from the dropdown — populated from `~/.claude/skills/*`.
2. Pick an eval set — auto-discovered from `<skill>/evals/`,
   `<skill>/resources/`, or `<skill>-workspace/`. Must be a JSON array of
   `{query, should_trigger}` objects.
3. Tune model / workers / iterations / holdout. Defaults are conservative
   (1 worker, 3 iters, 60s timeout) to match low-RAM laptops.
4. **Start.** The status pill flips to *running*. Each finished iteration
   appends a row to the live results table without reloading the page.
5. After the loop ends, **Apply best to SKILL.md** writes the winning
   description back to the real `SKILL.md` (sibling `.md.apply-backup`
   file is created first).

## Why SSE replaced the auto-refresh HTML

The legacy `generate_report.py` writes one giant HTML file to
`/tmp/skill_description_report_<skill>_<ts>.html` with `<meta refresh
content="5">`. Every 5 seconds the browser reloads the entire document.
With long iteration counts the file balloons (each iteration adds a row
× N queries × details), and the browser re-parses + re-renders all of
it on every tick. RAM and CPU climb steadily.

SSE sends per-iteration JSON deltas. The DOM is patched incrementally.
Steady-state RAM stays flat; CPU only spikes when an iteration lands.

## API surface

All endpoints are under `/api/`:

| Method | Path                            | Purpose                                  |
|--------|---------------------------------|------------------------------------------|
| GET    | `/api/health`                   | health check                             |
| GET    | `/api/skills`                   | list installed skills with previews      |
| GET    | `/api/skills/{name}`            | full description + candidate eval sets   |
| POST   | `/api/runs`                     | start a run, returns `{run_id}`          |
| GET    | `/api/runs`                     | list active + completed runs             |
| GET    | `/api/runs/{id}`                | snapshot of one run                      |
| GET    | `/api/runs/{id}/stream`         | SSE: live iteration events               |
| POST   | `/api/runs/{id}/stop`           | cooperative stop (next iteration boundary)|
| POST   | `/api/runs/{id}/apply`          | write best description back to SKILL.md  |

The SSE stream emits these event types:
- `snapshot` — full state at subscribe time
- `iteration_start` — iteration N starting
- `iteration_done` — iteration N finished, includes per-query results
- `improving` — loop is calling `improve_description.py` for next iter
- `loop_done` — final result + best description
- `error` — exception bubbled up

## Files

```
eval-server/
├── README.md              this file
├── server.py              FastAPI + SSE backend
├── start.sh               venv bootstrap + uvicorn launcher
├── requirements.txt       fastapi + uvicorn[standard]
└── static/
    ├── index.html         dashboard markup
    ├── styles.css         Anthropic-style theme (Lora/Poppins/cream)
    └── app.js             SSE client + table rendering
```
