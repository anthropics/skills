---
name: android-perfetto-skill
description: Use this skill when capturing or analyzing Android Perfetto traces for app startup, UI jank, freezes, memory, CPU scheduling, binder IPC, or ANR investigations. It guides trace capture, SQL-based analysis, run comparison, and scored reporting with conservative confidence handling.
license: LICENSE.txt
compatibility: Requires adb and trace_processor_shell. Designed for Claude Code, Codex, and other Agent Skills-compatible coding agents working in an Android project or on exported Perfetto traces.
metadata:
  author: Shaurya Jaiswal
  version: 1.0.0
---

## Prerequisites

- `adb` must be available for `capture` routes, and capture expects exactly one connected device unless the user explicitly chooses one.
- `trace_processor_shell` must be installed at `/opt/homebrew/bin/trace_processor_shell` or available via an equivalent path.
- Perfetto MCP is preferred when available, but this skill must work fully with `trace_processor_shell` fallback.
- The project should expose an Android application ID in `buildSrc/src/main/kotlin/Config.kt`, `app/build.gradle`, `app/build.gradle.kts`, or equivalent Gradle configuration.
- Prefer a release-like `profileable` variant for realistic perf runs: basic Perfetto tracing works on release builds too, while heap/deep inspection may still require `debuggable`.
- Existing and newly captured runs live under `.perf/runs/<timestamp>-<scenario>/`.

## Interaction Principles

These govern every phase of this skill.

- **Default to Autonomy:** Try to resolve targets, configurations, and commands on your own using standard Android tools. Only prompt the user if you are genuinely blocked (e.g., missing prerequisites, ambiguous targets, or failed auto-recovery).
- **Smart Fallbacks:** If an automated step fails (like launching an app), do not immediately stop. Explain the failure briefly to the user and ask them to manually perform the action (like opening the app) so you can continue the workflow. 
- **Physical interactions are the exception:** For `capture ui`, `capture freeze`, and as a last resort for `startup`, asking the user to navigate the app or reproduce an issue is expected. Wait for their confirmation before capturing.
- **Keep the user informed:** Briefly state what phase you are starting and summarize the results when moving to the next phase.

## Phase 0: Intent Message

State the intended route before doing any substantial work.

- For `capture startup`: say you will capture a cold-start trace and save a new run folder.
- For `capture ui`: say you will capture a UI-interaction trace and prompt the user during the capture window.
- For `capture freeze`: say you will capture a freeze/ANR trace and collect trace plus sidecar artifacts.
- For `analyze [path]`: say which trace or run folder you are analyzing.
- For `compare`: say which two runs you will compare.
- For `report`: say whether you will show the latest report or a trend summary.
- For `fix`: say you will read the latest report and map findings to code without auto-applying changes.
- For the default route: say you will run the startup pipeline `capture -> analyze -> report`.

**Reporting Action**: Before this phase, tell the user exactly which route you are taking. After this phase, confirm the route and the primary input you will use next.

## Phase 1: Subcommand Routing

Preserve the CLI-style subcommands exactly as behavior, but execute them through the phase routing below.

| Invocation | Route |
|----------|--------|
| `capture startup` | Phase 2 -> Phase 3 (`startup`) |
| `capture ui` | Phase 2 -> Phase 3 (`ui`) |
| `capture freeze` | Phase 2 -> Phase 3 (`freeze`) |
| `analyze [path]` | Phase 2 -> Phase 4 -> Phase 5 -> Phase 6 |
| `compare` | Phase 2 -> Phase 7 |
| `report` | Phase 2 -> Phase 9 |
| `fix` | Phase 2 -> Phase 8 |
| `default` (no argument) | Phase 2 -> Phase 3 (`startup`) -> Phase 4 -> Phase 5 -> Phase 6 -> Phase 9 |

Routing rules:

1. If the user provides a trace path or run folder, use it instead of guessing.
2. If `analyze`, `report`, or `fix` is called without a path, use the latest run folder in `.perf/runs/`.
3. `capture` routes stop after artifact collection unless the user explicitly asked for a full pipeline or used the default route.
4. `report` must remain a first-class route. Do not fold it into `analyze`.

**Reporting Action**: Before this phase, tell the user which route and scenario you selected. After this phase, tell the user which later phases will run and which ones are intentionally skipped.

## Phase 2: Discovery and Environment Validation

### Application ID detection

1. Check for Android project files (`buildSrc/src/main/kotlin/Config.kt`, `app/build.gradle.kts`, `app/build.gradle`, etc.).
2. **Directory Check:** If no Android project files are found, pause and tell the user: *"I don't see an Android codebase in this directory. Running analysis here might mean missing out on mapping performance findings back to your code. Should I proceed anyway, or do you want to change directories first?"* Wait for their decision.
3. Extract the base `applicationId` from the project files (if available). Check `buildTypes` and `productFlavors` for `applicationIdSuffix`.
4. Verify the installed package with `adb shell pm list packages` and match it to your findings.
5. Store both `${BASE_APP_ID}` (for code search) and `${RUNNING_APP_ID}` (for device commands).

### Target confirmation gate

Runs before any `capture` route. First of two mandatory user-input checkpoints. Keep it lightweight — only ask when you genuinely cannot decide.

1. **Ambiguity check** — if multiple `applicationId` candidates or installed packages match, present them and wait for the user's choice. If exactly one candidate exists, proceed and echo the resolved `${RUNNING_APP_ID}` so the user can correct you.
2. **Installation check** — verify `${RUNNING_APP_ID}` is installed via `pm list packages`. If missing, tell the user which package was expected, suggest the fix (install the build, switch device, or pick a different variant), and wait for `ready`.
3. **Scenario check** — if the user did not specify a scenario and the default route is not in use, confirm `startup`, `ui`, or `freeze` before capture.
4. Only after app identity, installation, device, and scenario are resolved, proceed to Phase 3.

### Device and tool validation

Follow the Interaction Principles: run every check yourself, describe any gap in plain English, and wait for `ready`.

1. Run `adb devices` and require exactly one connected device, unless the user explicitly chose one.
   - Zero devices: tell the user to connect via USB with USB Debugging enabled (Settings → Developer Options), or start an emulator. Also confirm they are in the Android project root (needed for `fix` and app-id detection); if not, ask them to navigate there and reply `ready`.
   - Multiple devices: list serials with model names and ask which to target.
2. Note whether the device is an emulator or physical hardware in capture metadata.
3. Confirm `adb` and `trace_processor_shell` are on PATH. If either is missing, tell the user what is missing and the one-line install or PATH fix, then wait for `ready` and re-check.
4. Create `.perf/runs/` if it does not exist.

### Launch activity resolution

For `capture startup`, resolve `${LAUNCH_ACTIVITY}` before Phase 3. For `capture ui` and `capture freeze`, resolve it too when possible so the skill can recover if the target app is not already open.

Preferred resolution order:

1. `adb shell cmd package resolve-activity --brief -c android.intent.category.LAUNCHER ${RUNNING_APP_ID} | tail -1`
2. If that fails, parse the manifest or Gradle/Android sources for the exported launcher activity.
3. If resolution is still ambiguous for `startup`, stop and tell the user in plain English that startup capture cannot proceed until a launchable activity is identified, and suggest the likely cause (no exported `LAUNCHER` intent filter, obfuscated manifest, or wrong variant). Wait for the user to reply `ready` after they confirm or adjust the target before retrying.
4. If resolution is still ambiguous for `ui` or `freeze`, note that recovery launch is unavailable and require the app to already be open on the device before capture begins.

### MCP availability probe

Before analysis, test MCP once with a trivial query such as `SELECT 1`.

- If MCP fails, set `MCP_AVAILABLE = false`, log the error once, and use `trace_processor_shell` for all subsequent analysis steps.
- If MCP succeeds, set `MCP_AVAILABLE = true` and use MCP as primary with per-step fallback only for data-specific failures.
- Do not retry MCP on every step after a connectivity failure.

### Input selection

1. For `analyze [path]`, accept either a run folder or a direct trace path.
2. For `compare`, identify the two most recent run folders unless the user provided explicit inputs.
3. For `report` and `fix`, resolve the latest analyzed run folder and its `report.md`.

**Reporting Action**: Before this phase, tell the user you are validating the package, tools, and inputs. After this phase, tell the user the resolved package name, selected device or trace, MCP/fallback mode, and run folder target. If you had to pause for user input (ambiguous variants, multiple matching packages, uninstalled target, missing device, or missing tool), state what you were waiting on and what the user confirmed once they replied `ready`.

## Phase 3: Capture

Keep scenario-specific capture commands in this file because they are short, context-critical, and easy to lose when buried in references.

### Perfetto config

Write the Perfetto config to `perfetto-config.pbtxt` in the run folder. The capture command is:

`cat perfetto-config.pbtxt | adb shell perfetto --txt -c - -o /data/misc/perfetto-traces/trace.pb`

`--txt` is required. If it is omitted, Perfetto treats the config as binary and fails with `invalid config, bailing out`. If the capture command exits non-zero or prints `invalid config` / `bailing out`, stop, report the error, and do not pull or analyze the trace.

For `startup`, treat this as the underlying Perfetto command, not a blocking foreground step. Start it asynchronously so the app can be launched while recording is already active. Save enough context to verify the capture started and later completed cleanly.

Use this config template and replace `${DURATION}` plus `${ATRACE_APPS}`:

```text
buffers { size_kb: 65536 fill_policy: RING_BUFFER }
buffers { size_kb: 8192 fill_policy: RING_BUFFER }
duration_ms: ${DURATION}

data_sources { config { name: "linux.ftrace" ftrace_config {
  ftrace_events: "sched/sched_switch"
  ftrace_events: "sched/sched_waking"
  ftrace_events: "sched/sched_blocked_reason"
  ftrace_events: "binder/binder_transaction"
  ftrace_events: "binder/binder_transaction_received"
  ftrace_events: "binder/binder_lock"
  ftrace_events: "binder/binder_locked"
  ftrace_events: "binder/binder_unlock"
  atrace_categories: "gfx"
  atrace_categories: "view"
  atrace_categories: "wm"
  atrace_categories: "am"
  atrace_categories: "dalvik"
  atrace_categories: "binder_driver"
  atrace_apps: "${ATRACE_APPS}"
} } }

data_sources { config { name: "linux.process_stats"
  process_stats_config { scan_all_processes_on_start: true proc_stats_poll_ms: 1000 }
} }

data_sources { config { name: "android.surfaceflinger.frametimeline" } }
data_sources { config { name: "android.packages_list" } }
data_sources { config { name: "android.anr" } }

data_sources { config { name: "linux.sys_stats"
  sys_stats_config { meminfo_period_ms: 1000 meminfo_counters: MEMINFO_MEM_AVAILABLE meminfo_counters: MEMINFO_SWAP_FREE vmstat_period_ms: 1000 }
} }
```

Use:

- `atrace_apps: "*"` for `startup`.
- `atrace_apps: "${RUNNING_APP_ID}"` for `ui` and `freeze`.
- Duration `20000ms` by default unless the user requested otherwise.

The config must include the data sources needed for startup, frame analysis, binder, process resolution, ANR detection, and memory tracking. Keep the authoritative query expectations aligned with [references/perfetto-queries.md](references/perfetto-queries.md).

### Startup capture

Startup capture is **normally fully automated**. The skill should launch the app itself in the standard case. Asking the user to tap the launcher usually defeats cold-start measurement and can corrupt the trace.

1. Confirm the Phase 2 target confirmation gate has passed. If it has not, return to Phase 2. Do not start capture.
2. `adb shell am force-stop ${RUNNING_APP_ID}` to guarantee a cold start.
3. Start the Perfetto capture **asynchronously** so recording is live before launch begins. Verify the capture started successfully and is still running; if startup of the capture command fails, stop and report the error. Do not continue to launch or analysis.
4. Wait roughly 2 seconds so trace collection is already stable when launch begins.
5. Launch the app yourself with `adb shell am start -W -n ${RUNNING_APP_ID}/${LAUNCH_ACTIVITY}` and save the output to `am_start_w.txt`.
6. **Launch Fallback:** If automated launch fails (for example `Error`, `does not exist`, or `Permission Denial`), abort the current startup capture attempt and tell the user the exact failure. Then ask one focused recovery question such as: *"I couldn't launch `${RUNNING_APP_ID}` automatically. Do I need a different activity name, extra flags, a setup step, or should I target a different package?"* If they prefer manual launch, make it explicit that you must retry the startup capture from the beginning so the cold start is still recorded.
7. After launch or user recovery, verify again that the target app is running and, when possible, foregrounded. If verification still fails, stop and do not capture.
8. After the launch succeeds, let the asynchronous capture run to completion before collecting artifacts.
9. After the trace completes, save `adb shell dumpsys meminfo ${RUNNING_APP_ID}` to `meminfo.txt`.
10. Pull the trace and sidecar artifacts only after the capture completed cleanly.

### UI interaction capture

UI capture requires the user to perform a real interaction inside the capture window. This is the second of two mandatory user-input checkpoints. The trace must not start until the user confirms they are ready.

1. Confirm the Phase 2 target confirmation gate has passed.
2. Verify whether the target app is already running and, when possible, foregrounded (`pidof`, `dumpsys activity`, or equivalent).
3. If it is not already running or foregrounded and `${LAUNCH_ACTIVITY}` is known, try launching it yourself with `adb shell am start -W -n ${RUNNING_APP_ID}/${LAUNCH_ACTIVITY}` and save the output. If launch fails, tell the user the exact failure and ask them to open the app and navigate to the target screen, then reply `ready`. Do not start Perfetto before that recovery step succeeds.
4. If `${LAUNCH_ACTIVITY}` is unavailable and the app is not already open, ask the user to open the app and navigate to the target screen, then reply `ready`.
5. After launch or user recovery, verify again that the target app is running and, when possible, foregrounded. If verification still fails, stop and do not capture.
6. Ask the user to confirm they are ready on the exact screen they want traced. Do not start Perfetto before they acknowledge.
7. Reset frame stats with `adb shell dumpsys gfxinfo ${RUNNING_APP_ID} reset`.
8. Start the Perfetto capture. Verify the command succeeded: zero exit code and no `invalid config` / `bailing out` in output. If capture failed, stop and report the error. Do not continue to analysis.
9. Tell the user to perform the target interaction now, during the capture window.
10. After capture completes, save `adb shell dumpsys gfxinfo ${RUNNING_APP_ID} framestats` to `gfxinfo.txt`.
11. After capture completes, save `adb shell dumpsys meminfo ${RUNNING_APP_ID}` to `meminfo.txt`.
12. Pull the trace and sidecar artifacts only after app-state verification and capture success.

### Freeze and ANR capture

Freeze capture also requires the user to be ready to reproduce the hang during the trace window. Do not start Perfetto until the user confirms.

1. Confirm the Phase 2 target confirmation gate has passed.
2. Verify whether the target app is already running and, when possible, foregrounded.
3. If it is not already running or foregrounded and `${LAUNCH_ACTIVITY}` is known, try launching it yourself with `adb shell am start -W -n ${RUNNING_APP_ID}/${LAUNCH_ACTIVITY}` and save the output. If launch fails, tell the user the exact failure and ask them to open the app, get it into the pre-freeze state, then reply `ready`.
4. If `${LAUNCH_ACTIVITY}` is unavailable and the app is not already open, ask the user to open the app, get it into the pre-freeze state, then reply `ready`.
5. After launch or user recovery, verify again that the target app is running and, when possible, foregrounded. If verification still fails, stop and do not capture.
6. Ask the user to confirm they are ready to reproduce the freeze or ANR. Do not start Perfetto before they acknowledge.
7. Start the Perfetto capture. Verify the command succeeded: zero exit code and no `invalid config` / `bailing out` in output. If capture failed, stop and report the error. Do not continue to analysis.
8. Tell the user to reproduce the freeze or hang immediately.
9. After capture completes, save `adb logcat -d` to `logcat.txt`.
10. After capture completes, save `adb shell dumpsys meminfo ${RUNNING_APP_ID}` to `meminfo.txt`.
11. Check `/data/anr/` and pull ANR artifacts when present.
12. Pull the trace and sidecar artifacts only after app-state verification and capture success.

### Artifact contract

Capture into `.perf/runs/<timestamp>-<scenario>/` using this shape:

```text
trace.perfetto-trace       # always
metadata.json              # always
perfetto-config.pbtxt      # always
meminfo.txt                # always
am_start_w.txt             # startup only
gfxinfo.txt                # ui only
logcat.txt                 # freeze only
anr/                       # freeze only, if artifacts exist
```

`metadata.json` must include timestamp, scenario, package, device model, Android version, SDK level, battery/thermal context, and important capture caveats such as USB power or throttling.

**Reporting Action**: Before this phase, tell the user what scenario you are about to capture and whether they need to interact. After this phase, tell the user where artifacts were saved, which sidecars were collected, and any obvious capture caveats.

## Phase 4: Analysis

Read the exact query sections named below from [references/perfetto-queries.md](references/perfetto-queries.md) before issuing SQL. Keep orchestration and heuristics here; keep full SQL bodies in the reference file.

### Analysis setup

1. Resolve `${TARGET_UPID}` using the ordered cascade in [references/perfetto-queries.md#process-resolution](references/perfetto-queries.md#process-resolution):
   - direct process-name match
   - suffix match using the last two package segments
   - thread-name match against `<pre-initialized>` for cold-start traces
   - UID match through `package_list`
2. If all four resolution steps return empty, stop analysis and tell the user the app process was not found in the trace.
3. Check DEX extraction and verification using [references/perfetto-queries.md#dex-compilation-state](references/perfetto-queries.md#dex-compilation-state). If DEX work is significant, flag the run as not AOT-compiled, report DEX time separately, recommend Baseline Profiles, and do not attribute that inflation to app code.
4. Load required modules using [references/perfetto-queries.md#perfetto-modules](references/perfetto-queries.md#perfetto-modules). If a required table still does not exist after `INCLUDE`, report `data source not in trace`, not `no events found`.

### Required analysis steps

1. **Frame performance**: Use [references/perfetto-queries.md#frame-performance](references/perfetto-queries.md#frame-performance).
   - If `actual_frame_timeline_slice` is empty, check expected frames and `gfxinfo.txt`.
   - If both Perfetto frame tables are empty and `gfxinfo` also shows no useful frames, mark frame analysis as `Insufficient data`.
   - If `gfxinfo` is healthy but Perfetto attribution is unavailable, use `gfxinfo` for frame-health scoring and lower causality confidence.
   - Only compute raw and adjusted jank when 30 or more usable frames exist.
   - Use adjusted jank for scoring. Do not compute adjusted jank from unrelated or system-attributed frame rows.
2. **Cold-start timeline**: For startup runs, use [references/perfetto-queries.md#startup-timeline](references/perfetto-queries.md#startup-timeline).
   - Reconstruct the timeline chronologically with nesting.
   - Include `bindApplication`, `makeApplication`, `app.onCreate`, `performCreate`, first `Choreographer#doFrame`, `reportFullyDrawn`, inflation work, content providers, and framework-specific markers when present.
   - Do not double-count child slices inside a parent slice.
3. **Main-thread hotspots**: Use [references/perfetto-queries.md#main-thread-hotspots](references/perfetto-queries.md#main-thread-hotspots).
   - Exclude obvious debug-only tooling and dev-build libraries when they are clearly unrelated to production behavior.
4. **ANR detection**: Use [references/perfetto-queries.md#anr-detection](references/perfetto-queries.md#anr-detection).
   - If ANRs are found, investigate blocked main-thread state around the ANR timestamp.
5. **Memory RSS and classification**: Use [references/perfetto-queries.md#memory-rss](references/perfetto-queries.md#memory-rss).
   - Parse `meminfo.txt` alongside RSS.
   - Distinguish startup allocation, startup allocation still in progress, and likely leak. Do not call startup allocation a leak.
6. **GC pressure**: Use [references/perfetto-queries.md#gc-pressure](references/perfetto-queries.md#gc-pressure).
   - Correlate long GC pauses with janky frames when timestamps line up.
7. **CPU per thread**: Use [references/perfetto-queries.md#cpu-per-thread](references/perfetto-queries.md#cpu-per-thread).
8. **Thread contention**: Use [references/perfetto-queries.md#thread-contention](references/perfetto-queries.md#thread-contention).
   - Group contention by root-cause lock owner. Multiple events on the same lock are one finding with repeated occurrences.
9. **Binder IPC**: Use [references/perfetto-queries.md#binder-ipc](references/perfetto-queries.md#binder-ipc).
   - Main-thread binder calls over 100ms are ANR risks.
   - Background-thread calls to `keystore2` are often TLS or credential setup; note them without over-alarming unless corroborating evidence exists.
10. **RenderThread check**: Use [references/perfetto-queries.md#renderthread-check](references/perfetto-queries.md#renderthread-check).
   - If RenderThread max work is lower than main-thread max work, the bottleneck is not GPU-bound.
   - If RenderThread dominates, switch recommendations toward overdraw, heavy animation, or complex drawing work.

### Extend beyond the checklist when evidence demands it

- If a slice name stands out, investigate it instead of ignoring it.
- If the app is Compose, Flutter, React Native, Unity, WebView-heavy, or otherwise framework-driven, include the equivalent runtime markers that better explain the behavior.
- Missing data is a finding. If `reportFullyDrawn` is absent, or ANR tables were not captured, say so explicitly.
- What is not in the trace can matter as much as what is present.

**Reporting Action**: Before this phase, tell the user which trace you are analyzing and that you are resolving the process plus running the standard analysis sequence. After this phase, tell the user the strongest findings, major missing-data caveats, and whether confidence is limited by frame attribution, DEX state, or missing data sources.

## Phase 5: Validation and Confidence

Before writing or presenting conclusions, validate capture quality:

1. The app process was found in the trace.
2. The scenario was actually captured.
   - Startup: `bindApplication` or equivalent startup markers are present.
   - UI: usable frame telemetry exists from Perfetto or healthy `gfxinfo`.
   - Freeze: a stall, ANR marker, or corroborating freeze evidence exists.
3. Trace duration is long enough for the scenario.
4. Required data sources were present, or their absence is explicitly called out.

Use only these confidence states:

- `Issue found`
- `Likely issue, low confidence`
- `No issue found`
- `Insufficient data`

False-positive guards:

- Do not compute jank percentages from fewer than 30 usable frames.
- Do not emit `0% jank` when app-attributed frame telemetry is unavailable.
- Do not treat missing tables as proof that nothing happened.
- Do not compare startup timings across runs with different DEX compilation states as direct regressions.
- Do not downgrade confidence silently. Explain why confidence is reduced.

**Reporting Action**: Before this phase, tell the user you are validating the trace and assigning confidence conservatively. After this phase, tell the user whether the run is high confidence, low confidence, or insufficient, and list the gating checks that affected that outcome.

## Phase 6: Final Report

Write the report to `.perf/runs/<run-folder>/report.md`.

Use [references/reporting.md#report-structure](references/reporting.md#report-structure) for the report shape and required sections.

Use [references/reporting.md#score-breakdown-guidance](references/reporting.md#score-breakdown-guidance) for score thresholds and denominator reduction rules.

For startup runs, use [references/reporting.md#startup-timeline-guidance](references/reporting.md#startup-timeline-guidance) so the timeline is chronological, nested, and separated into build-level versus code-level cost.

For CPU and contention sections, use [references/reporting.md#cpu-and-threading-guidance](references/reporting.md#cpu-and-threading-guidance).

For finding vocabulary, use [references/reporting.md#confidence-states](references/reporting.md#confidence-states).

Append one JSON line to `.perf/history.jsonl` using [references/reporting.md#history-append](references/reporting.md#history-append).

Required report sections:

- `Capture Quality`
- `Score Breakdown`
- `Cold Start Timeline` for startup runs
- `Frame Performance`
- `Memory`
- `GC Pressure`
- `CPU & Threading`
- `Binder IPC`
- `Additional Findings`
- `Recommendations`

**Reporting Action**: Before this phase, tell the user you are writing the final report and history entry. After this phase, tell the user where `report.md` was written, the headline score, and the top recommendations.

## Phase 7: Compare

Use [references/reporting.md#compare-guidance](references/reporting.md#compare-guidance) to compare two runs.

Comparison rules:

1. Compare individual metrics, not just headline score.
2. Call out differences in device, Android version, thermal state, scenario, app version, and DEX compilation state before labeling anything a regression.
3. If startup DEX state differs, compare only non-DEX startup portions.
4. If either startup run has fewer than 30 usable frame rows, do not compare startup jank percentages.
5. Distinguish likely noise from a real performance change.

**Reporting Action**: Before this phase, tell the user which two runs you are comparing and which compatibility checks matter most. After this phase, tell the user the key improvements, regressions, and any comparison caveats that weaken confidence.

## Phase 8: Fix

Read the latest report and map findings back to code without auto-applying changes.

Use the report plus trace evidence to search for likely source locations. Resolve the latest run folder, report path, and `${BASE_APP_ID}` via Phase 2 before beginning code search.

Use the report plus trace evidence to search for likely source locations:

- Slice names and startup markers -> search for matching methods, SDK initialization, or lifecycle hooks.
- Contention root causes -> search for the owning class, lock, or singleton access path.
- Memory findings -> search for allocation-heavy code or retained objects.
- Binder findings -> search for call sites, networking setup, keystore access, or IPC wrappers.

Preferred remediation patterns:

- Heavy `Application.onCreate` -> defer non-critical initialization.
- `runBlocking` on hot paths -> replace with suspend-based flow.
- Duplicate network clients or repeated session setup -> share client and connection state.
- Startup analytics or SDK initialization -> defer until post-first-frame.
- RecyclerView or layout cost -> flatten hierarchy, reduce bind work, prefetch, or simplify drawing.
- High JIT or DEX pressure -> recommend Baseline Profiles, code shrinking, or smaller startup surface.
- `GlobalScope` and similar lifecycle leaks -> move to lifecycle-aware scopes.
- WebView or Chromium startup on main thread -> defer creation or preload more carefully.
- DI or service-locator contention -> reduce lock serialization and startup graph work.

Do not auto-apply code changes from the `fix` route. Rank fixes by likely impact and confidence.

**Reporting Action**: Before this phase, tell the user you are mapping the latest findings to code and will return recommendations only. After this phase, tell the user the highest-impact fix candidates, where they likely live, and why they rank highest.

## Phase 9: Report View

`report` is a read-and-summarize route, not a re-analysis route.

Use [references/reporting.md#report-view-guidance](references/reporting.md#report-view-guidance) when showing the latest report or trend summary.

1. If a latest `report.md` exists, summarize its score, scenario, top findings, and major caveats.
2. If `.perf/history.jsonl` has two or more entries, show the short trend and recent delta before drilling into the latest run.
3. If there is no report yet, tell the user that no analyzed run is available and point them to `analyze` or the default route.

**Reporting Action**: Before this phase, tell the user whether you are opening the latest report or summarizing recent history. After this phase, tell the user the latest score, trend direction, and the top issues or caveats worth acting on next.

## Mandatory Rules

- You **MUST** keep the user informed before and after every significant phase. Never execute a multi-step route silently.
- You **MUST** preserve the `capture`, `analyze`, `compare`, `report`, `fix`, and default routes as distinct behaviors.
- You **MUST** read the exact reference section named for each analysis or reporting step before using it.
- You **MUST** test MCP once, fail fast on connectivity issues, and switch to durable fallback instead of retrying every step.
- You **MUST** keep scenario-specific capture flow in this file and the heavy SQL in [references/perfetto-queries.md](references/perfetto-queries.md).
- You **MUST** state when confidence is reduced and why.
- You **MUST** pass the Phase 2 target confirmation gate before any capture. Never guess a variant silently and never run analysis on an unverified target.
- For `capture startup`, attempt to launch the app yourself via `adb shell am start -W`. If it fails, you MUST ask the user to manually launch the app and wait for their confirmation rather than abandoning the trace.
- The Perfetto capture command must include `--txt`. If capture fails (non-zero exit, `invalid config`, or `bailing out` in output), stop immediately and report the error. Do not pull a pre-existing device trace and do not proceed to analysis on a failed capture.
- For `capture ui` and `capture freeze`, try to launch the app yourself when the target is not already open and `${LAUNCH_ACTIVITY}` is known. If that launch fails, ask for the user's help before proceeding to capture.
- For `capture ui` and `capture freeze`, wait for the user to confirm readiness before starting Perfetto.
- For `capture ui` and `capture freeze`, verify the target app is running and, when possible, foregrounded before starting Perfetto. If it is not, recover by launching when safe and unambiguous; otherwise stop instead of collecting a random trace.
- The two mandatory user-input checkpoints are: (1) Phase 2 target confirmation gate, and (2) readiness handshake before `ui` or `freeze` capture. Do not skip either.
- Do not call startup allocation a leak.
- Do not compute or headline jank from fewer than 30 usable frames.
- Do not emit `0% jank` when frame attribution is unavailable.
- Do not confuse `data source not in trace` with `no events found`.
- Do not attribute DEX extraction or verification time to app code.
- Do not compare startup timings across different DEX states as direct regressions.
- Do not double-count nested startup slices.
- Do not report contention event-by-event; group by root cause.
- Do not over-alarm on background binder calls to `keystore2` without corroborating evidence.
- Do not claim a GPU-bound bottleneck until RenderThread evidence supports it.
- Do not auto-apply code changes during the `fix` route.
- If something important is missing from the trace, that absence is itself a finding and should be reported explicitly.
