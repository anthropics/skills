# Stall Detection Protocol

Defines monitoring thresholds for code_runner_agent. All thresholds are user-overridable.

## Detection Types

### OUTPUT_STALL

- **What**: Monitored output files have not changed in size
- **Default threshold**: 3 consecutive checks (90 seconds at 30s interval)
- **Override**: User sets `stall_tolerance` (number of checks)
- **Exception**: Long-running single computations (e.g., large matrix operations) produce no intermediate output. If user warns "this takes a while", increase tolerance to 10 checks (5 min).
- **Action**: ADVISORY — notify user, suggest continue/kill/adjust

### METRIC_PLATEAU (training type only)

- **What**: Primary metric has stopped improving
- **Prerequisite**: User specifies `metric_file` (path to log) and `metric_key` (column/field name)
- **Default threshold**: Last 10 data points change < 0.1% relative
- **Override**: User sets `plateau_window` (data points) and `plateau_threshold` (relative change)
- **Action**: ADVISORY — show metric trend, suggest early stopping

### RESOURCE_ANOMALY

- **What**: Memory usage growing unexpectedly
- **Detection**: RSS memory via `ps aux` exceeds 3x the value recorded at process start
- **Override**: User sets `memory_multiplier_limit`
- **Action**: ADVISORY — possible memory leak, suggest investigation

### SLOW_PROGRESS (etl and simulation types)

- **What**: Experiment progressing slower than expected
- **Prerequisite**: User specifies expected total units (rows, iterations) and log format
- **Default threshold**: Actual rate < 50% of expected rate (calculated from first 10% of progress)
- **Override**: User sets `progress_rate_threshold`
- **Action**: ADVISORY — show current rate, revised ETA

### HARD_TIMEOUT

- **What**: Experiment has exceeded maximum allowed duration
- **Default**: 30 minutes
- **Override**: User sets `timeout` at PARSE step
- **Action**: MANDATORY — kill process (SIGTERM, then SIGKILL after 10s), collect stderr, report

## Check Interval

- Default: every 30 seconds
- Override: User sets `check_interval_seconds`
- Minimum: 10 seconds (to avoid excessive polling overhead)
- Maximum: 300 seconds (5 minutes — longer gaps risk missing transient failures)

## Alert Behavior

- First detection: full alert with options (continue / kill / adjust)
- Same anomaly persists after user chooses "continue": silent for 2 checks, then one reminder
- After reminder: silent until anomaly resolves or escalates
- Different anomaly: always full alert regardless of prior alerts
