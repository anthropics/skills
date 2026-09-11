# Expected: Lifecycle Node Design

## Required Elements

### 1. Lifecycle Node Recommendation
- Must explicitly recommend lifecycle (managed) node for hardware driver
- Must explain why: explicit resource control, predictable shutdown, error recovery

### 2. State Transition Description
Must describe the full lifecycle:
- Unconfigured -> (on_configure) -> Inactive
- Inactive -> (on_activate) -> Active
- Active -> (on_deactivate) -> Inactive
- Inactive -> (on_cleanup) -> Unconfigured
- Any -> (on_shutdown) -> Finalized
- Any -> (on_error) -> Error handling

### 3. Callback Implementations
- **on_configure**: Open serial port, validate connection, declare parameters
- **on_activate**: Start 100 Hz timer/control loop, begin publishing
- **on_deactivate**: Send zero-velocity command, stop timer (SAFETY CRITICAL)
- **on_cleanup**: Close serial port, release resources
- **on_shutdown**: Emergency stop, close port, final cleanup

### 4. Error Handling
- Must distinguish transient errors (retry with backoff) from fatal errors
- Must use `on_error` callback or transition to error state
- Must log errors at appropriate severity levels

### 5. Safe Shutdown
- MUST send zero-velocity command in on_deactivate
- Should also send zero-velocity in destructor as last resort
- Must handle case where serial port is already closed

### 6. Launch Orchestration
- Must show LifecycleNode usage in launch file
- Must include lifecycle state transitions (configure -> activate)
- Should mention lifecycle manager or launch events for automation
