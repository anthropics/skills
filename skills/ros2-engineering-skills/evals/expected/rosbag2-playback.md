# Expected: Rosbag2 Playback QoS Analysis

## Required Elements

### 1. Metadata Parsing
- Must identify 2 topics: `/map` and `/scan`
- Must extract QoS profiles from offered_qos_profiles
- Must note MCAP storage format (Jazzy default)

### 2. TRANSIENT_LOCAL Playback Issue
- Must warn that `/map` uses TRANSIENT_LOCAL durability
- Must explain: rosbag2 play publishes as VOLATILE by default
- Subscribers expecting TRANSIENT_LOCAL will not receive late-joined data
- Fix: use `--qos-profile-overrides-path` to set durability for `/map`

### 3. Subscriber Configuration
- `/scan` subscriber: BEST_EFFORT/VOLATILE/KEEP_LAST recommended
- `/map` subscriber: RELIABLE/TRANSIENT_LOCAL/KEEP_LAST required for latched behavior
- Must warn that mixing QoS in the same subscriber node requires careful profile configuration

### 4. Large Bag Recommendations
- Should mention `--read-ahead-queue-size` for bags with 50000+ messages
- May mention `--rate` flag for controlling playback speed
- Should note that 5-minute duration (300s) at ~167 Hz average is high-throughput

### 5. Clock Handling
- Must mention `--clock` flag for publishing /clock
- Must mention `use_sim_time` parameter for subscribers
