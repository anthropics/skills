# Perfetto Queries Reference

Use this file for the full SQL bodies referenced by `android-perfetto-skill/SKILL.md`. Keep execution order and interpretation rules in the skill, and use this file only for the concrete queries.

## Process resolution

Run these in order and stop at the first successful match.

### Direct process-name match

```sql
SELECT upid
FROM process
WHERE name = '${RUNNING_APP_ID}';
```

### Suffix match

```sql
SELECT upid
FROM process
WHERE name LIKE '%${APP_SUFFIX}%';
```

`APP_SUFFIX` is usually the last two package segments, for example `app.debug`.

### Thread-name match for cold-start traces

```sql
SELECT DISTINCT t.upid
FROM thread t
JOIN process p ON t.upid = p.upid
WHERE t.name LIKE '%${APP_SUFFIX}%'
  AND p.name = '<pre-initialized>'
LIMIT 1;
```

### UID match through package list

```sql
SELECT uid
FROM package_list
WHERE package_name = '${RUNNING_APP_ID}';
```

If a UID is returned, resolve the process with:

```sql
SELECT upid
FROM process
WHERE uid = ${UID};
```

## DEX compilation state

```sql
SELECT s.name,
       ROUND(SUM(s.dur) / 1e6, 2) AS total_ms,
       COUNT(*) AS count
FROM slice s
JOIN thread_track tt ON s.track_id = tt.id
JOIN thread t ON tt.utid = t.utid
WHERE t.upid = ${TARGET_UPID}
  AND (
    s.name LIKE 'Extract dex file%'
    OR s.name LIKE 'Verify dex file%'
    OR s.name LIKE 'VerifyClass%'
  )
GROUP BY s.name
ORDER BY total_ms DESC
LIMIT 10;
```

## Perfetto modules

Run these before steps that depend on derived Perfetto tables:

```sql
INCLUDE PERFETTO MODULE android.binder;
INCLUDE PERFETTO MODULE android.anrs;
```

If a table is still missing after `INCLUDE`, the corresponding data source was not captured.

## Frame performance

### App-attributed frame timeline

```sql
SELECT jank_type,
       COUNT(*) AS frame_count,
       ROUND(AVG(dur) / 1e6, 2) AS avg_ms,
       ROUND(MAX(dur) / 1e6, 2) AS max_ms
FROM actual_frame_timeline_slice
WHERE upid = ${TARGET_UPID}
GROUP BY jank_type
ORDER BY frame_count DESC, max_ms DESC;
```

### Worst app-attributed frames

```sql
SELECT ROUND(ts / 1e9, 3) AS ts_s,
       ROUND(dur / 1e6, 2) AS frame_ms,
       jank_type,
       present_type
FROM actual_frame_timeline_slice
WHERE upid = ${TARGET_UPID}
ORDER BY dur DESC
LIMIT 20;
```

### Expected-frame fallback

```sql
SELECT COUNT(*) AS frame_count
FROM expected_frame_timeline_slice
WHERE upid = ${TARGET_UPID};
```

### Adjusted-jank numerator

```sql
SELECT COUNT(*) AS adjusted_janky_frames
FROM actual_frame_timeline_slice
WHERE upid = ${TARGET_UPID}
  AND jank_type LIKE '%App Deadline Missed%';
```

### Raw-jank numerator

```sql
SELECT COUNT(*) AS raw_janky_frames
FROM actual_frame_timeline_slice
WHERE upid = ${TARGET_UPID}
  AND jank_type != 'None';
```

### Total usable frames

```sql
SELECT COUNT(*) AS total_frames
FROM actual_frame_timeline_slice
WHERE upid = ${TARGET_UPID};
```

## Startup timeline

```sql
SELECT s.name,
       ROUND(s.dur / 1e6, 2) AS duration_ms,
       ROUND(s.ts / 1e9, 3) AS timestamp_s,
       s.depth,
       s.parent_id
FROM slice s
JOIN thread_track tt ON s.track_id = tt.id
JOIN thread t ON tt.utid = t.utid
WHERE t.upid = ${TARGET_UPID}
  AND (
    s.name LIKE '%ActivityThreadMain%'
    OR s.name LIKE '%bindApplication%'
    OR s.name LIKE '%makeApplication%'
    OR s.name LIKE '%app.onCreate%'
    OR s.name LIKE '%activityStart%'
    OR s.name LIKE '%performCreate%'
    OR s.name LIKE '%activityResume%'
    OR s.name LIKE '%Choreographer#doFrame%'
    OR s.name LIKE '%reportFullyDrawn%'
    OR s.name LIKE '%inflate%'
    OR s.name LIKE '%traversal%'
    OR s.name LIKE '%layout%'
    OR s.name LIKE '%Verify dex file%'
    OR s.name LIKE '%Extract dex file%'
    OR s.name LIKE '%VerifyClass%'
    OR s.name LIKE '%ContentProvider%'
  )
ORDER BY s.ts ASC, s.depth ASC;
```

## Main-thread hotspots

```sql
SELECT s.name,
       ROUND(SUM(s.dur) / 1e6, 2) AS total_ms,
       ROUND(MAX(s.dur) / 1e6, 2) AS max_ms,
       COUNT(*) AS occurrences
FROM slice s
JOIN thread_track tt ON s.track_id = tt.id
JOIN thread t ON tt.utid = t.utid
WHERE t.upid = ${TARGET_UPID}
  AND t.is_main_thread = 1
  AND s.dur > 5000000
GROUP BY s.name
ORDER BY total_ms DESC
LIMIT 25;
```

## ANR detection

### ANR rows

```sql
SELECT *
FROM android_anrs
WHERE upid = ${TARGET_UPID};
```

### Main-thread prerequisite

Resolve `${MAIN_THREAD_UTID}` with:

```sql
SELECT utid
FROM thread
WHERE upid = ${TARGET_UPID}
  AND is_main_thread = 1
LIMIT 1;
```

### ANR-window prerequisite

Derive `${WINDOW_START_TS}` and `${WINDOW_END_TS}` from the ANR row you are investigating. For example, start with the ANR timestamp and inspect a window around it:

```sql
SELECT ts,
       ts - 5000000000 AS window_start_ts,
       ts + 5000000000 AS window_end_ts
FROM android_anrs
WHERE upid = ${TARGET_UPID}
ORDER BY ts DESC
LIMIT 1;
```

### Main-thread state around an ANR window

```sql
SELECT ROUND(ts / 1e9, 3) AS ts_s,
       ROUND(dur / 1e6, 2) AS dur_ms,
       state,
       blocked_function
FROM thread_state
WHERE utid = ${MAIN_THREAD_UTID}
  AND ts BETWEEN ${WINDOW_START_TS} AND ${WINDOW_END_TS}
ORDER BY ts;
```

### Scheduler slices around an ANR window

```sql
SELECT ROUND(ts / 1e9, 3) AS ts_s,
       ROUND(dur / 1e6, 2) AS dur_ms,
       cpu,
       end_state
FROM sched_slice
WHERE utid = ${MAIN_THREAD_UTID}
  AND ts BETWEEN ${WINDOW_START_TS} AND ${WINDOW_END_TS}
ORDER BY ts;
```

## Memory RSS

### RSS time series

```sql
SELECT ROUND(c.ts / 1e9, 3) AS timestamp_s,
       ROUND(c.value / 1e6, 2) AS rss_mb
FROM counter c
JOIN process_counter_track ct ON c.track_id = ct.id
WHERE ct.upid = ${TARGET_UPID}
  AND ct.name = 'mem.rss'
ORDER BY c.ts;
```

### Peak RSS

```sql
SELECT ROUND(MAX(c.value) / 1e6, 2) AS peak_rss_mb
FROM counter c
JOIN process_counter_track ct ON c.track_id = ct.id
WHERE ct.upid = ${TARGET_UPID}
  AND ct.name = 'mem.rss';
```

## GC pressure

```sql
SELECT s.name AS gc_type,
       COUNT(*) AS count,
       ROUND(SUM(s.dur) / 1e6, 2) AS total_ms,
       ROUND(AVG(s.dur) / 1e6, 2) AS avg_ms,
       ROUND(MAX(s.dur) / 1e6, 2) AS max_ms
FROM slice s
JOIN thread_track tt ON s.track_id = tt.id
JOIN thread t ON tt.utid = t.utid
WHERE t.upid = ${TARGET_UPID}
  AND (
    s.name LIKE '%concurrent%GC%'
    OR s.name LIKE '%Background%GC%'
    OR s.name LIKE '%young%GC%'
    OR s.name LIKE '%explicit%GC%'
    OR s.name LIKE '%alloc%GC%'
  )
GROUP BY s.name
ORDER BY total_ms DESC;
```

## CPU per thread

```sql
SELECT t.name AS thread_name,
       ROUND(SUM(ss.dur) / 1e6, 2) AS runtime_ms,
       COUNT(*) AS schedules,
       ROUND(MAX(ss.dur) / 1e6, 2) AS max_slice_ms
FROM sched_slice ss
JOIN thread t ON ss.utid = t.utid
WHERE t.upid = ${TARGET_UPID}
GROUP BY t.name
ORDER BY runtime_ms DESC
LIMIT 20;
```

## Thread contention

### Raw contention events

```sql
SELECT s.name,
       ROUND(s.dur / 1e6, 2) AS duration_ms,
       t.name AS thread_name
FROM slice s
JOIN thread_track tt ON s.track_id = tt.id
JOIN thread t ON tt.utid = t.utid
WHERE t.upid = ${TARGET_UPID}
  AND s.name LIKE '%monitor_contention%'
ORDER BY s.dur DESC
LIMIT 50;
```

### Grouped contention by root cause

```sql
SELECT s.name AS root_cause,
       COUNT(*) AS events,
       ROUND(SUM(s.dur) / 1e6, 2) AS total_blocked_ms,
       ROUND(MAX(s.dur) / 1e6, 2) AS max_blocked_ms
FROM slice s
JOIN thread_track tt ON s.track_id = tt.id
JOIN thread t ON tt.utid = t.utid
WHERE t.upid = ${TARGET_UPID}
  AND s.name LIKE '%monitor_contention%'
GROUP BY s.name
ORDER BY total_blocked_ms DESC
LIMIT 20;
```

## Binder IPC

```sql
SELECT client_process,
       server_process,
       ROUND(client_dur / 1e6, 2) AS duration_ms,
       client_thread
FROM android_binder_txns
WHERE client_upid = ${TARGET_UPID}
  AND client_dur > 5000000
ORDER BY client_dur DESC
LIMIT 15;
```

## RenderThread check

```sql
SELECT s.name,
       ROUND(s.dur / 1e6, 2) AS duration_ms
FROM slice s
JOIN thread_track tt ON s.track_id = tt.id
JOIN thread t ON tt.utid = t.utid
WHERE t.upid = ${TARGET_UPID}
  AND t.name = 'RenderThread'
  AND s.dur > 1000000
ORDER BY s.dur DESC
LIMIT 15;
```
