# Rosbag2 Playback QoS Analysis

## Scenario

You have a rosbag2 file recorded with the following metadata:

```yaml
rosbag2_bagfile_information:
  version: 8
  storage_identifier: mcap
  duration:
    nanoseconds: 300000000000
  message_count: 50000
  topics_with_message_count:
    - topic_metadata:
        name: /map
        type: nav_msgs/msg/OccupancyGrid
        serialization_format: cdr
        offered_qos_profiles: |
          - reliability: reliable
            durability: transient_local
            history: keep_last
            depth: 1
      message_count: 5
    - topic_metadata:
        name: /scan
        type: sensor_msgs/msg/LaserScan
        serialization_format: cdr
        offered_qos_profiles: |
          - reliability: best_effort
            durability: volatile
            history: keep_last
            depth: 5
      message_count: 49995
```

## Question

Analyze the playback compatibility of this bag file. What issues will arise
when replaying with `ros2 bag play`? How should subscribers be configured
to receive all topics correctly?
