# QoS Compatibility Analysis

## Scenario

A ROS 2 Jazzy system has the following configuration:

- **Publisher** (`/camera/image_raw`): `sensor_msgs/msg/Image`
  - Reliability: `BEST_EFFORT`
  - Durability: `VOLATILE`
  - History: `KEEP_LAST`
  - Depth: `5`

- **Subscriber** (`/camera/image_raw`): `sensor_msgs/msg/Image`
  - Reliability: `RELIABLE`
  - Durability: `VOLATILE`
  - History: `KEEP_LAST`
  - Depth: `10`

## Question

The subscriber is not receiving any messages from the publisher.
Diagnose the issue, explain why this happens at the DDS protocol level,
and provide specific fixes with code examples.
