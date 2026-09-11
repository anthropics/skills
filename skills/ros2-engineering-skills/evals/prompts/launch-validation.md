# Launch File Review

## Scenario

Review the following ROS 2 launch file for issues:

```python
from launch import LaunchDescription
from launch_ros.actions import Node

def create_nodes():
    return LaunchDescription([
        Node(
            package='my_robot',
            node_executable='camera_driver',
            node_name='camera',
            node_namespace='/sensors',
            parameters=['/home/user/catkin_ws/config/camera.yaml'],
            output='screen',
        ),
        Node(
            package='my_robot',
            executable='lidar_driver',
            name='camera',
            output='screen',
        ),
    ])
```

## Question

Identify all issues in this launch file. Categorize each as error, warning, or info.
Provide the corrected version.
