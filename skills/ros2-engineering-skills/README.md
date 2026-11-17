# ros2-engineering-skills

Agent skill for production-grade ROS 2 development — from first workspace to fleet deployment.

Works with [Claude Code](https://code.claude.com), [Codex](https://developers.openai.com/codex), [Cursor](https://cursor.sh), [Gemini CLI](https://github.com/google-gemini/gemini-cli), and any agent supporting the [Agent Skills](https://agentskills.io) standard.

## Before / After

> **Prompt:** *"My ROS 2 subscriber isn't receiving any sensor messages. Help me fix it."*

<table>
<tr>
<th width="50%">Without this skill</th>
<th width="50%">With this skill loaded</th>
</tr>
<tr>
<td>

```python
# "Check your topic name and make sure
#  the publisher is running"
sub = node.create_subscription(
    Image, '/camera/image_raw',
    callback, 10)
```

Generic advice — misses the real issue.

</td>
<td>

```python
# Diagnoses QoS mismatch (DDS RxO rules):
# Sensor drivers default to BEST_EFFORT,
# but queue depth "10" implies RELIABLE.
from rclpy.qos import qos_profile_sensor_data

sub = node.create_subscription(
    Image, '/camera/image_raw',
    callback, qos_profile_sensor_data)
#          ^^^^^^^^^^^^^^^^^^^^^^
# BEST_EFFORT + VOLATILE — matches sensor pub
```

Identifies the root cause, explains DDS Request-vs-Offered semantics, and applies the correct `qos_profile_sensor_data` preset.

</td>
</tr>
</table>

> **Prompt:** *"Create a C++ driver package for my LiDAR sensor."*

<table>
<tr>
<th width="50%">Without this skill</th>
<th width="50%">With this skill loaded</th>
</tr>
<tr>
<td>

```
my_lidar_driver/
├── src/main.cpp          # rclcpp::Node
├── CMakeLists.txt
└── package.xml
```

Bare `Node`, no lifecycle, no tests, no launch file, `ament_target_dependencies` (deprecated in Kilted).

</td>
<td>

```
my_lidar_driver/
├── include/my_lidar_driver/
│   └── my_lidar_driver_node.hpp  # LifecycleNode
├── src/
│   ├── my_lidar_driver_node.cpp  # on_configure/activate/…
│   └── main.cpp
├── launch/bringup.launch.py      # auto-configure + activate
├── config/params.yaml
├── test/test_my_lidar_driver.cpp  # gtest
├── CMakeLists.txt                 # target_link_libraries
└── package.xml                    # format 3, Apache-2.0
```

LifecycleNode with managed transitions, launch file with auto-activation, gtest scaffolding, modern CMake (`target_link_libraries` over deprecated `ament_target_dependencies`), and distro-aware defaults.

</td>
</tr>
</table>

## What this is

A `SKILL.md`-based knowledge module that gives AI coding agents deep ROS 2 engineering expertise. Instead of a shallow cheat sheet, it provides:

- **Decision frameworks** — when to use rclcpp vs rclpy, which QoS profile, lifecycle vs plain node
- **Progressive disclosure** — compact routing in `SKILL.md`, detailed patterns in `references/`
- **Full spectrum** — workspace setup through real-time tuning, Nav2, MoveIt 2, ros2_control, DDS configuration, cross-compilation, and CI/CD
- **Distro-aware** — explicit Humble / Jazzy / Kilted / Rolling differences with migration paths
- **Anti-pattern documentation** — what breaks in production and why

## How it differs from existing ROS 2 skills

| Aspect | Typical ROS 2 skill | This project |
|---|---|---|
| Depth | Basic QoS + lifecycle intro | DDS vendor tuning, custom executors, intra-process zero-copy, type adapters |
| Scope | Single SKILL.md file | 20 reference files via progressive disclosure |
| Hardware | Mentioned in passing | ros2_control hardware interface patterns, serial/CAN/EtherCAT, controller chaining |
| Real-time | Not covered | PREEMPT_RT, realtime_tools, memory allocation, callback group strategies |
| Simulation | Mentioned in passing | Gazebo version matrix, gz_ros2_control, Isaac Sim, sim-to-real |
| Security | Not covered | SROS2, DDS security plugins, certificate management, supply chain |
| Embedded | Not covered | micro-ROS, rclc, XRCE-DDS, ESP32/STM32/RP2040 |
| Multi-robot | Not covered | Open-RMF, fleet adapters, DDS discovery at scale, NTP/PTP sync |
| Testing | "Use pytest" | launch_testing, gtest, industrial_ci, simulation-in-the-loop CI |
| Deployment | Not covered | Docker multi-stage, cross-compile, fleet OTA, Zenoh routing |

## Installation

### Claude Code
```bash
# From plugin marketplace
claude plugin marketplace add dbwls99706/ros2-engineering-skills
claude plugin install ros2-engineering@ros2-engineering-skills

# Or clone directly
git clone https://github.com/dbwls99706/ros2-engineering-skills.git ~/.claude/skills/ros2-engineering-skills
```

### Codex / Gemini CLI / OpenCode
```bash
git clone https://github.com/dbwls99706/ros2-engineering-skills.git ~/.agents/skills/ros2-engineering-skills
```

### Cursor
```bash
git clone https://github.com/dbwls99706/ros2-engineering-skills.git
# Add to .cursor/rules/ros2-engineering-skills
```

### Any project (symlink)
```bash
ln -s /path/to/ros2-engineering-skills .claude/skills/ros2-engineering-skills
```

## Structure

```
ros2-engineering-skills/
├── SKILL.md                        # Entry point — decision router + core principles
├── references/                     # 20 reference files (13,000+ lines)
│   ├── workspace-build.md          # colcon, ament_cmake, package.xml, overlays
│   ├── nodes-executors.md          # rclcpp/rclpy nodes, executors, callback groups
│   ├── communication.md            # Topics, services, actions, QoS, type adapters, DDS tuning
│   ├── lifecycle-components.md     # Managed nodes, component loading, composition
│   ├── launch-system.md            # Python launch API, conditions, events, large systems
│   ├── tf2-urdf.md                 # Transforms, URDF, xacro, robot_state_publisher
│   ├── hardware-interface.md       # ros2_control, HW interfaces, controller chaining, EtherCAT
│   ├── realtime.md                 # RT kernel, realtime_tools, jitter, deterministic execution
│   ├── navigation.md               # Nav2, SLAM, costmaps, BT navigator, collision monitor
│   ├── manipulation.md             # MoveIt 2, MTC, planning scene, grasp pipelines
│   ├── perception.md               # image_transport, PCL, cv_bridge, depth, Isaac ROS
│   ├── simulation.md               # Gazebo, Isaac Sim, gz_ros2_control, sim-to-real
│   ├── security.md                 # SROS2, DDS security plugins, certificates, supply chain
│   ├── micro-ros.md                # micro-ROS, rclc, XRCE-DDS, ESP32/STM32/RP2040
│   ├── multi-robot.md              # Fleet management, Open-RMF, DDS discovery at scale
│   ├── testing.md                  # gtest, pytest, launch_testing, industrial_ci, CI/CD
│   ├── debugging.md                # ros2 doctor, tracing, Foxglove, MCAP, rosbag2
│   ├── deployment.md               # Docker, cross-compile, fleet management, Zenoh routing
│   ├── message-types.md            # Message conventions, units, covariance, diagnostics
│   └── migration-ros1.md           # ROS 1 → ROS 2 strategy, ros1_bridge
├── scripts/
│   ├── create_package.py           # Scaffold a package with best-practice structure (cpp/python/interfaces)
│   ├── qos_checker.py              # Verify QoS compatibility between pub/sub pairs with fix suggestions
│   └── launch_validator.py         # AST-based static analysis for Python launch files
├── tests/
│   ├── test_create_package.py      # 40 tests — scaffolding, validation, copyright, direct + CLI
│   ├── test_launch_validator.py    # 38 tests — AST visitors, patterns, CLI, main()
│   ├── test_qos_checker.py        # 46 tests — parsing, compatibility, presets, CLI, main()
│   ├── test_qos_property.py       # 13 tests — Hypothesis property-based DDS RxO verification
│   └── Dockerfile.ros2-test        # Multi-stage Docker test (build + validate across distros)
├── setup.cfg                       # flake8 + mypy configuration
├── pytest.ini                      # pytest configuration
├── LICENSE
└── README.md
```

## Current status

**Complete.** 20 reference files, 13,000+ lines of production-grade guidance, 3 utility scripts — all tested and CI-validated.

| | |
|---|---|
| **398 tests** | Unit + property-based (Hypothesis) + CLI + integration |
| **94% coverage** | All scripts verified with flake8 + mypy clean |
| **3 distros** | Humble, Jazzy, Rolling — tested on Python 3.10 / 3.11 / 3.12 |
| **4 CI jobs** | Lint, unit-tests, ros2-integration, lint-scripts |

## Supported ROS 2 distributions

- **Jazzy Jalisco** (LTS, recommended) — primary target
- **Kilted Kaiju** (non-LTS, May 2025) — Zenoh Tier 1, EventsExecutor stable
- **Humble Hawksbill** (LTS) — fully supported
- **Foxy Fitzroy** (LTS, EOL June 2023) — referenced for legacy migration
- **Rolling Ridley** — latest features, noted where they diverge

## Contributing

Contributions welcome. Please:

1. Keep `SKILL.md` under 500 lines — add depth in `references/`
2. Include working code examples, not pseudocode
3. Document anti-patterns alongside correct patterns
4. Note which ROS 2 distros your change applies to
5. Run `flake8 scripts/ tests/` and `mypy scripts/` before submitting
6. Ensure `pytest tests/ --cov=scripts --cov-fail-under=90` passes
7. Test with at least one agent (Claude Code, Codex, etc.)

## License

Apache-2.0 — see [LICENSE](LICENSE).