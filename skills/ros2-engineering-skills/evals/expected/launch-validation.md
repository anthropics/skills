# Expected: Launch File Review

## Required Issues Detected

### Errors
1. **Missing `generate_launch_description`**: Function is named `create_nodes` instead
   of `generate_launch_description` — launch system will not find it
2. **Duplicate node name**: Both nodes have name `camera` — will cause conflicts

### Warnings
1. **Deprecated keywords**: `node_executable`, `node_name`, `node_namespace` are
   deprecated — use `executable`, `name`, `namespace`
2. **Hardcoded path**: `/home/user/catkin_ws/config/camera.yaml` is not portable —
   use `os.path.join(get_package_share_directory('my_robot'), 'config', 'camera.yaml')`

### Info
- Second node uses correct modern keywords (`executable`, `name`)

## Required Corrected Version
Must include:
- Function renamed to `generate_launch_description`
- All deprecated keywords replaced with modern equivalents
- Hardcoded path replaced with `get_package_share_directory`
- Duplicate node name resolved (e.g., `camera` and `lidar`)
- Proper imports including `get_package_share_directory` from `ament_index_python`
