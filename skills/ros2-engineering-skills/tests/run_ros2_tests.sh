#!/usr/bin/env bash
# Run tests against multiple ROS 2 distros using Docker.
#
# Usage:
#   ./tests/run_ros2_tests.sh                    # Test all supported distros
#   ./tests/run_ros2_tests.sh humble             # Test a single distro
#   ./tests/run_ros2_tests.sh humble jazzy       # Test specific distros

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Supported distros (matching osrf/ros:<distro>-desktop images)
ALL_DISTROS=(humble jazzy rolling)

if [[ $# -gt 0 ]]; then
    DISTROS=("$@")
else
    DISTROS=("${ALL_DISTROS[@]}")
fi

PASS=()
FAIL=()

echo "============================================="
echo "  ROS 2 Multi-Distro Test Runner"
echo "============================================="
echo "  Distros: ${DISTROS[*]}"
echo "  Project: ${PROJECT_DIR}"
echo "============================================="
echo

for distro in "${DISTROS[@]}"; do
    echo "---------------------------------------------"
    echo "  Testing ROS 2 ${distro}"
    echo "---------------------------------------------"

    tag="ros2-skills-test:${distro}"

    if docker build \
        -f "${SCRIPT_DIR}/Dockerfile.ros2-test" \
        --build-arg "ROS_DISTRO=${distro}" \
        -t "${tag}" \
        "${PROJECT_DIR}" 2>&1; then
        echo "[PASS] ROS 2 ${distro}"
        PASS+=("${distro}")
    else
        echo "[FAIL] ROS 2 ${distro}"
        FAIL+=("${distro}")
    fi
    echo
done

echo "============================================="
echo "  Results"
echo "============================================="
echo "  Passed: ${PASS[*]:-none}"
echo "  Failed: ${FAIL[*]:-none}"
echo "============================================="

if [[ ${#FAIL[@]} -gt 0 ]]; then
    exit 1
fi
