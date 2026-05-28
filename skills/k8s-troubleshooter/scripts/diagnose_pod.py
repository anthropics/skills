#!/usr/bin/env python3
"""
Diagnose pod issues by running a series of kubectl commands and analyzing the output.

Usage:
    python scripts/diagnose_pod.py <pod-name> [--namespace <namespace>]
    python scripts/diagnose_pod.py my-app-pod-abc123 --namespace production
    python scripts/diagnose_pod.py my-app-pod-abc123  # uses default namespace

This script will:
1. Get pod status and phase
2. Check for common error conditions (CrashLoopBackOff, ImagePullBackOff, etc.)
3. Retrieve recent events
4. Get container logs (current and previous if crashed)
5. Check resource usage
6. Provide diagnosis and recommended actions
"""

import subprocess
import sys
import argparse
import json
import re


def run_kubectl(args, capture_output=True):
    """Run a kubectl command and return the output."""
    cmd = ['kubectl'] + args
    try:
        result = subprocess.run(cmd, capture_output=capture_output, text=True, timeout=30)
        return result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        return '', 'Command timed out', 1
    except FileNotFoundError:
        return '', 'kubectl not found. Please ensure kubectl is installed and in PATH.', 1


def get_pod_json(pod_name, namespace):
    """Get pod details as JSON."""
    args = ['get', 'pod', pod_name, '-o', 'json']
    if namespace:
        args.extend(['-n', namespace])
    stdout, stderr, rc = run_kubectl(args)
    if rc != 0:
        return None, stderr
    try:
        return json.loads(stdout), None
    except json.JSONDecodeError as e:
        return None, f"Failed to parse pod JSON: {e}"


def get_pod_events(pod_name, namespace):
    """Get events related to the pod."""
    args = ['get', 'events', '--field-selector', f'involvedObject.name={pod_name}',
            '--sort-by=.lastTimestamp', '-o', 'json']
    if namespace:
        args.extend(['-n', namespace])
    stdout, stderr, rc = run_kubectl(args)
    if rc != 0:
        return [], stderr
    try:
        events = json.loads(stdout)
        return events.get('items', []), None
    except json.JSONDecodeError:
        return [], "Failed to parse events"


def get_pod_logs(pod_name, namespace, previous=False, tail=50):
    """Get pod logs."""
    args = ['logs', pod_name, f'--tail={tail}']
    if namespace:
        args.extend(['-n', namespace])
    if previous:
        args.append('--previous')
    stdout, stderr, rc = run_kubectl(args)
    return stdout, stderr, rc


def analyze_pod_status(pod_data):
    """Analyze pod status and return diagnosis."""
    diagnosis = {
        'status': 'unknown',
        'issues': [],
        'recommendations': []
    }
    
    if not pod_data:
        diagnosis['issues'].append("Could not retrieve pod data")
        return diagnosis
    
    status = pod_data.get('status', {})
    phase = status.get('phase', 'Unknown')
    diagnosis['status'] = phase
    
    # Check container statuses
    container_statuses = status.get('containerStatuses', [])
    init_container_statuses = status.get('initContainerStatuses', [])
    
    for cs in container_statuses + init_container_statuses:
        container_name = cs.get('name', 'unknown')
        ready = cs.get('ready', False)
        restart_count = cs.get('restartCount', 0)
        
        # Check waiting state
        waiting = cs.get('state', {}).get('waiting', {})
        if waiting:
            reason = waiting.get('reason', '')
            message = waiting.get('message', '')
            
            if reason == 'CrashLoopBackOff':
                diagnosis['issues'].append(f"Container '{container_name}' is in CrashLoopBackOff")
                diagnosis['recommendations'].append("Check container logs with --previous flag")
                diagnosis['recommendations'].append("Verify application configuration and dependencies")
                
            elif reason == 'ImagePullBackOff' or reason == 'ErrImagePull':
                diagnosis['issues'].append(f"Container '{container_name}' cannot pull image: {message}")
                diagnosis['recommendations'].append("Verify image name and tag exist in registry")
                diagnosis['recommendations'].append("Check imagePullSecrets if using private registry")
                
            elif reason == 'CreateContainerConfigError':
                diagnosis['issues'].append(f"Container '{container_name}' config error: {message}")
                diagnosis['recommendations'].append("Check ConfigMaps and Secrets referenced by the pod")
                
            elif reason:
                diagnosis['issues'].append(f"Container '{container_name}' waiting: {reason} - {message}")
        
        # Check terminated state
        terminated = cs.get('state', {}).get('terminated', {})
        if terminated:
            reason = terminated.get('reason', '')
            exit_code = terminated.get('exitCode', -1)
            
            if reason == 'OOMKilled':
                diagnosis['issues'].append(f"Container '{container_name}' was OOMKilled")
                diagnosis['recommendations'].append("Increase memory limits in pod spec")
                diagnosis['recommendations'].append("Check for memory leaks in application")
                
            elif reason == 'Error' or exit_code != 0:
                diagnosis['issues'].append(f"Container '{container_name}' terminated with exit code {exit_code}")
                diagnosis['recommendations'].append("Check container logs for error details")
        
        # Check restart count
        if restart_count > 5:
            diagnosis['issues'].append(f"Container '{container_name}' has restarted {restart_count} times")
            diagnosis['recommendations'].append("Investigate why container keeps crashing")
    
    # Check conditions
    conditions = status.get('conditions', [])
    for condition in conditions:
        cond_type = condition.get('type', '')
        cond_status = condition.get('status', '')
        reason = condition.get('reason', '')
        message = condition.get('message', '')
        
        if cond_type == 'PodScheduled' and cond_status == 'False':
            diagnosis['issues'].append(f"Pod not scheduled: {reason} - {message}")
            if 'Insufficient' in message:
                diagnosis['recommendations'].append("Check cluster resource availability")
                diagnosis['recommendations'].append("Consider scaling cluster or reducing resource requests")
            elif 'node' in message.lower():
                diagnosis['recommendations'].append("Check nodeSelector and affinity rules")
                diagnosis['recommendations'].append("Verify node taints and tolerations")
        
        elif cond_type == 'Ready' and cond_status == 'False':
            if 'probe' in message.lower():
                diagnosis['issues'].append(f"Readiness probe failing: {message}")
                diagnosis['recommendations'].append("Check readiness probe configuration")
                diagnosis['recommendations'].append("Verify application is responding on probe endpoint")
    
    return diagnosis


def analyze_events(events):
    """Analyze events for additional issues."""
    issues = []
    recommendations = []
    
    for event in events[-10:]:  # Last 10 events
        event_type = event.get('type', '')
        reason = event.get('reason', '')
        message = event.get('message', '')
        
        if event_type == 'Warning':
            issues.append(f"Warning: {reason} - {message}")
            
            if 'FailedScheduling' in reason:
                recommendations.append("Check resource quotas and node availability")
            elif 'FailedMount' in reason:
                recommendations.append("Check PersistentVolumeClaims and volume configurations")
            elif 'Unhealthy' in reason:
                recommendations.append("Check liveness/readiness probe configurations")
            elif 'BackOff' in reason:
                recommendations.append("Check container logs for startup errors")
    
    return issues, recommendations


def main():
    parser = argparse.ArgumentParser(
        description='Diagnose Kubernetes pod issues',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument('pod_name', help='Name of the pod to diagnose')
    parser.add_argument('-n', '--namespace', default=None, help='Namespace (default: current context namespace)')
    parser.add_argument('--json', action='store_true', help='Output diagnosis as JSON')
    
    args = parser.parse_args()
    
    print(f"Diagnosing pod: {args.pod_name}")
    if args.namespace:
        print(f"Namespace: {args.namespace}")
    print("-" * 50)
    
    # Get pod data
    pod_data, error = get_pod_json(args.pod_name, args.namespace)
    if error:
        print(f"Error getting pod: {error}")
        sys.exit(1)
    
    # Analyze pod status
    diagnosis = analyze_pod_status(pod_data)
    
    # Get and analyze events
    events, _ = get_pod_events(args.pod_name, args.namespace)
    event_issues, event_recommendations = analyze_events(events)
    diagnosis['issues'].extend(event_issues)
    diagnosis['recommendations'].extend(event_recommendations)
    
    # Remove duplicates
    diagnosis['issues'] = list(dict.fromkeys(diagnosis['issues']))
    diagnosis['recommendations'] = list(dict.fromkeys(diagnosis['recommendations']))
    
    if args.json:
        print(json.dumps(diagnosis, indent=2))
    else:
        print(f"\nPod Phase: {diagnosis['status']}")
        
        if diagnosis['issues']:
            print(f"\nIssues Found ({len(diagnosis['issues'])}):")
            for i, issue in enumerate(diagnosis['issues'], 1):
                print(f"  {i}. {issue}")
        else:
            print("\nNo issues detected.")
        
        if diagnosis['recommendations']:
            print(f"\nRecommendations ({len(diagnosis['recommendations'])}):")
            for i, rec in enumerate(diagnosis['recommendations'], 1):
                print(f"  {i}. {rec}")
        
        # Get logs if there are issues
        if diagnosis['issues']:
            print("\n" + "-" * 50)
            print("Recent Logs:")
            logs, log_err, rc = get_pod_logs(args.pod_name, args.namespace, tail=20)
            if rc == 0 and logs:
                print(logs)
            elif 'CrashLoopBackOff' in str(diagnosis['issues']):
                print("Attempting to get previous container logs...")
                logs, log_err, rc = get_pod_logs(args.pod_name, args.namespace, previous=True, tail=20)
                if rc == 0 and logs:
                    print(logs)
                else:
                    print(f"Could not get logs: {log_err}")
            else:
                print(f"Could not get logs: {log_err}")
    
    # Exit with error if issues found
    sys.exit(1 if diagnosis['issues'] else 0)


if __name__ == '__main__':
    main()
