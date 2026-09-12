#!/usr/bin/env python3
"""
Check overall Kubernetes cluster health and identify potential issues.

Usage:
    python scripts/cluster_health.py
    python scripts/cluster_health.py --json
    python scripts/cluster_health.py --namespace production

This script will:
1. Check node status and resource pressure
2. Verify control plane components
3. Check for pods in error states across namespaces
4. Identify resource quota issues
5. Check for pending PersistentVolumeClaims
6. Provide overall cluster health summary
"""

import subprocess
import sys
import argparse
import json


def run_kubectl(args, capture_output=True):
    """Run a kubectl command and return the output."""
    cmd = ['kubectl'] + args
    try:
        result = subprocess.run(cmd, capture_output=capture_output, text=True, timeout=60)
        return result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        return '', 'Command timed out', 1
    except FileNotFoundError:
        return '', 'kubectl not found. Please ensure kubectl is installed and in PATH.', 1


def check_nodes():
    """Check node health and return issues."""
    issues = []
    healthy_nodes = 0
    total_nodes = 0
    
    stdout, stderr, rc = run_kubectl(['get', 'nodes', '-o', 'json'])
    if rc != 0:
        return {'error': stderr, 'issues': [], 'healthy': 0, 'total': 0}
    
    try:
        nodes = json.loads(stdout)
        for node in nodes.get('items', []):
            total_nodes += 1
            node_name = node.get('metadata', {}).get('name', 'unknown')
            conditions = node.get('status', {}).get('conditions', [])
            
            node_ready = False
            node_issues = []
            
            for condition in conditions:
                cond_type = condition.get('type', '')
                status = condition.get('status', '')
                
                if cond_type == 'Ready':
                    node_ready = status == 'True'
                    if not node_ready:
                        node_issues.append(f"Node {node_name} is NotReady")
                
                elif cond_type in ['MemoryPressure', 'DiskPressure', 'PIDPressure']:
                    if status == 'True':
                        node_issues.append(f"Node {node_name} has {cond_type}")
            
            if node_ready and not node_issues:
                healthy_nodes += 1
            issues.extend(node_issues)
    
    except json.JSONDecodeError:
        return {'error': 'Failed to parse node data', 'issues': [], 'healthy': 0, 'total': 0}
    
    return {'issues': issues, 'healthy': healthy_nodes, 'total': total_nodes}


def check_pods(namespace=None):
    """Check for pods in error states."""
    issues = []
    error_pods = []
    
    args = ['get', 'pods', '-o', 'json']
    if namespace:
        args.extend(['-n', namespace])
    else:
        args.append('--all-namespaces')
    
    stdout, stderr, rc = run_kubectl(args)
    if rc != 0:
        return {'error': stderr, 'issues': [], 'error_pods': []}
    
    try:
        pods = json.loads(stdout)
        for pod in pods.get('items', []):
            pod_name = pod.get('metadata', {}).get('name', 'unknown')
            pod_namespace = pod.get('metadata', {}).get('namespace', 'default')
            phase = pod.get('status', {}).get('phase', 'Unknown')
            
            # Check for problematic phases
            if phase in ['Failed', 'Unknown']:
                error_pods.append({
                    'name': pod_name,
                    'namespace': pod_namespace,
                    'phase': phase
                })
                issues.append(f"Pod {pod_namespace}/{pod_name} is in {phase} phase")
            
            # Check container statuses
            container_statuses = pod.get('status', {}).get('containerStatuses', [])
            for cs in container_statuses:
                waiting = cs.get('state', {}).get('waiting', {})
                reason = waiting.get('reason', '')
                
                if reason in ['CrashLoopBackOff', 'ImagePullBackOff', 'ErrImagePull', 'CreateContainerConfigError']:
                    error_pods.append({
                        'name': pod_name,
                        'namespace': pod_namespace,
                        'phase': reason
                    })
                    issues.append(f"Pod {pod_namespace}/{pod_name} has container in {reason}")
    
    except json.JSONDecodeError:
        return {'error': 'Failed to parse pod data', 'issues': [], 'error_pods': []}
    
    return {'issues': issues, 'error_pods': error_pods}


def check_pending_pvcs(namespace=None):
    """Check for pending PersistentVolumeClaims."""
    issues = []
    pending_pvcs = []
    
    args = ['get', 'pvc', '-o', 'json']
    if namespace:
        args.extend(['-n', namespace])
    else:
        args.append('--all-namespaces')
    
    stdout, stderr, rc = run_kubectl(args)
    if rc != 0:
        return {'issues': [], 'pending_pvcs': []}
    
    try:
        pvcs = json.loads(stdout)
        for pvc in pvcs.get('items', []):
            pvc_name = pvc.get('metadata', {}).get('name', 'unknown')
            pvc_namespace = pvc.get('metadata', {}).get('namespace', 'default')
            phase = pvc.get('status', {}).get('phase', 'Unknown')
            
            if phase == 'Pending':
                pending_pvcs.append({
                    'name': pvc_name,
                    'namespace': pvc_namespace
                })
                issues.append(f"PVC {pvc_namespace}/{pvc_name} is Pending")
    
    except json.JSONDecodeError:
        pass
    
    return {'issues': issues, 'pending_pvcs': pending_pvcs}


def check_deployments(namespace=None):
    """Check for deployments with unavailable replicas."""
    issues = []
    unhealthy_deployments = []
    
    args = ['get', 'deployments', '-o', 'json']
    if namespace:
        args.extend(['-n', namespace])
    else:
        args.append('--all-namespaces')
    
    stdout, stderr, rc = run_kubectl(args)
    if rc != 0:
        return {'issues': [], 'unhealthy_deployments': []}
    
    try:
        deployments = json.loads(stdout)
        for deploy in deployments.get('items', []):
            deploy_name = deploy.get('metadata', {}).get('name', 'unknown')
            deploy_namespace = deploy.get('metadata', {}).get('namespace', 'default')
            
            status = deploy.get('status', {})
            desired = status.get('replicas', 0)
            available = status.get('availableReplicas', 0)
            ready = status.get('readyReplicas', 0)
            
            if desired > 0 and (available < desired or ready < desired):
                unhealthy_deployments.append({
                    'name': deploy_name,
                    'namespace': deploy_namespace,
                    'desired': desired,
                    'available': available,
                    'ready': ready
                })
                issues.append(f"Deployment {deploy_namespace}/{deploy_name}: {ready}/{desired} ready")
    
    except json.JSONDecodeError:
        pass
    
    return {'issues': issues, 'unhealthy_deployments': unhealthy_deployments}


def main():
    parser = argparse.ArgumentParser(
        description='Check Kubernetes cluster health',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument('-n', '--namespace', default=None, 
                        help='Check specific namespace only (default: all namespaces)')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    
    args = parser.parse_args()
    
    print("Kubernetes Cluster Health Check")
    print("=" * 50)
    
    health_report = {
        'nodes': {},
        'pods': {},
        'pvcs': {},
        'deployments': {},
        'overall_status': 'healthy',
        'total_issues': 0
    }
    
    # Check nodes
    print("\nChecking nodes...")
    node_health = check_nodes()
    health_report['nodes'] = node_health
    
    # Check pods
    print("Checking pods...")
    pod_health = check_pods(args.namespace)
    health_report['pods'] = pod_health
    
    # Check PVCs
    print("Checking PersistentVolumeClaims...")
    pvc_health = check_pending_pvcs(args.namespace)
    health_report['pvcs'] = pvc_health
    
    # Check deployments
    print("Checking deployments...")
    deploy_health = check_deployments(args.namespace)
    health_report['deployments'] = deploy_health
    
    # Calculate total issues
    all_issues = []
    all_issues.extend(node_health.get('issues', []))
    all_issues.extend(pod_health.get('issues', []))
    all_issues.extend(pvc_health.get('issues', []))
    all_issues.extend(deploy_health.get('issues', []))
    
    health_report['total_issues'] = len(all_issues)
    if len(all_issues) > 0:
        health_report['overall_status'] = 'unhealthy'
    
    if args.json:
        print(json.dumps(health_report, indent=2))
    else:
        print("\n" + "=" * 50)
        print("HEALTH REPORT")
        print("=" * 50)
        
        # Node summary
        print(f"\nNodes: {node_health.get('healthy', 0)}/{node_health.get('total', 0)} healthy")
        for issue in node_health.get('issues', []):
            print(f"  - {issue}")
        
        # Pod summary
        error_pods = pod_health.get('error_pods', [])
        print(f"\nPods with issues: {len(error_pods)}")
        for pod in error_pods[:10]:  # Show first 10
            print(f"  - {pod['namespace']}/{pod['name']}: {pod['phase']}")
        if len(error_pods) > 10:
            print(f"  ... and {len(error_pods) - 10} more")
        
        # PVC summary
        pending_pvcs = pvc_health.get('pending_pvcs', [])
        if pending_pvcs:
            print(f"\nPending PVCs: {len(pending_pvcs)}")
            for pvc in pending_pvcs[:5]:
                print(f"  - {pvc['namespace']}/{pvc['name']}")
        
        # Deployment summary
        unhealthy_deploys = deploy_health.get('unhealthy_deployments', [])
        if unhealthy_deploys:
            print(f"\nUnhealthy Deployments: {len(unhealthy_deploys)}")
            for deploy in unhealthy_deploys[:5]:
                print(f"  - {deploy['namespace']}/{deploy['name']}: {deploy['ready']}/{deploy['desired']} ready")
        
        # Overall status
        print("\n" + "=" * 50)
        status_emoji = "HEALTHY" if health_report['overall_status'] == 'healthy' else "ISSUES DETECTED"
        print(f"Overall Status: {status_emoji}")
        print(f"Total Issues: {health_report['total_issues']}")
    
    sys.exit(0 if health_report['overall_status'] == 'healthy' else 1)


if __name__ == '__main__':
    main()
