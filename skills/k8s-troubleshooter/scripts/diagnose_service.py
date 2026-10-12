#!/usr/bin/env python3
"""
Diagnose Kubernetes service connectivity issues.

Usage:
    python scripts/diagnose_service.py <service-name> [--namespace <namespace>]
    python scripts/diagnose_service.py my-service --namespace production
    python scripts/diagnose_service.py my-service  # uses default namespace

This script will:
1. Check if service exists and get its configuration
2. Verify endpoints are populated
3. Check if selector matches any pods
4. Verify target pods are ready
5. Check for network policies that might block traffic
6. Provide diagnosis and recommended actions
"""

import subprocess
import sys
import argparse
import json


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


def get_service(service_name, namespace):
    """Get service details as JSON."""
    args = ['get', 'service', service_name, '-o', 'json']
    if namespace:
        args.extend(['-n', namespace])
    stdout, stderr, rc = run_kubectl(args)
    if rc != 0:
        return None, stderr
    try:
        return json.loads(stdout), None
    except json.JSONDecodeError as e:
        return None, f"Failed to parse service JSON: {e}"


def get_endpoints(service_name, namespace):
    """Get endpoints for the service."""
    args = ['get', 'endpoints', service_name, '-o', 'json']
    if namespace:
        args.extend(['-n', namespace])
    stdout, stderr, rc = run_kubectl(args)
    if rc != 0:
        return None, stderr
    try:
        return json.loads(stdout), None
    except json.JSONDecodeError:
        return None, "Failed to parse endpoints"


def get_pods_by_selector(selector, namespace):
    """Get pods matching a label selector."""
    selector_str = ','.join([f"{k}={v}" for k, v in selector.items()])
    args = ['get', 'pods', '-l', selector_str, '-o', 'json']
    if namespace:
        args.extend(['-n', namespace])
    stdout, stderr, rc = run_kubectl(args)
    if rc != 0:
        return [], stderr
    try:
        pods = json.loads(stdout)
        return pods.get('items', []), None
    except json.JSONDecodeError:
        return [], "Failed to parse pods"


def get_network_policies(namespace):
    """Get network policies in the namespace."""
    args = ['get', 'networkpolicies', '-o', 'json']
    if namespace:
        args.extend(['-n', namespace])
    stdout, stderr, rc = run_kubectl(args)
    if rc != 0:
        return [], stderr
    try:
        policies = json.loads(stdout)
        return policies.get('items', []), None
    except json.JSONDecodeError:
        return [], "Failed to parse network policies"


def analyze_service(service_data, endpoints_data, pods, network_policies):
    """Analyze service configuration and return diagnosis."""
    diagnosis = {
        'service_type': 'unknown',
        'issues': [],
        'recommendations': [],
        'details': {}
    }
    
    if not service_data:
        diagnosis['issues'].append("Service not found")
        return diagnosis
    
    spec = service_data.get('spec', {})
    diagnosis['service_type'] = spec.get('type', 'ClusterIP')
    diagnosis['details']['ports'] = spec.get('ports', [])
    diagnosis['details']['selector'] = spec.get('selector', {})
    
    # Check if service has a selector
    selector = spec.get('selector', {})
    if not selector:
        diagnosis['issues'].append("Service has no selector defined")
        diagnosis['recommendations'].append("Add selector to service spec to match target pods")
        return diagnosis
    
    # Check endpoints
    if endpoints_data:
        subsets = endpoints_data.get('subsets', [])
        if not subsets:
            diagnosis['issues'].append("Service has no endpoints (no ready pods matching selector)")
            diagnosis['recommendations'].append("Check if pods with matching labels exist and are ready")
        else:
            total_addresses = 0
            not_ready_addresses = 0
            for subset in subsets:
                addresses = subset.get('addresses', [])
                not_ready = subset.get('notReadyAddresses', [])
                total_addresses += len(addresses)
                not_ready_addresses += len(not_ready)
            
            diagnosis['details']['ready_endpoints'] = total_addresses
            diagnosis['details']['not_ready_endpoints'] = not_ready_addresses
            
            if total_addresses == 0:
                diagnosis['issues'].append("No ready endpoints available")
                if not_ready_addresses > 0:
                    diagnosis['issues'].append(f"{not_ready_addresses} endpoints are not ready")
                    diagnosis['recommendations'].append("Check why pods are not passing readiness probes")
    else:
        diagnosis['issues'].append("Could not retrieve endpoints")
    
    # Check matching pods
    if pods:
        ready_pods = 0
        not_ready_pods = 0
        
        for pod in pods:
            pod_name = pod.get('metadata', {}).get('name', 'unknown')
            conditions = pod.get('status', {}).get('conditions', [])
            
            is_ready = False
            for condition in conditions:
                if condition.get('type') == 'Ready' and condition.get('status') == 'True':
                    is_ready = True
                    break
            
            if is_ready:
                ready_pods += 1
            else:
                not_ready_pods += 1
                diagnosis['issues'].append(f"Pod {pod_name} is not ready")
        
        diagnosis['details']['matching_pods'] = len(pods)
        diagnosis['details']['ready_pods'] = ready_pods
        diagnosis['details']['not_ready_pods'] = not_ready_pods
        
        if len(pods) == 0:
            diagnosis['issues'].append("No pods match the service selector")
            diagnosis['recommendations'].append(f"Create pods with labels: {selector}")
    else:
        diagnosis['issues'].append("No pods found matching service selector")
        diagnosis['recommendations'].append(f"Verify pods have labels: {selector}")
    
    # Check service type specific issues
    service_type = spec.get('type', 'ClusterIP')
    
    if service_type == 'LoadBalancer':
        status = service_data.get('status', {})
        lb = status.get('loadBalancer', {})
        ingress = lb.get('ingress', [])
        
        if not ingress:
            diagnosis['issues'].append("LoadBalancer has no external IP assigned")
            diagnosis['recommendations'].append("Check cloud provider load balancer quota and configuration")
        else:
            diagnosis['details']['external_ip'] = ingress[0].get('ip') or ingress[0].get('hostname')
    
    elif service_type == 'NodePort':
        ports = spec.get('ports', [])
        for port in ports:
            node_port = port.get('nodePort')
            if node_port:
                diagnosis['details']['node_port'] = node_port
                diagnosis['recommendations'].append(f"Ensure firewall allows traffic on port {node_port}")
    
    # Check network policies
    if network_policies:
        diagnosis['details']['network_policies'] = len(network_policies)
        diagnosis['recommendations'].append(f"Found {len(network_policies)} NetworkPolicies - verify they allow traffic to service")
    
    return diagnosis


def main():
    parser = argparse.ArgumentParser(
        description='Diagnose Kubernetes service connectivity issues',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument('service_name', help='Name of the service to diagnose')
    parser.add_argument('-n', '--namespace', default=None, help='Namespace (default: current context namespace)')
    parser.add_argument('--json', action='store_true', help='Output diagnosis as JSON')
    
    args = parser.parse_args()
    
    print(f"Diagnosing service: {args.service_name}")
    if args.namespace:
        print(f"Namespace: {args.namespace}")
    print("-" * 50)
    
    # Get service
    service_data, error = get_service(args.service_name, args.namespace)
    if error and 'not found' in error.lower():
        print(f"Error: Service '{args.service_name}' not found")
        sys.exit(1)
    
    # Get endpoints
    endpoints_data, _ = get_endpoints(args.service_name, args.namespace)
    
    # Get pods matching selector
    pods = []
    if service_data:
        selector = service_data.get('spec', {}).get('selector', {})
        if selector:
            pods, _ = get_pods_by_selector(selector, args.namespace)
    
    # Get network policies
    network_policies, _ = get_network_policies(args.namespace)
    
    # Analyze
    diagnosis = analyze_service(service_data, endpoints_data, pods, network_policies)
    
    if args.json:
        print(json.dumps(diagnosis, indent=2))
    else:
        print(f"\nService Type: {diagnosis['service_type']}")
        
        # Show details
        details = diagnosis.get('details', {})
        if 'selector' in details:
            print(f"Selector: {details['selector']}")
        if 'ports' in details:
            for port in details['ports']:
                print(f"Port: {port.get('port')} -> {port.get('targetPort')} ({port.get('protocol', 'TCP')})")
        if 'external_ip' in details:
            print(f"External IP: {details['external_ip']}")
        if 'node_port' in details:
            print(f"NodePort: {details['node_port']}")
        
        print(f"\nMatching Pods: {details.get('matching_pods', 0)}")
        print(f"Ready Pods: {details.get('ready_pods', 0)}")
        print(f"Ready Endpoints: {details.get('ready_endpoints', 0)}")
        
        if diagnosis['issues']:
            print(f"\nIssues Found ({len(diagnosis['issues'])}):")
            for i, issue in enumerate(diagnosis['issues'], 1):
                print(f"  {i}. {issue}")
        else:
            print("\nNo issues detected - service appears healthy.")
        
        if diagnosis['recommendations']:
            print(f"\nRecommendations ({len(diagnosis['recommendations'])}):")
            for i, rec in enumerate(diagnosis['recommendations'], 1):
                print(f"  {i}. {rec}")
    
    sys.exit(1 if diagnosis['issues'] else 0)


if __name__ == '__main__':
    main()
