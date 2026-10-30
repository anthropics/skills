Skill: pod_status
Purpose
Check cluster health — nodes, pods, cluster operators, and version.
Triggers
"get pods", "pod status", "show pods in namespace"
"get nodes", "node status", "are nodes ready"
"cluster operators", "is co healthy", "get co"
"cluster version", "what version is OCP", "get clusterversion"
Tools
get_pods
When: User wants pod status in a specific namespace
Args: namespace (required)
Example: Show pods in namespace "monitoring"
get_nodes
When: User wants node health overview
Returns: All nodes with status and roles
get_cluster_operators
When: User wants to check if all cluster operators are healthy
Returns: oc get co output — Available/Progressing/Degraded
get_cluster_version
When: User asks for OCP version
Returns: Current and desired cluster version
Prompts
pod_health_prompt
When: User wants analysis of unhealthy pods in a namespace
Resources
ocp://cluster-overview
When: Claude needs cluster version and node count as context
