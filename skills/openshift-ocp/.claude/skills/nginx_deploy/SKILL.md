Skill: nginx_deploy
Purpose
Deploy nginx on OCP using Red Hat UBI image — non-root, SCC compliant.
Triggers
"deploy nginx", "create nginx app"
"get nginx route", "nginx URL", "nginx exposed"
"nginx deployment status"
Tools
deploy_nginx
When: User wants to deploy nginx in a namespace
Args: namespace (required), app_name (optional, default: nginx-app)
Note: Uses ubi8/nginx-120 — no root, OCP SCC compliant
get_nginx_route
When: User wants the public URL of deployed nginx
Args: namespace (required), app_name (optional)
Returns: http route URL
Prompts
nginx_deploy_prompt
When: User wants full deploy + verify flow in one prompt
Notes
Always use UBI image: registry.access.redhat.com/ubi8/nginx-120
Port 8080 (non-root requirement)
Route is HTTP by default — add TLS separately if needed
