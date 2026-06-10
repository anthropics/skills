Skill: login_status
Purpose
Manage OCP authentication — check login state and login to clusters.
Triggers
"am I logged in", "check login", "login status"
"login to OCP", "connect to cluster"
"who am I", "current user"
Tools
check_login
When: User asks if they are logged in or wants to see current session
Returns: Current user and server URL, or error if not logged in
ocp_login
When: User wants to login to an OCP cluster
Args: server (API URL), username, password
Example: Login to https://api.cluster.example.com:6443
Prompts
login_status_prompt
When: User wants a natural language summary of login state
Resources
ocp://login-status
When: Claude needs current login state as context before running other tools
