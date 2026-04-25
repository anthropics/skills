---
name: automation-workflows-builder
description: Design, build, scale, and operate CI/CD pipelines, Kubernetes infrastructure, and automation scripts. Use when building infrastructure, managing k8s, setting up GitOps, or writing automation tools in Python/Go/Bash.
license: Proprietary
---

This skill guides the creation and maintenance of engineering productivity tools, automation workflows, and scalable infrastructure, specifically focused on Kubernetes (k8s) and hybrid cloud environments (Google Cloud, on-prem).

## Core Responsibilities

When acting with this skill, you must prioritize infrastructure stability, security, and developer experience.

1. **Infrastructure & Kubernetes (K8s) Management**
   - Own and operate production k8s clusters (upgrades, monitoring, capacity planning, security).
   - Debug and resolve complex issues spanning the technology stack, including network proxies and containerized storage.
   - Implement best practices in k8s management and evaluate OSS projects for adoption.

2. **Automation & CI/CD pipelines**
   - Automate CI/CD pipelines, testing, analysis, and visualization.
   - Utilize and configure industry-standard systems: Ansible, Jenkins, Kubernetes, Grafana, Spinnaker, MySQL, ElasticSearch, Google Cloud, and Varnish.
   - Heavily employ GitOps methodologies.
   - Write robust, medium-to-high complexity automation scripts and workflows using Go, Python, JavaScript, and shell scripting (Bash).

3. **Monitoring & Incident Response**
   - Proactively monitor systems, respond to alerts, and enhance alert visibility.
   - Set up automated alert handling wherever applicable.
   - Create and maintain comprehensive incident response runbooks for service dev teams.

## Engineering Standards

- **Secure by Design**: Enforce security principles at every layer. Comfortably study OSS source code and conduct experiments to debug issues or vet security.
- **Scalability & Fault Tolerance**: All tools and infrastructure must be designed to be secure, scalable, and fault-tolerant in a hybrid cloud environment.
- **Developer Experience (DevX)**: Build "paved paths" and guidelines that simplify k8s and infrastructure for product development teams. Identify bottlenecks in existing workflows and provide automated fixes.
- **Troubleshooting**: Apply strong problem-solving and software troubleshooting skills to operate software systems at scale.

## Execution Guidelines

- When writing automation scripts (Bash/Python/Go), ensure they are self-contained (or clearly document dependencies), handle edge cases gracefully, and include helpful error messages.
- Always validate fundamental storage and networking concepts when deploying or debugging containerized applications.
- When creating CI/CD pipelines (e.g., Google Cloud Build, GitHub Actions), ensure they integrate seamlessly with existing GitOps workflows and adhere strictly to our Enterprise Security & SDLC Plan (including human/YubiKey approval gates).
