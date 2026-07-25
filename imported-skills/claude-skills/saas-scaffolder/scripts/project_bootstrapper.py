#!/usr/bin/env python3
"""Project Bootstrapper — Generate SaaS project scaffolding from config.

Creates project directory structure with boilerplate files, README,
docker-compose, environment configs, and CI/CD templates.

Usage:
    python project_bootstrapper.py config.json --output-dir ./my-project
    python project_bootstrapper.py config.json --format json --dry-run
"""

import argparse
import json
import os
import sys
from typing import Dict, List, Any, Optional
from datetime import datetime


STACK_TEMPLATES = {
    "nextjs": {
        "package.json": lambda c: json.dumps({
            "name": c["name"],
            "version": "0.1.0",
            "private": True,
            "scripts": {
                "dev": "next dev",
                "build": "next build",
                "start": "next start",
                "lint": "next lint",
                "test": "jest",
                "test:watch": "jest --watch"
            },
            "dependencies": {
                "next": "^14.0.0",
                "react": "^18.0.0",
                "react-dom": "^18.0.0"
            },
            "devDependencies": {
                "typescript": "^5.0.0",
                "@types/react": "^18.0.0",
                "@types/node": "^20.0.0",
                "eslint": "^8.0.0",
                "eslint-config-next": "^14.0.0"
            }
        }, indent=2),
        "tsconfig.json": lambda c: json.dumps({
            "compilerOptions": {
                "target": "es5",
                "lib": ["dom", "dom.iterable", "esnext"],
                "allowJs": True,
                "skipLibCheck": True,
                "strict": True,
                "forceConsistentCasingInFileNames": True,
                "noEmit": True,
                "esModuleInterop": True,
                "module": "esnext",
                "moduleResolution": "bundler",
                "resolveJsonModule": True,
                "isolatedModules": True,
                "jsx": "preserve",
                "incremental": True,
                "paths": {"@/*": ["./src/*"]}
            },
            "include": ["next-env.d.ts", "**/*.ts", "**/*.tsx"],
            "exclude": ["node_modules"]
        }, indent=2),
        "dirs": ["src/app", "src/components", "src/lib", "src/styles", "public", "tests"],
        "files": {
            "src/app/layout.tsx": "export default function RootLayout({ children }: { children: React.ReactNode }) {\n  return <html lang=\"en\"><body>{children}</body></html>;\n}\n",
            "src/app/page.tsx": "export default function Home() {\n  return <main><h1>Welcome</h1></main>;\n}\n",
        }
    },
    "express": {
        "package.json": lambda c: json.dumps({
            "name": c["name"],
            "version": "0.1.0",
            "main": "src/index.ts",
            "scripts": {
                "dev": "tsx watch src/index.ts",
                "build": "tsc",
                "start": "node dist/index.js",
                "test": "jest",
                "lint": "eslint src/"
            },
            "dependencies": {
                "express": "^4.18.0",
                "cors": "^2.8.5",
                "helmet": "^7.0.0",
                "dotenv": "^16.0.0"
            },
            "devDependencies": {
                "typescript": "^5.0.0",
                "@types/express": "^4.17.0",
                "@types/cors": "^2.8.0",
                "@types/node": "^20.0.0",
                "tsx": "^4.0.0",
                "jest": "^29.0.0",
                "@types/jest": "^29.0.0",
                "eslint": "^8.0.0"
            }
        }, indent=2),
        "dirs": ["src/routes", "src/middleware", "src/models", "src/services", "src/utils", "tests"],
        "files": {
            "src/index.ts": "import express from 'express';\nimport cors from 'cors';\nimport helmet from 'helmet';\nimport { config } from 'dotenv';\n\nconfig();\n\nconst app = express();\nconst PORT = process.env.PORT || 3000;\n\napp.use(helmet());\napp.use(cors());\napp.use(express.json());\n\napp.get('/health', (req, res) => res.json({ status: 'ok' }));\n\napp.listen(PORT, () => console.log(`Server running on port ${PORT}`));\n",
        }
    },
    "fastapi": {
        "requirements.txt": lambda c: "fastapi>=0.100.0\nuvicorn[standard]>=0.23.0\npydantic>=2.0.0\npython-dotenv>=1.0.0\nsqlalchemy>=2.0.0\nalembic>=1.12.0\npytest>=7.0.0\nhttpx>=0.24.0\n",
        "dirs": ["app/api", "app/models", "app/services", "app/core", "tests", "alembic"],
        "files": {
            "app/__init__.py": "",
            "app/main.py": "from fastapi import FastAPI\nfrom app.core.config import settings\n\napp = FastAPI(title=settings.PROJECT_NAME)\n\n@app.get('/health')\ndef health(): return {'status': 'ok'}\n",
            "app/core/__init__.py": "",
            "app/core/config.py": "from pydantic_settings import BaseSettings\n\nclass Settings(BaseSettings):\n    PROJECT_NAME: str = 'API'\n    DATABASE_URL: str = 'sqlite:///./app.db'\n    class Config:\n        env_file = '.env'\n\nsettings = Settings()\n",
        }
    }
}


def generate_readme(config: Dict[str, Any]) -> str:
    """Generate README.md content."""
    name = config.get("name", "my-project")
    desc = config.get("description", "A SaaS application")
    stack = config.get("stack", "nextjs")

    return f"""# {name}

{desc}

## Tech Stack

- **Framework**: {stack}
- **Database**: {config.get('database', 'PostgreSQL')}
- **Auth**: {config.get('auth', 'JWT')}

## Getting Started

### Prerequisites

- Node.js 18+ / Python 3.11+
- Docker & Docker Compose

### Development

```bash
# Clone the repo
git clone <repo-url>
cd {name}

# Copy environment variables
cp .env.example .env

# Start with Docker
docker compose up -d

# Or run locally
{'npm install && npm run dev' if stack in ('nextjs', 'express') else 'pip install -r requirements.txt && uvicorn app.main:app --reload'}
```

### Testing

```bash
{'npm test' if stack in ('nextjs', 'express') else 'pytest'}
```

## Project Structure

```
{name}/
├── {'src/' if stack in ('nextjs', 'express') else 'app/'}
├── tests/
├── docker-compose.yml
├── .env.example
└── README.md
```

## License

MIT
"""


def generate_env_example(config: Dict[str, Any]) -> str:
    """Generate .env.example file."""
    lines = [
        "# Application",
        f"APP_NAME={config.get('name', 'my-app')}",
        "NODE_ENV=development",
        "PORT=3000",
        "",
        "# Database",
    ]
    db = config.get("database", "postgresql")
    if db == "postgresql":
        lines.extend(["DATABASE_URL=postgresql://user:password@localhost:5432/mydb", ""])
    elif db == "mongodb":
        lines.extend(["MONGODB_URI=mongodb://localhost:27017/mydb", ""])
    elif db == "mysql":
        lines.extend(["DATABASE_URL=mysql://user:password@localhost:3306/mydb", ""])

    if config.get("auth"):
        lines.extend([
            "# Auth",
            "JWT_SECRET=change-me-in-production",
            "JWT_EXPIRY=7d",
            ""
        ])

    if config.get("features", {}).get("email"):
        lines.extend(["# Email", "SMTP_HOST=smtp.example.com", "SMTP_PORT=587", "SMTP_USER=", "SMTP_PASS=", ""])

    if config.get("features", {}).get("storage"):
        lines.extend(["# Storage", "S3_BUCKET=", "S3_REGION=us-east-1", "AWS_ACCESS_KEY_ID=", "AWS_SECRET_ACCESS_KEY=", ""])

    return "\n".join(lines)


def generate_docker_compose(config: Dict[str, Any]) -> str:
    """Generate docker-compose.yml."""
    name = config.get("name", "app")
    stack = config.get("stack", "nextjs")
    db = config.get("database", "postgresql")

    services = {
        "app": {
            "build": ".",
            "ports": ["3000:3000"],
            "env_file": [".env"],
            "depends_on": ["db"] if db else [],
            "volumes": [".:/app", "/app/node_modules"] if stack != "fastapi" else [".:/app"]
        }
    }

    if db == "postgresql":
        services["db"] = {
            "image": "postgres:16-alpine",
            "ports": ["5432:5432"],
            "environment": {
                "POSTGRES_USER": "user",
                "POSTGRES_PASSWORD": "password",
                "POSTGRES_DB": "mydb"
            },
            "volumes": ["pgdata:/var/lib/postgresql/data"]
        }
    elif db == "mongodb":
        services["db"] = {
            "image": "mongo:7",
            "ports": ["27017:27017"],
            "volumes": ["mongodata:/data/db"]
        }

    if config.get("features", {}).get("redis"):
        services["redis"] = {
            "image": "redis:7-alpine",
            "ports": ["6379:6379"]
        }

    compose = {
        "version": "3.8",
        "services": services,
        "volumes": {}
    }
    if db == "postgresql":
        compose["volumes"]["pgdata"] = {}
    elif db == "mongodb":
        compose["volumes"]["mongodata"] = {}

    # Manual YAML-like output (avoid pyyaml dependency)
    nl = "\n"
    depends_on = f"    depends_on:{nl}      - db" if db else ""
    vol_line = "  pgdata:" if db == "postgresql" else "  mongodata:" if db == "mongodb" else "  {}"
    return f"""version: '3.8'

services:
  app:
    build: .
    ports:
      - "3000:3000"
    env_file:
      - .env
    volumes:
      - .:/app
{depends_on}

{generate_db_service(db)}
{generate_redis_service(config)}
volumes:
{vol_line}
"""


def generate_db_service(db: str) -> str:
    if db == "postgresql":
        return """  db:
    image: postgres:16-alpine
    ports:
      - "5432:5432"
    environment:
      POSTGRES_USER: user
      POSTGRES_PASSWORD: password
      POSTGRES_DB: mydb
    volumes:
      - pgdata:/var/lib/postgresql/data
"""
    elif db == "mongodb":
        return """  db:
    image: mongo:7
    ports:
      - "27017:27017"
    volumes:
      - mongodata:/data/db
"""
    return ""


def generate_redis_service(config: Dict[str, Any]) -> str:
    if config.get("features", {}).get("redis"):
        return """  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
"""
    return ""


def generate_gitignore(stack: str) -> str:
    """Generate .gitignore."""
    common = "node_modules/\n.env\n.env.local\ndist/\nbuild/\n.next/\n*.log\n.DS_Store\ncoverage/\n__pycache__/\n*.pyc\n.pytest_cache/\n.venv/\n"
    return common


def generate_dockerfile(config: Dict[str, Any]) -> str:
    """Generate Dockerfile."""
    stack = config.get("stack", "nextjs")
    if stack == "fastapi":
        return """FROM python:3.11-slim
WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt
COPY . .
EXPOSE 3000
CMD ["uvicorn", "app.main:app", "--host", "0.0.0.0", "--port", "3000"]
"""
    return """FROM node:20-alpine
WORKDIR /app
COPY package*.json ./
RUN npm ci
COPY . .
RUN npm run build
EXPOSE 3000
CMD ["npm", "start"]
"""


def scaffold_project(config: Dict[str, Any], output_dir: str, dry_run: bool = False) -> Dict[str, Any]:
    """Generate project scaffolding."""
    stack = config.get("stack", "nextjs")
    template = STACK_TEMPLATES.get(stack, STACK_TEMPLATES["nextjs"])
    files_created = []

    # Create directories
    for d in template.get("dirs", []):
        path = os.path.join(output_dir, d)
        if not dry_run:
            os.makedirs(path, exist_ok=True)
        files_created.append({"path": d + "/", "type": "directory"})

    # Create template files
    all_files = {}

    # Package/requirements file
    for key in ("package.json", "requirements.txt"):
        if key in template:
            all_files[key] = template[key](config)

    if "tsconfig.json" in template:
        all_files["tsconfig.json"] = template["tsconfig.json"](config)

    # Stack-specific files
    all_files.update(template.get("files", {}))

    # Common files
    all_files["README.md"] = generate_readme(config)
    all_files[".env.example"] = generate_env_example(config)
    all_files[".gitignore"] = generate_gitignore(stack)
    all_files["docker-compose.yml"] = generate_docker_compose(config)
    all_files["Dockerfile"] = generate_dockerfile(config)

    # Write files
    for filepath, content in all_files.items():
        full_path = os.path.join(output_dir, filepath)
        if not dry_run:
            os.makedirs(os.path.dirname(full_path), exist_ok=True)
            with open(full_path, "w") as f:
                f.write(content)
        files_created.append({"path": filepath, "type": "file", "size": len(content)})

    return {
        "generated_at": datetime.now().isoformat(),
        "project_name": config.get("name", "my-project"),
        "stack": stack,
        "output_dir": output_dir,
        "files_created": files_created,
        "total_files": len([f for f in files_created if f["type"] == "file"]),
        "total_dirs": len([f for f in files_created if f["type"] == "directory"]),
        "dry_run": dry_run
    }


def main():
    parser = argparse.ArgumentParser(description="Bootstrap SaaS project from config")
    parser.add_argument("input", help="Path to project config JSON")
    parser.add_argument("--output-dir", type=str, default="./my-project", help="Output directory")
    parser.add_argument("--format", choices=["json", "text"], default="text", help="Output format")
    parser.add_argument("--dry-run", action="store_true", help="Preview without creating files")

    args = parser.parse_args()

    with open(args.input) as f:
        config = json.load(f)

    result = scaffold_project(config, args.output_dir, args.dry_run)

    if args.format == "json":
        print(json.dumps(result, indent=2))
    else:
        print(f"Project '{result['project_name']}' scaffolded at {result['output_dir']}")
        print(f"Stack: {result['stack']}")
        print(f"Created: {result['total_files']} files, {result['total_dirs']} directories")
        if result["dry_run"]:
            print("\n[DRY RUN] No files were created. Files that would be created:")
        print("\nFiles:")
        for f in result["files_created"]:
            prefix = "📁" if f["type"] == "directory" else "📄"
            size = f" ({f.get('size', 0)} bytes)" if f.get("size") else ""
            print(f"  {prefix} {f['path']}{size}")


if __name__ == "__main__":
    main()
