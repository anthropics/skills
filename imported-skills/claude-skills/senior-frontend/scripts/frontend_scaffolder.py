#!/usr/bin/env python3
"""
Frontend Project Scaffolder

Generates a complete Next.js/React project structure with TypeScript,
Tailwind CSS, and best practice configurations.

Usage:
    python frontend_scaffolder.py my-app --template nextjs
    python frontend_scaffolder.py dashboard --template react --features auth,api
    python frontend_scaffolder.py landing --template nextjs --dry-run
"""

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Dict, List, Optional


# Project templates
TEMPLATES = {
    "nextjs": {
        "name": "Next.js 14+ App Router",
        "description": "Modern Next.js with App Router, Server Components, and TypeScript",
        "structure": {
            "app": {
                "layout.tsx": "ROOT_LAYOUT",
                "page.tsx": "HOME_PAGE",
                "globals.css": "GLOBALS_CSS",
                "(auth)": {
                    "login": {"page.tsx": "AUTH_PAGE"},
                    "register": {"page.tsx": "AUTH_PAGE"},
                },
                "api": {
                    "health": {"route.ts": "HEALTH_ROUTE"},
                },
            },
            "components": {
                "ui": {
                    "button.tsx": "UI_BUTTON",
                    "input.tsx": "UI_INPUT",
                    "card.tsx": "UI_CARD",
                    "index.ts": "UI_INDEX",
                },
                "layout": {
                    "header.tsx": "LAYOUT_HEADER",
                    "footer.tsx": "LAYOUT_FOOTER",
                    "sidebar.tsx": "LAYOUT_SIDEBAR",
                },
            },
            "lib": {
                "utils.ts": "UTILS",
                "constants.ts": "CONSTANTS",
            },
            "hooks": {
                "use-debounce.ts": "HOOK_DEBOUNCE",
                "use-local-storage.ts": "HOOK_LOCAL_STORAGE",
            },
            "types": {
                "index.ts": "TYPES_INDEX",
            },
            "public": {
                ".gitkeep": "EMPTY",
            },
        },
        "config_files": [
            "next.config.js",
            "tailwind.config.ts",
            "tsconfig.json",
            "postcss.config.js",
            ".eslintrc.json",
            ".prettierrc",
            ".gitignore",
            "package.json",
        ],
    },
    "react": {
        "name": "React + Vite",
        "description": "Modern React with Vite, TypeScript, and Tailwind CSS",
        "structure": {
            "src": {
                "App.tsx": "REACT_APP",
                "main.tsx": "REACT_MAIN",
                "index.css": "GLOBALS_CSS",
                "components": {
                    "ui": {
                        "button.tsx": "UI_BUTTON",
                        "input.tsx": "UI_INPUT",
                        "card.tsx": "UI_CARD",
                        "index.ts": "UI_INDEX",
                    },
                },
                "hooks": {
                    "use-debounce.ts": "HOOK_DEBOUNCE",
                    "use-local-storage.ts": "HOOK_LOCAL_STORAGE",
                },
                "lib": {
                    "utils.ts": "UTILS",
                },
                "types": {
                    "index.ts": "TYPES_INDEX",
                },
            },
            "public": {
                ".gitkeep": "EMPTY",
            },
        },
        "config_files": [
            "vite.config.ts",
            "tailwind.config.ts",
            "tsconfig.json",
            "postcss.config.js",
            ".eslintrc.json",
            ".prettierrc",
            ".gitignore",
            "package.json",
            "index.html",
        ],
    },
}

# Feature modules that can be added
FEATURES = {
    "auth": {
        "description": "Authentication with session management",
        "files": {
            "lib/auth.ts": "AUTH_LIB",
            "middleware.ts": "AUTH_MIDDLEWARE",
            "components/auth/login-form.tsx": "LOGIN_FORM",
            "components/auth/register-form.tsx": "REGISTER_FORM",
        },
        "dependencies": ["next-auth", "@auth/core"],
    },
    "api": {
        "description": "API client with React Query",
        "files": {
            "lib/api-client.ts": "API_CLIENT",
            "lib/query-client.ts": "QUERY_CLIENT",
            "providers/query-provider.tsx": "QUERY_PROVIDER",
        },
        "dependencies": ["@tanstack/react-query", "axios"],
    },
    "forms": {
        "description": "Form handling with React Hook Form + Zod",
        "files": {
            "lib/form-utils.ts": "FORM_UTILS",
            "components/forms/form-field.tsx": "FORM_FIELD",
        },
        "dependencies": ["react-hook-form", "@hookform/resolvers", "zod"],
    },
    "testing": {
        "description": "Testing setup with Vitest and Testing Library",
        "files": {
            "vitest.config.ts": "VITEST_CONFIG",
            "src/test/setup.ts": "TEST_SETUP",
            "src/test/utils.tsx": "TEST_UTILS",
        },
        "dependencies": ["vitest", "@testing-library/react", "@testing-library/jest-dom"],
    },
    "storybook": {
        "description": "Component documentation with Storybook",
        "files": {
            ".storybook/main.ts": "STORYBOOK_MAIN",
            ".storybook/preview.ts": "STORYBOOK_PREVIEW",
        },
        "dependencies": ["@storybook/react-vite", "@storybook/addon-essentials"],
    },
}

# File content templates
FILE_CONTENTS = {
    "ROOT_LAYOUT": '''import type { Metadata } from 'next';
import { Inter } from 'next/font/google';
import './globals.css';

const inter = Inter({ subsets: ['latin'], variable: '--font-inter' });

export const metadata: Metadata = {
  title: 'My App',
  description: 'Built with Next.js',
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en">
      <body className={`${inter.variable} font-sans antialiased`}>
        {children}
      </body>
    </html>
  );
}
''',
    "HOME_PAGE": '''export default function Home() {
  return (
    <main className="flex min-h-screen flex-col items-center justify-center p-24">
      <h1 className="text-4xl font-bold">Welcome</h1>
      <p className="mt-4 text-lg text-gray-600">
        Get started by editing app/page.tsx
      </p>
    </main>
  );
}
''',
    "GLOBALS_CSS": '''@tailwind base;
@tailwind components;
@tailwind utilities;

@layer base {
  :root {
    --background: 0 0% 100%;
    --foreground: 222.2 84% 4.9%;
    --primary: 222.2 47.4% 11.2%;
    --primary-foreground: 210 40% 98%;
    --secondary: 210 40% 96.1%;
    --secondary-foreground: 222.2 47.4% 11.2%;
    --muted: 210 40% 96.1%;
    --muted-foreground: 215.4 16.3% 46.9%;
    --accent: 210 40% 96.1%;
    --accent-foreground: 222.2 47.4% 11.2%;
    --destructive: 0 84.2% 60.2%;
    --destructive-foreground: 210 40% 98%;
    --border: 214.3 31.8% 91.4%;
    --ring: 222.2 84% 4.9%;
    --radius: 0.5rem;
  }

  .dark {
    --background: 222.2 84% 4.9%;
    --foreground: 210 40% 98%;
  }
}

@layer base {
  * {
    @apply border-border;
  }
  body {
    @apply bg-background text-foreground;
  }
}
''',
    "UI_BUTTON": '''import { forwardRef } from 'react';
import { cn } from '@/lib/utils';

interface ButtonProps extends React.ButtonHTMLAttributes<HTMLButtonElement> {
  variant?: 'default' | 'destructive' | 'outline' | 'ghost';
  size?: 'default' | 'sm' | 'lg';
}

const Button = forwardRef<HTMLButtonElement, ButtonProps>(
  ({ className, variant = 'default', size = 'default', ...props }, ref) => {
    return (
      <button
        className={cn(
          'inline-flex items-center justify-center rounded-md font-medium transition-colors',
          'focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring',
          'disabled:pointer-events-none disabled:opacity-50',
          {
            'bg-primary text-primary-foreground hover:bg-primary/90': variant === 'default',
            'bg-destructive text-destructive-foreground hover:bg-destructive/90': variant === 'destructive',
            'border border-input bg-background hover:bg-accent': variant === 'outline',
            'hover:bg-accent hover:text-accent-foreground': variant === 'ghost',
          },
          {
            'h-10 px-4 py-2': size === 'default',
            'h-9 px-3': size === 'sm',
            'h-11 px-8': size === 'lg',
          },
          className
        )}
        ref={ref}
        {...props}
      />
    );
  }
);

Button.displayName = 'Button';

export { Button, type ButtonProps };
''',
    "UI_INPUT": '''import { forwardRef } from 'react';
import { cn } from '@/lib/utils';

interface InputProps extends React.InputHTMLAttributes<HTMLInputElement> {
  error?: string;
}

const Input = forwardRef<HTMLInputElement, InputProps>(
  ({ className, error, ...props }, ref) => {
    return (
      <div className="w-full">
        <input
          className={cn(
            'flex h-10 w-full rounded-md border border-input bg-background px-3 py-2',
            'text-sm ring-offset-background file:border-0 file:bg-transparent',
            'file:text-sm file:font-medium placeholder:text-muted-foreground',
            'focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring',
            'disabled:cursor-not-allowed disabled:opacity-50',
            error && 'border-destructive focus-visible:ring-destructive',
            className
          )}
          ref={ref}
          {...props}
        />
        {error && <p className="mt-1 text-sm text-destructive">{error}</p>}
      </div>
    );
  }
);

Input.displayName = 'Input';

export { Input, type InputProps };
''',
    "UI_CARD": '''import { cn } from '@/lib/utils';

interface CardProps extends React.HTMLAttributes<HTMLDivElement> {}

function Card({ className, ...props }: CardProps) {
  return (
    <div
      className={cn(
        'rounded-lg border bg-card text-card-foreground shadow-sm',
        className
      )}
      {...props}
    />
  );
}

function CardHeader({ className, ...props }: CardProps) {
  return <div className={cn('flex flex-col space-y-1.5 p-6', className)} {...props} />;
}

function CardTitle({ className, ...props }: React.HTMLAttributes<HTMLHeadingElement>) {
  return <h3 className={cn('text-2xl font-semibold leading-none', className)} {...props} />;
}

function CardContent({ className, ...props }: CardProps) {
  return <div className={cn('p-6 pt-0', className)} {...props} />;
}

function CardFooter({ className, ...props }: CardProps) {
  return <div className={cn('flex items-center p-6 pt-0', className)} {...props} />;
}

export { Card, CardHeader, CardTitle, CardContent, CardFooter };
''',
    "UI_INDEX": '''export { Button } from './button';
export { Input } from './input';
export { Card, CardHeader, CardTitle, CardContent, CardFooter } from './card';
''',
    "UTILS": '''import { type ClassValue, clsx } from 'clsx';
import { twMerge } from 'tailwind-merge';

export function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

export function formatDate(date: Date | string): string {
  return new Intl.DateTimeFormat('en-US', {
    month: 'short',
    day: 'numeric',
    year: 'numeric',
  }).format(new Date(date));
}

export function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}
''',
    "CONSTANTS": '''export const APP_NAME = 'My App';
export const API_URL = process.env.NEXT_PUBLIC_API_URL || 'http://localhost:3000/api';

export const ROUTES = {
  home: '/',
  login: '/login',
  register: '/register',
  dashboard: '/dashboard',
} as const;

export const QUERY_KEYS = {
  user: ['user'],
  products: ['products'],
} as const;
''',
    "HOOK_DEBOUNCE": '''import { useState, useEffect } from 'react';

export function useDebounce<T>(value: T, delay: number = 500): T {
  const [debouncedValue, setDebouncedValue] = useState<T>(value);

  useEffect(() => {
    const timer = setTimeout(() => setDebouncedValue(value), delay);
    return () => clearTimeout(timer);
  }, [value, delay]);

  return debouncedValue;
}
''',
    "HOOK_LOCAL_STORAGE": '''import { useState, useEffect } from 'react';

export function useLocalStorage<T>(
  key: string,
  initialValue: T
): [T, (value: T | ((prev: T) => T)) => void] {
  const [storedValue, setStoredValue] = useState<T>(() => {
    if (typeof window === 'undefined') return initialValue;

    try {
      const item = window.localStorage.getItem(key);
      return item ? JSON.parse(item) : initialValue;
    } catch {
      return initialValue;
    }
  });

  useEffect(() => {
    if (typeof window !== 'undefined') {
      window.localStorage.setItem(key, JSON.stringify(storedValue));
    }
  }, [key, storedValue]);

  return [storedValue, setStoredValue];
}
''',
    "TYPES_INDEX": '''export interface User {
  id: string;
  email: string;
  name: string;
  createdAt: Date;
}

export interface ApiResponse<T> {
  data: T;
  message?: string;
  error?: string;
}

export interface PaginatedResponse<T> {
  data: T[];
  total: number;
  page: number;
  pageSize: number;
  totalPages: number;
}
''',
    "HEALTH_ROUTE": '''import { NextResponse } from 'next/server';

export async function GET() {
  return NextResponse.json({
    status: 'ok',
    timestamp: new Date().toISOString(),
  });
}
''',
    "AUTH_PAGE": ''''use client';

export default function AuthPage() {
  return (
    <div className="flex min-h-screen items-center justify-center">
      <div className="w-full max-w-md p-8">
        <h1 className="text-2xl font-bold text-center">Authentication</h1>
      </div>
    </div>
  );
}
''',
    "LAYOUT_HEADER": '''import Link from 'next/link';

export function Header() {
  return (
    <header className="sticky top-0 z-50 w-full border-b bg-background/95 backdrop-blur">
      <div className="container flex h-14 items-center">
        <Link href="/" className="font-bold">
          Logo
        </Link>
        <nav className="ml-auto flex gap-4">
          <Link href="/about" className="text-sm text-muted-foreground hover:text-foreground">
            About
          </Link>
        </nav>
      </div>
    </header>
  );
}
''',
    "LAYOUT_FOOTER": '''export function Footer() {
  return (
    <footer className="border-t py-6">
      <div className="container text-center text-sm text-muted-foreground">
        <p>&copy; {new Date().getFullYear()} My App. All rights reserved.</p>
      </div>
    </footer>
  );
}
''',
    "LAYOUT_SIDEBAR": '''interface SidebarProps {
  children?: React.ReactNode;
}

export function Sidebar({ children }: SidebarProps) {
  return (
    <aside className="fixed left-0 top-14 z-30 h-[calc(100vh-3.5rem)] w-64 border-r bg-background">
      <div className="p-4">{children}</div>
    </aside>
  );
}
''',
    "REACT_APP": '''import { Button } from './components/ui';

function App() {
  return (
    <main className="flex min-h-screen flex-col items-center justify-center p-24">
      <h1 className="text-4xl font-bold">Welcome</h1>
      <p className="mt-4 text-lg text-gray-600">
        Get started by editing src/App.tsx
      </p>
      <Button className="mt-6">Get Started</Button>
    </main>
  );
}

export default App;
''',
    "REACT_MAIN": '''import React from 'react';
import ReactDOM from 'react-dom/client';
import App from './App';
import './index.css';

ReactDOM.createRoot(document.getElementById('root')!).render(
  <React.StrictMode>
    <App />
  </React.StrictMode>
);
''',
    "EMPTY": "",
}


def generate_structure(
    base_path: Path,
    structure: Dict,
    dry_run: bool = False
) -> List[str]:
    """Generate directory structure recursively."""
    created_files = []

    for name, content in structure.items():
        current_path = base_path / name

        if isinstance(content, dict):
            # It's a directory
            if not dry_run:
                current_path.mkdir(parents=True, exist_ok=True)
            created_files.extend(generate_structure(current_path, content, dry_run))
        else:
            # It's a file
            if not dry_run:
                current_path.parent.mkdir(parents=True, exist_ok=True)
                file_content = FILE_CONTENTS.get(content, "")
                current_path.write_text(file_content)
            created_files.append(str(current_path))

    return created_files


def generate_config_files(
    project_path: Path,
    template: str,
    project_name: str,
    features: List[str],
    dry_run: bool = False
) -> List[str]:
    """Generate configuration files."""
    created_files = []
    config_templates = get_config_templates(project_name, template, features)

    template_config = TEMPLATES[template]
    for config_file in template_config["config_files"]:
        file_path = project_path / config_file
        if config_file in config_templates:
            if not dry_run:
                file_path.write_text(config_templates[config_file])
            created_files.append(str(file_path))

    return created_files


def get_config_templates(name: str, template: str, features: List[str]) -> Dict[str, str]:
    """Get configuration file contents."""
    deps = {
        "nextjs": {
            "dependencies": {
                "next": "^14.0.0",
                "react": "^18.2.0",
                "react-dom": "^18.2.0",
                "clsx": "^2.0.0",
                "tailwind-merge": "^2.0.0",
            },
            "devDependencies": {
                "@types/node": "^20.0.0",
                "@types/react": "^18.2.0",
                "@types/react-dom": "^18.2.0",
                "autoprefixer": "^10.0.0",
                "eslint": "^8.0.0",
                "eslint-config-next": "^14.0.0",
                "postcss": "^8.0.0",
                "prettier": "^3.0.0",
                "tailwindcss": "^3.4.0",
                "typescript": "^5.0.0",
            },
        },
        "react": {
            "dependencies": {
                "react": "^18.2.0",
                "react-dom": "^18.2.0",
                "clsx": "^2.0.0",
                "tailwind-merge": "^2.0.0",
            },
            "devDependencies": {
                "@types/react": "^18.2.0",
                "@types/react-dom": "^18.2.0",
                "@vitejs/plugin-react": "^4.0.0",
                "autoprefixer": "^10.0.0",
                "eslint": "^8.0.0",
                "postcss": "^8.0.0",
                "prettier": "^3.0.0",
                "tailwindcss": "^3.4.0",
                "typescript": "^5.0.0",
                "vite": "^5.0.0",
            },
        },
    }

    # Add feature dependencies
    for feature in features:
        if feature in FEATURES:
            for dep in FEATURES[feature].get("dependencies", []):
                deps[template]["dependencies"][dep] = "latest"

    package_json = {
        "name": name,
        "version": "0.1.0",
        "private": True,
        "scripts": {
            "dev": "next dev" if template == "nextjs" else "vite",
            "build": "next build" if template == "nextjs" else "vite build",
            "start": "next start" if template == "nextjs" else "vite preview",
            "lint": "eslint . --ext .ts,.tsx",
            "format": "prettier --write .",
        },
        "dependencies": deps[template]["dependencies"],
        "devDependencies": deps[template]["devDependencies"],
    }

    return {
        "package.json": json.dumps(package_json, indent=2),
        "tsconfig.json": '''{
  "compilerOptions": {
    "target": "ES2020",
    "lib": ["dom", "dom.iterable", "esnext"],
    "allowJs": true,
    "skipLibCheck": true,
    "strict": true,
    "noEmit": true,
    "esModuleInterop": true,
    "module": "esnext",
    "moduleResolution": "bundler",
    "resolveJsonModule": true,
    "isolatedModules": true,
    "jsx": "preserve",
    "incremental": true,
    "plugins": [{ "name": "next" }],
    "paths": {
      "@/*": ["./*"]
    }
  },
  "include": ["next-env.d.ts", "**/*.ts", "**/*.tsx", ".next/types/**/*.ts"],
  "exclude": ["node_modules"]
}
''',
        "tailwind.config.ts": '''import type { Config } from 'tailwindcss';

const config: Config = {
  content: [
    './pages/**/*.{js,ts,jsx,tsx,mdx}',
    './components/**/*.{js,ts,jsx,tsx,mdx}',
    './app/**/*.{js,ts,jsx,tsx,mdx}',
    './src/**/*.{js,ts,jsx,tsx,mdx}',
  ],
  theme: {
    extend: {
      colors: {
        background: 'hsl(var(--background))',
        foreground: 'hsl(var(--foreground))',
        primary: {
          DEFAULT: 'hsl(var(--primary))',
          foreground: 'hsl(var(--primary-foreground))',
        },
        secondary: {
          DEFAULT: 'hsl(var(--secondary))',
          foreground: 'hsl(var(--secondary-foreground))',
        },
        destructive: {
          DEFAULT: 'hsl(var(--destructive))',
          foreground: 'hsl(var(--destructive-foreground))',
        },
        muted: {
          DEFAULT: 'hsl(var(--muted))',
          foreground: 'hsl(var(--muted-foreground))',
        },
        accent: {
          DEFAULT: 'hsl(var(--accent))',
          foreground: 'hsl(var(--accent-foreground))',
        },
        border: 'hsl(var(--border))',
        ring: 'hsl(var(--ring))',
      },
      borderRadius: {
        lg: 'var(--radius)',
        md: 'calc(var(--radius) - 2px)',
        sm: 'calc(var(--radius) - 4px)',
      },
    },
  },
  plugins: [],
};

export default config;
''',
        "postcss.config.js": '''module.exports = {
  plugins: {
    tailwindcss: {},
    autoprefixer: {},
  },
};
''',
        "next.config.js": '''/** @type {import('next').NextConfig} */
const nextConfig = {
  images: {
    remotePatterns: [],
    formats: ['image/avif', 'image/webp'],
  },
  experimental: {
    optimizePackageImports: ['lucide-react'],
  },
};

module.exports = nextConfig;
''',
        "vite.config.ts": '''import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
import path from 'path';

export default defineConfig({
  plugins: [react()],
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
    },
  },
});
''',
        ".eslintrc.json": '''{
  "extends": ["next/core-web-vitals", "prettier"],
  "rules": {
    "react/no-unescaped-entities": "off"
  }
}
''',
        ".prettierrc": '''{
  "semi": true,
  "singleQuote": true,
  "tabWidth": 2,
  "trailingComma": "es5",
  "printWidth": 100
}
''',
        ".gitignore": '''# Dependencies
node_modules/
.pnp
.pnp.js

# Build
.next/
out/
dist/
build/

# Environment
.env
.env.local
.env.*.local

# IDE
.vscode/
.idea/

# Debug
npm-debug.log*
yarn-debug.log*
yarn-error.log*

# OS
.DS_Store
Thumbs.db

# Testing
coverage/
''',
        "index.html": '''<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <link rel="icon" type="image/svg+xml" href="/vite.svg" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>''' + name + '''</title>
  </head>
  <body>
    <div id="root"></div>
    <script type="module" src="/src/main.tsx"></script>
  </body>
</html>
''',
    }


def scaffold_project(
    name: str,
    output_dir: Path,
    template: str = "nextjs",
    features: Optional[List[str]] = None,
    dry_run: bool = False,
) -> Dict:
    """Scaffold a complete frontend project."""
    features = features or []
    project_path = output_dir / name

    if project_path.exists() and not dry_run:
        return {"error": f"Directory already exists: {project_path}"}

    template_config = TEMPLATES.get(template)
    if not template_config:
        return {"error": f"Unknown template: {template}"}

    created_files = []

    # Create project directory
    if not dry_run:
        project_path.mkdir(parents=True, exist_ok=True)

    # Generate base structure
    created_files.extend(
        generate_structure(project_path, template_config["structure"], dry_run)
    )

    # Generate config files
    created_files.extend(
        generate_config_files(project_path, template, name, features, dry_run)
    )

    # Add feature files
    for feature in features:
        if feature in FEATURES:
            for file_path, content_key in FEATURES[feature]["files"].items():
                full_path = project_path / file_path
                if not dry_run:
                    full_path.parent.mkdir(parents=True, exist_ok=True)
                    content = FILE_CONTENTS.get(content_key, f"// TODO: Implement {content_key}")
                    full_path.write_text(content)
                created_files.append(str(full_path))

    return {
        "name": name,
        "template": template,
        "template_name": template_config["name"],
        "features": features,
        "path": str(project_path),
        "files_created": len(created_files),
        "files": created_files,
        "next_steps": [
            f"cd {name}",
            "npm install",
            "npm run dev",
        ],
    }


def print_result(result: Dict) -> None:
    """Print scaffolding result."""
    if "error" in result:
        print(f"Error: {result['error']}", file=sys.stderr)
        return

    print(f"\n{'='*60}")
    print(f"Project Scaffolded: {result['name']}")
    print(f"{'='*60}")
    print(f"Template: {result['template_name']}")
    print(f"Location: {result['path']}")
    print(f"Files Created: {result['files_created']}")

    if result["features"]:
        print(f"Features: {', '.join(result['features'])}")

    print(f"\nNext Steps:")
    for step in result["next_steps"]:
        print(f"  $ {step}")

    print(f"{'='*60}\n")


def main():
    parser = argparse.ArgumentParser(
        description="Scaffold a frontend project with best practices"
    )
    parser.add_argument(
        "name",
        help="Project name (kebab-case recommended)"
    )
    parser.add_argument(
        "--dir", "-d",
        default=".",
        help="Output directory (default: current directory)"
    )
    parser.add_argument(
        "--template", "-t",
        choices=list(TEMPLATES.keys()),
        default="nextjs",
        help="Project template (default: nextjs)"
    )
    parser.add_argument(
        "--features", "-f",
        help="Comma-separated features to add (auth,api,forms,testing,storybook)"
    )
    parser.add_argument(
        "--list-templates",
        action="store_true",
        help="List available templates"
    )
    parser.add_argument(
        "--list-features",
        action="store_true",
        help="List available features"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be created without creating files"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format"
    )

    args = parser.parse_args()

    if args.list_templates:
        print("\nAvailable Templates:")
        for key, template in TEMPLATES.items():
            print(f"  {key}: {template['name']}")
            print(f"    {template['description']}")
        return

    if args.list_features:
        print("\nAvailable Features:")
        for key, feature in FEATURES.items():
            print(f"  {key}: {feature['description']}")
            deps = ", ".join(feature.get("dependencies", []))
            if deps:
                print(f"    Adds: {deps}")
        return

    features = []
    if args.features:
        features = [f.strip() for f in args.features.split(",")]
        invalid = [f for f in features if f not in FEATURES]
        if invalid:
            print(f"Unknown features: {', '.join(invalid)}", file=sys.stderr)
            print(f"Valid features: {', '.join(FEATURES.keys())}")
            sys.exit(1)

    result = scaffold_project(
        name=args.name,
        output_dir=Path(args.dir),
        template=args.template,
        features=features,
        dry_run=args.dry_run,
    )

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print_result(result)


if __name__ == "__main__":
    main()
