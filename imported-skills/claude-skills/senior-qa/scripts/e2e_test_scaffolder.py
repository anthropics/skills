#!/usr/bin/env python3
"""
E2E Test Scaffolder

Scans Next.js pages/app directory and generates Playwright test files
with common interactions, Page Object Model classes, and configuration.

Usage:
    python e2e_test_scaffolder.py src/app/ --output e2e/
    python e2e_test_scaffolder.py pages/ --include-pom --routes "/login,/dashboard"
"""

import os
import sys
import json
import argparse
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Set
from dataclasses import dataclass, field, asdict
from datetime import datetime


@dataclass
class RouteInfo:
    """Information about a detected route"""
    path: str  # URL path e.g., /dashboard
    file_path: str  # File system path
    route_type: str  # 'page', 'layout', 'api', 'dynamic'
    has_params: bool
    params: List[str]
    has_form: bool
    has_auth: bool
    interactions: List[str]


@dataclass
class TestSpec:
    """A Playwright test specification"""
    route: RouteInfo
    test_cases: List[str]
    imports: Set[str] = field(default_factory=set)


@dataclass
class PageObject:
    """Page Object Model class definition"""
    name: str
    route: str
    locators: List[Tuple[str, str, str]]  # (name, selector, description)
    methods: List[Tuple[str, str]]  # (name, code)


class RouteScanner:
    """Scans Next.js directories for routes"""

    # Pattern to detect page files
    PAGE_PATTERNS = {
        'page.tsx', 'page.ts', 'page.jsx', 'page.js',  # App Router
        'index.tsx', 'index.ts', 'index.jsx', 'index.js'  # Pages Router
    }

    # Patterns indicating specific features
    FORM_PATTERNS = [
        r'<form', r'handleSubmit', r'onSubmit', r'useForm',
        r'<input', r'<textarea', r'<select'
    ]

    AUTH_PATTERNS = [
        r'auth', r'login', r'signin', r'signup', r'register',
        r'useAuth', r'useSession', r'getServerSession', r'withAuth'
    ]

    INTERACTION_PATTERNS = {
        'click': r'onClick|button|Button|<a\s|Link',
        'type': r'<input|<textarea|onChange',
        'select': r'<select|Dropdown|Select',
        'navigation': r'useRouter|router\.push|Link',
        'modal': r'Modal|Dialog|isOpen|onClose',
        'toggle': r'toggle|Switch|Checkbox',
        'upload': r'<input.*type=["\']file|upload|dropzone'
    }

    def __init__(self, source_path: Path, verbose: bool = False):
        self.source_path = source_path
        self.verbose = verbose
        self.routes: List[RouteInfo] = []
        self.is_app_router = self._detect_router_type()

    def _detect_router_type(self) -> bool:
        """Detect if using App Router or Pages Router"""
        # App Router: has 'app' directory with page.tsx files
        # Pages Router: has 'pages' directory with index.tsx files
        app_dir = self.source_path / 'app'
        if app_dir.exists() and list(app_dir.rglob('page.*')):
            return True

        return 'app' in str(self.source_path).lower()

    def scan(self, filter_routes: Optional[List[str]] = None) -> List[RouteInfo]:
        """Scan for all routes"""
        self._scan_directory(self.source_path)

        # Filter if specific routes requested
        if filter_routes:
            self.routes = [
                r for r in self.routes
                if any(fr in r.path for fr in filter_routes)
            ]

        return self.routes

    def _scan_directory(self, directory: Path, url_path: str = ''):
        """Recursively scan directory for routes"""
        if not directory.exists():
            return

        for item in directory.iterdir():
            if item.name.startswith('.') or item.name == 'node_modules':
                continue

            if item.is_dir():
                # Handle route groups (parentheses) and dynamic routes
                dir_name = item.name

                if dir_name.startswith('(') and dir_name.endswith(')'):
                    # Route group - doesn't add to URL path
                    self._scan_directory(item, url_path)
                elif dir_name.startswith('[') and dir_name.endswith(']'):
                    # Dynamic route
                    param_name = dir_name[1:-1]
                    if param_name.startswith('...'):
                        # Catch-all route
                        new_path = f"{url_path}/[...{param_name[3:]}]"
                    else:
                        new_path = f"{url_path}/[{param_name}]"
                    self._scan_directory(item, new_path)
                elif dir_name == 'api':
                    # API routes - scan but mark differently
                    self._scan_api_directory(item, '/api')
                else:
                    new_path = f"{url_path}/{dir_name}"
                    self._scan_directory(item, new_path)

            elif item.is_file():
                self._process_file(item, url_path)

    def _process_file(self, file_path: Path, url_path: str):
        """Process a potential page file"""
        if file_path.name not in self.PAGE_PATTERNS:
            return

        # Skip if it's a layout or other special file
        if any(x in file_path.name for x in ['layout', 'loading', 'error', 'template']):
            return

        try:
            content = file_path.read_text(encoding='utf-8')
        except Exception:
            return

        # Determine route path
        if url_path == '':
            route_path = '/'
        else:
            route_path = url_path

        # Detect dynamic parameters
        params = re.findall(r'\[([^\]]+)\]', route_path)
        has_params = len(params) > 0

        # Detect features
        has_form = any(re.search(p, content) for p in self.FORM_PATTERNS)
        has_auth = any(re.search(p, content, re.IGNORECASE) for p in self.AUTH_PATTERNS)

        # Detect interactions
        interactions = []
        for interaction, pattern in self.INTERACTION_PATTERNS.items():
            if re.search(pattern, content):
                interactions.append(interaction)

        route = RouteInfo(
            path=route_path,
            file_path=str(file_path),
            route_type='dynamic' if has_params else 'page',
            has_params=has_params,
            params=params,
            has_form=has_form,
            has_auth=has_auth,
            interactions=interactions
        )

        self.routes.append(route)

        if self.verbose:
            print(f"  Found route: {route_path}")

    def _scan_api_directory(self, directory: Path, url_path: str):
        """Scan API routes (mark them differently)"""
        for item in directory.iterdir():
            if item.is_dir():
                new_path = f"{url_path}/{item.name}"
                self._scan_api_directory(item, new_path)
            elif item.is_file() and item.suffix in {'.ts', '.tsx', '.js', '.jsx'}:
                # API routes don't get E2E tests typically
                pass


class TestGenerator:
    """Generates Playwright test files"""

    def __init__(self, include_pom: bool = False, verbose: bool = False):
        self.include_pom = include_pom
        self.verbose = verbose

    def generate(self, route: RouteInfo) -> str:
        """Generate a test file for a route"""
        lines = []

        # Imports
        lines.append("import { test, expect } from '@playwright/test';")

        if self.include_pom:
            page_class = self._get_page_class_name(route.path)
            lines.append(f"import {{ {page_class} }} from './pages/{page_class}';")

        lines.append('')

        # Test describe block
        route_name = route.path if route.path != '/' else 'Home'
        lines.append(f"test.describe('{route_name}', () => {{")

        # Generate test cases based on route features
        test_cases = self._generate_test_cases(route)

        for test_case in test_cases:
            lines.append('')
            lines.append(test_case)

        lines.append('});')
        lines.append('')

        return '\n'.join(lines)

    def _generate_test_cases(self, route: RouteInfo) -> List[str]:
        """Generate test cases based on route features"""
        cases = []
        url = self._get_test_url(route)

        # Basic navigation test
        cases.append(f'''  test('loads successfully', async ({{ page }}) => {{
    await page.goto('{url}');
    await expect(page).toHaveURL(/{re.escape(route.path.replace('[', '').replace(']', '.*'))}/);
    // TODO: Add specific content assertions
  }});''')

        # Page title test
        cases.append(f'''  test('has correct title', async ({{ page }}) => {{
    await page.goto('{url}');
    // TODO: Update expected title
    await expect(page).toHaveTitle(/.*/);
  }});''')

        # Auth-related tests
        if route.has_auth:
            cases.append(f'''  test('redirects unauthenticated users', async ({{ page }}) => {{
    await page.goto('{url}');
    // TODO: Verify redirect to login
    // await expect(page).toHaveURL('/login');
  }});

  test('allows authenticated access', async ({{ page }}) => {{
    // TODO: Set up authentication
    // await page.context().addCookies([{{ name: 'session', value: '...' }}]);
    await page.goto('{url}');
    await expect(page).toHaveURL(/{re.escape(route.path.replace('[', '').replace(']', '.*'))}/);
  }});''')

        # Form tests
        if route.has_form:
            cases.append(f'''  test('form submission works', async ({{ page }}) => {{
    await page.goto('{url}');

    // TODO: Fill in form fields
    // await page.getByLabel('Email').fill('test@example.com');
    // await page.getByLabel('Password').fill('password123');

    // Submit form
    // await page.getByRole('button', {{ name: 'Submit' }}).click();

    // TODO: Assert success state
    // await expect(page.getByText('Success')).toBeVisible();
  }});

  test('shows validation errors', async ({{ page }}) => {{
    await page.goto('{url}');

    // Submit without filling required fields
    await page.getByRole('button', {{ name: /submit/i }}).click();

    // TODO: Assert validation errors shown
    // await expect(page.getByText('Required')).toBeVisible();
  }});''')

        # Click interaction tests
        if 'click' in route.interactions:
            cases.append(f'''  test('button interactions work', async ({{ page }}) => {{
    await page.goto('{url}');

    // TODO: Find and click interactive elements
    // const button = page.getByRole('button', {{ name: '...' }});
    // await button.click();
    // await expect(page.getByText('...')).toBeVisible();
  }});''')

        # Navigation tests
        if 'navigation' in route.interactions:
            cases.append(f'''  test('navigation works correctly', async ({{ page }}) => {{
    await page.goto('{url}');

    // TODO: Click navigation links
    // await page.getByRole('link', {{ name: '...' }}).click();
    // await expect(page).toHaveURL('...');
  }});''')

        # Modal tests
        if 'modal' in route.interactions:
            cases.append(f'''  test('modal opens and closes', async ({{ page }}) => {{
    await page.goto('{url}');

    // TODO: Open modal
    // await page.getByRole('button', {{ name: 'Open' }}).click();
    // await expect(page.getByRole('dialog')).toBeVisible();

    // TODO: Close modal
    // await page.getByRole('button', {{ name: 'Close' }}).click();
    // await expect(page.getByRole('dialog')).not.toBeVisible();
  }});''')

        # Dynamic route test
        if route.has_params:
            cases.append(f'''  test('handles dynamic parameters', async ({{ page }}) => {{
    // TODO: Test with different parameter values
    await page.goto('{url}');
    await expect(page.locator('body')).toBeVisible();
  }});''')

        return cases

    def _get_test_url(self, route: RouteInfo) -> str:
        """Get a testable URL for the route"""
        url = route.path

        # Replace dynamic segments with example values
        for param in route.params:
            if param.startswith('...'):
                url = url.replace(f'[...{param[3:]}]', 'example/path')
            else:
                url = url.replace(f'[{param}]', 'test-id')

        return url

    def _get_page_class_name(self, route_path: str) -> str:
        """Get Page Object class name from route path"""
        if route_path == '/':
            return 'HomePage'

        # Remove leading slash and convert to PascalCase
        name = route_path.strip('/')
        name = re.sub(r'\[.*?\]', '', name)  # Remove dynamic segments
        parts = name.split('/')
        return ''.join(p.title() for p in parts if p) + 'Page'


class PageObjectGenerator:
    """Generates Page Object Model classes"""

    def __init__(self, verbose: bool = False):
        self.verbose = verbose

    def generate(self, route: RouteInfo) -> str:
        """Generate a Page Object class for a route"""
        class_name = self._get_class_name(route.path)
        url = route.path

        # Replace dynamic segments
        for param in route.params:
            url = url.replace(f'[{param}]', f'${{{param}}}')

        lines = []

        # Imports
        lines.append("import { Page, Locator, expect } from '@playwright/test';")
        lines.append('')

        # Class definition
        lines.append(f"export class {class_name} {{")
        lines.append("  readonly page: Page;")

        # Common locators
        locators = self._get_locators(route)
        for name, selector, _ in locators:
            lines.append(f"  readonly {name}: Locator;")

        lines.append('')

        # Constructor
        lines.append("  constructor(page: Page) {")
        lines.append("    this.page = page;")
        for name, selector, _ in locators:
            lines.append(f"    this.{name} = page.{selector};")
        lines.append("  }")
        lines.append('')

        # Navigation method
        if route.has_params:
            param_args = ', '.join(f'{p}: string' for p in route.params)
            url_parts = url.split('/')
            url_template = '/'.join(
                f'${{{p}}}' if f'${{{p}}}' in part else part
                for p, part in zip(route.params, url_parts)
            )
            lines.append(f"  async goto({param_args}) {{")
            lines.append(f"    await this.page.goto(`{url_template}`);")
        else:
            lines.append("  async goto() {")
            lines.append(f"    await this.page.goto('{route.path}');")
        lines.append("  }")
        lines.append('')

        # Add methods based on features
        methods = self._get_methods(route, locators)
        for method_name, method_code in methods:
            lines.append(method_code)
            lines.append('')

        lines.append('}')
        lines.append('')

        return '\n'.join(lines)

    def _get_class_name(self, route_path: str) -> str:
        """Get class name from route path"""
        if route_path == '/':
            return 'HomePage'

        name = route_path.strip('/')
        name = re.sub(r'\[.*?\]', '', name)
        parts = name.split('/')
        return ''.join(p.title() for p in parts if p) + 'Page'

    def _get_locators(self, route: RouteInfo) -> List[Tuple[str, str, str]]:
        """Get common locators for a page"""
        locators = []

        # Always add a heading locator
        locators.append(('heading', "getByRole('heading', { level: 1 })", 'Main heading'))

        if route.has_form:
            locators.extend([
                ('submitButton', "getByRole('button', { name: /submit/i })", 'Form submit button'),
                ('form', "locator('form')", 'Main form element'),
            ])

        if route.has_auth:
            locators.extend([
                ('emailInput', "getByLabel('Email')", 'Email input field'),
                ('passwordInput', "getByLabel('Password')", 'Password input field'),
            ])

        if 'navigation' in route.interactions:
            locators.append(('navLinks', "getByRole('navigation').getByRole('link')", 'Navigation links'))

        if 'modal' in route.interactions:
            locators.append(('modal', "getByRole('dialog')", 'Modal dialog'))

        return locators

    def _get_methods(
        self,
        route: RouteInfo,
        locators: List[Tuple[str, str, str]]
    ) -> List[Tuple[str, str]]:
        """Get methods for the page object"""
        methods = []

        # Wait for load method
        methods.append(('waitForLoad', '''  async waitForLoad() {
    await expect(this.heading).toBeVisible();
  }'''))

        if route.has_form:
            methods.append(('submitForm', '''  async submitForm() {
    await this.submitButton.click();
  }'''))

        if route.has_auth:
            methods.append(('login', '''  async login(email: string, password: string) {
    await this.emailInput.fill(email);
    await this.passwordInput.fill(password);
    await this.submitButton.click();
  }'''))

        if 'modal' in route.interactions:
            methods.append(('waitForModal', '''  async waitForModal() {
    await expect(this.modal).toBeVisible();
  }'''))
            methods.append(('closeModal', '''  async closeModal() {
    await this.page.keyboard.press('Escape');
    await expect(this.modal).not.toBeVisible();
  }'''))

        return methods


class ConfigGenerator:
    """Generates Playwright configuration"""

    def generate_config(self) -> str:
        """Generate playwright.config.ts"""
        return '''import { defineConfig, devices } from '@playwright/test';

/**
 * Playwright Test Configuration
 * @see https://playwright.dev/docs/test-configuration
 */
export default defineConfig({
  testDir: './e2e',
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  reporter: [
    ['html', { open: 'never' }],
    ['list'],
  ],
  use: {
    baseURL: process.env.BASE_URL || 'http://localhost:3000',
    trace: 'on-first-retry',
    screenshot: 'only-on-failure',
  },
  projects: [
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] },
    },
    {
      name: 'firefox',
      use: { ...devices['Desktop Firefox'] },
    },
    {
      name: 'webkit',
      use: { ...devices['Desktop Safari'] },
    },
    {
      name: 'Mobile Chrome',
      use: { ...devices['Pixel 5'] },
    },
  ],
  webServer: {
    command: 'npm run dev',
    url: 'http://localhost:3000',
    reuseExistingServer: !process.env.CI,
    timeout: 120 * 1000,
  },
});
'''

    def generate_auth_fixture(self) -> str:
        """Generate authentication fixture"""
        return '''import { test as base, Page } from '@playwright/test';

interface AuthFixtures {
  authenticatedPage: Page;
}

export const test = base.extend<AuthFixtures>({
  authenticatedPage: async ({ page }, use) => {
    // Option 1: Login via UI
    // await page.goto('/login');
    // await page.getByLabel('Email').fill(process.env.TEST_EMAIL || 'test@example.com');
    // await page.getByLabel('Password').fill(process.env.TEST_PASSWORD || 'password');
    // await page.getByRole('button', { name: 'Sign in' }).click();
    // await page.waitForURL('/dashboard');

    // Option 2: Login via API
    // const response = await page.request.post('/api/auth/login', {
    //   data: {
    //     email: process.env.TEST_EMAIL,
    //     password: process.env.TEST_PASSWORD,
    //   },
    // });
    // const { token } = await response.json();
    // await page.context().addCookies([
    //   { name: 'auth-token', value: token, domain: 'localhost', path: '/' }
    // ]);

    await use(page);
  },
});

export { expect } from '@playwright/test';
'''


class E2ETestScaffolder:
    """Main scaffolder class"""

    def __init__(
        self,
        source_path: str,
        output_path: Optional[str] = None,
        include_pom: bool = False,
        routes: Optional[str] = None,
        verbose: bool = False
    ):
        self.source_path = Path(source_path)
        self.output_path = Path(output_path) if output_path else Path('e2e')
        self.include_pom = include_pom
        self.routes_filter = routes.split(',') if routes else None
        self.verbose = verbose
        self.results = {
            'status': 'success',
            'source': str(self.source_path),
            'routes': [],
            'generated_files': [],
            'summary': {}
        }

    def run(self) -> Dict:
        """Run the scaffolder"""
        print(f"Scanning: {self.source_path}")

        # Validate source path
        if not self.source_path.exists():
            raise ValueError(f"Source path does not exist: {self.source_path}")

        # Scan for routes
        scanner = RouteScanner(self.source_path, self.verbose)
        routes = scanner.scan(self.routes_filter)

        print(f"Found {len(routes)} routes")

        # Create output directories
        self.output_path.mkdir(parents=True, exist_ok=True)
        if self.include_pom:
            (self.output_path / 'pages').mkdir(exist_ok=True)

        # Generate test files
        test_generator = TestGenerator(self.include_pom, self.verbose)
        pom_generator = PageObjectGenerator(self.verbose) if self.include_pom else None
        config_generator = ConfigGenerator()

        # Generate tests for each route
        for route in routes:
            # Generate test file
            test_content = test_generator.generate(route)
            test_filename = self._get_test_filename(route.path)
            test_path = self.output_path / test_filename

            test_path.write_text(test_content, encoding='utf-8')

            self.results['generated_files'].append({
                'type': 'test',
                'route': route.path,
                'path': str(test_path)
            })

            print(f"  {test_filename}")

            # Generate Page Object if enabled
            if self.include_pom:
                pom_content = pom_generator.generate(route)
                pom_filename = self._get_pom_filename(route.path)
                pom_path = self.output_path / 'pages' / pom_filename

                pom_path.write_text(pom_content, encoding='utf-8')

                self.results['generated_files'].append({
                    'type': 'page_object',
                    'route': route.path,
                    'path': str(pom_path)
                })

                print(f"  pages/{pom_filename}")

        # Generate config files if not exists
        config_path = Path('playwright.config.ts')
        if not config_path.exists():
            config_content = config_generator.generate_config()
            config_path.write_text(config_content, encoding='utf-8')
            self.results['generated_files'].append({
                'type': 'config',
                'path': str(config_path)
            })
            print(f"  playwright.config.ts")

        # Generate auth fixture
        fixtures_dir = self.output_path / 'fixtures'
        fixtures_dir.mkdir(exist_ok=True)
        auth_fixture_path = fixtures_dir / 'auth.ts'
        if not auth_fixture_path.exists():
            auth_content = config_generator.generate_auth_fixture()
            auth_fixture_path.write_text(auth_content, encoding='utf-8')
            self.results['generated_files'].append({
                'type': 'fixture',
                'path': str(auth_fixture_path)
            })
            print(f"  fixtures/auth.ts")

        # Store route info
        self.results['routes'] = [asdict(r) for r in routes]

        # Summary
        self.results['summary'] = {
            'total_routes': len(routes),
            'total_files': len(self.results['generated_files']),
            'output_directory': str(self.output_path),
            'include_pom': self.include_pom
        }

        print('')
        print(f"Summary: {len(routes)} routes, {len(self.results['generated_files'])} files generated")

        return self.results

    def _get_test_filename(self, route_path: str) -> str:
        """Get test filename from route path"""
        if route_path == '/':
            return 'home.spec.ts'

        name = route_path.strip('/')
        name = re.sub(r'\[([^\]]+)\]', r'\1', name)  # [id] -> id
        name = name.replace('/', '-')
        return f"{name}.spec.ts"

    def _get_pom_filename(self, route_path: str) -> str:
        """Get Page Object filename from route path"""
        if route_path == '/':
            return 'HomePage.ts'

        name = route_path.strip('/')
        name = re.sub(r'\[.*?\]', '', name)
        parts = name.split('/')
        class_name = ''.join(p.title() for p in parts if p) + 'Page'
        return f"{class_name}.ts"


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Generate Playwright E2E tests from Next.js routes",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Scaffold E2E tests for App Router
  python e2e_test_scaffolder.py src/app/ --output e2e/

  # Include Page Object Models
  python e2e_test_scaffolder.py src/app/ --include-pom

  # Generate for specific routes only
  python e2e_test_scaffolder.py src/app/ --routes "/login,/dashboard,/checkout"

  # Verbose output
  python e2e_test_scaffolder.py pages/ -v
        """
    )
    parser.add_argument(
        'source',
        help='Source directory (app/ or pages/)'
    )
    parser.add_argument(
        '--output', '-o',
        default='e2e',
        help='Output directory for test files (default: e2e/)'
    )
    parser.add_argument(
        '--include-pom',
        action='store_true',
        help='Generate Page Object Model classes'
    )
    parser.add_argument(
        '--routes',
        help='Comma-separated list of routes to generate tests for'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output results as JSON'
    )

    args = parser.parse_args()

    try:
        scaffolder = E2ETestScaffolder(
            source_path=args.source,
            output_path=args.output,
            include_pom=args.include_pom,
            routes=args.routes,
            verbose=args.verbose
        )

        results = scaffolder.run()

        if args.json:
            print(json.dumps(results, indent=2))

    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
