#!/usr/bin/env node
/**
 * Deterministic scaffolder for a new VS Code extension.
 * Usage:
 *   node create-extension.js --name my-ext --displayName "My Ext" \
 *     --description "Does a thing" --publisher local-dev \
 *     --type command --dir /abs/path/to/output
 */
const fs = require('fs');
const path = require('path');

function parseArgs(argv) {
	const out = {};
	for (let i = 0; i < argv.length; i++) {
		const arg = argv[i];
		if (arg.startsWith('--')) {
			const key = arg.slice(2);
			const next = argv[i + 1];
			if (next === undefined || next.startsWith('--')) {
				out[key] = true;
			} else {
				out[key] = next;
				i++;
			}
		}
	}
	return out;
}

const args = parseArgs(process.argv.slice(2));

const name = args.name;
if (!name || !/^[a-z0-9][a-z0-9-]*$/.test(name)) {
	console.error('Error: --name is required and must be a kebab-case identifier (e.g. "my-extension").');
	process.exit(1);
}

const displayName = args.displayName || name.replace(/-/g, ' ').replace(/\b\w/g, (c) => c.toUpperCase());
const description = args.description || `${displayName} for VS Code.`;
const publisher = args.publisher || 'local-dev';
const type = args.type || 'command';
const outDir = path.resolve(args.dir || path.join(process.cwd(), name));

if (!['command', 'theme', 'snippets'].includes(type)) {
	console.error(`Error: --type must be one of command | theme | snippets (got "${type}")`);
	process.exit(1);
}

if (fs.existsSync(outDir) && fs.readdirSync(outDir).length > 0) {
	console.error(`Error: output directory "${outDir}" already exists and is not empty.`);
	process.exit(1);
}

function write(relPath, content) {
	const full = path.join(outDir, relPath);
	fs.mkdirSync(path.dirname(full), { recursive: true });
	fs.writeFileSync(full, content, 'utf8');
}

const year = new Date().getFullYear();

const commonGitignore = `out/\nnode_modules/\n*.vsix\n.vscode-test/\n`;

const readme = `# ${displayName}

${description}

## Features

<!-- Describe the extension's features here. -->

## Requirements

None.

## Extension Settings

This extension does not currently contribute any settings.

## Known Issues

None.

## Release Notes

### 0.0.1

Initial release.
`;

const changelog = `# Change Log

All notable changes to the "${name}" extension will be documented in this file.

## [0.0.1]

- Initial release
`;

const license = `MIT License

Copyright (c) ${year} ${publisher}

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
`;

if (type === 'command') {
	const packageJson = {
		name,
		displayName,
		description,
		version: '0.0.1',
		publisher,
		license: 'MIT',
		engines: { vscode: '^1.85.0' },
		categories: ['Other'],
		activationEvents: [],
		main: './out/extension.js',
		contributes: {
			commands: [
				{
					command: `${name}.helloWorld`,
					title: 'Hello World',
				},
			],
		},
		scripts: {
			'vscode:prepublish': 'npm run compile',
			compile: 'tsc -p ./',
			watch: 'tsc -watch -p ./',
		},
		devDependencies: {
			'@types/vscode': '^1.85.0',
			'@types/node': '^20.0.0',
			typescript: '^5.4.0',
		},
	};
	write('package.json', JSON.stringify(packageJson, null, 2) + '\n');

	write(
		'tsconfig.json',
		JSON.stringify(
			{
				compilerOptions: {
					module: 'commonjs',
					target: 'ES2022',
					outDir: 'out',
					lib: ['ES2022'],
					sourceMap: true,
					rootDir: 'src',
					strict: true,
				},
				exclude: ['node_modules', '.vscode-test'],
			},
			null,
			2
		) + '\n'
	);

	write(
		'src/extension.ts',
		`import * as vscode from 'vscode';

export function activate(context: vscode.ExtensionContext) {
	console.log('${displayName} is now active.');

	const disposable = vscode.commands.registerCommand('${name}.helloWorld', () => {
		vscode.window.showInformationMessage('Hello World from ${displayName}!');
	});

	context.subscriptions.push(disposable);
}

export function deactivate() {}
`
	);

	write(
		'.vscode/launch.json',
		JSON.stringify(
			{
				version: '0.2.0',
				configurations: [
					{
						name: 'Run Extension',
						type: 'extensionHost',
						request: 'launch',
						args: ['--extensionDevelopmentPath=${workspaceFolder}'],
						outFiles: ['${workspaceFolder}/out/**/*.js'],
						preLaunchTask: '${defaultBuildTask}',
					},
				],
			},
			null,
			2
		) + '\n'
	);

	write(
		'.vscode/tasks.json',
		JSON.stringify(
			{
				version: '2.0.0',
				tasks: [
					{
						type: 'npm',
						script: 'watch',
						problemMatcher: '$tsc-watch',
						isBackground: true,
						presentation: { reveal: 'never' },
						group: { kind: 'build', isDefault: true },
					},
				],
			},
			null,
			2
		) + '\n'
	);

	write(
		'.vscodeignore',
		['.vscode/**', '.vscode-test/**', 'src/**', '.gitignore', 'tsconfig.json', '**/*.map', '**/*.ts', 'node_modules/**'].join('\n') + '\n'
	);
} else if (type === 'theme') {
	const themeFileName = `${name}-color-theme.json`;
	const packageJson = {
		name,
		displayName,
		description,
		version: '0.0.1',
		publisher,
		license: 'MIT',
		engines: { vscode: '^1.85.0' },
		categories: ['Themes'],
		contributes: {
			themes: [
				{
					label: displayName,
					uiTheme: 'vs-dark',
					path: `./themes/${themeFileName}`,
				},
			],
		},
	};
	write('package.json', JSON.stringify(packageJson, null, 2) + '\n');

	write(
		`themes/${themeFileName}`,
		JSON.stringify(
			{
				name: displayName,
				type: 'dark',
				colors: {
					'editor.background': '#1e1e1e',
					'editor.foreground': '#d4d4d4',
				},
				tokenColors: [
					{
						scope: ['comment'],
						settings: { foreground: '#6a9955', fontStyle: 'italic' },
					},
					{
						scope: ['keyword'],
						settings: { foreground: '#569cd6' },
					},
					{
						scope: ['string'],
						settings: { foreground: '#ce9178' },
					},
				],
			},
			null,
			2
		) + '\n'
	);

	write('.vscodeignore', ['.vscode/**', '.gitignore'].join('\n') + '\n');
} else if (type === 'snippets') {
	const snippetsFileName = `${name}.code-snippets`;
	const packageJson = {
		name,
		displayName,
		description,
		version: '0.0.1',
		publisher,
		license: 'MIT',
		engines: { vscode: '^1.85.0' },
		categories: ['Snippets'],
		contributes: {
			snippets: [
				{
					language: 'plaintext',
					path: `./snippets/${snippetsFileName}`,
				},
			],
		},
	};
	write('package.json', JSON.stringify(packageJson, null, 2) + '\n');

	write(
		`snippets/${snippetsFileName}`,
		JSON.stringify(
			{
				'Example Snippet': {
					prefix: name,
					body: ['$1'],
					description: 'Example snippet — replace with real snippets.',
				},
			},
			null,
			2
		) + '\n'
	);

	write('.vscodeignore', ['.vscode/**', '.gitignore'].join('\n') + '\n');
}

write('.gitignore', commonGitignore);
write('README.md', readme);
write('CHANGELOG.md', changelog);
write('LICENSE', license);

console.log(`Scaffolded "${type}" extension "${name}" at: ${outDir}`);
