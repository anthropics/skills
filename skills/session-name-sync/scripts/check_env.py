"""Check environment dependencies and install if missing."""
import subprocess, sys, json, os

def check_cc_connect():
    """Check if cc-connect is installed, install if missing."""
    result = subprocess.run(['which', 'cc-connect'], capture_output=True, text=True)
    if result.returncode == 0:
        # Check version
        ver = subprocess.run(['npm', 'list', '-g', 'cc-connect'], capture_output=True, text=True)
        installed = True
        version_line = ver.stdout.strip()
        print(f'cc-connect: OK ({version_line})')
    else:
        print('cc-connect: MISSING')
        installed = False
    return installed

def check_vscode_claude():
    """Check if VSCode Claude Code extension is installed, install if missing."""
    # Check if code CLI exists
    result = subprocess.run(['which', 'code'], capture_output=True, text=True)
    if result.returncode != 0:
        print('VSCode: CLI not found — cannot check extensions')
        return None  # Can't determine

    # List extensions and check for anthropic.claude-code
    ext_result = subprocess.run(['code', '--list-extensions'], capture_output=True, text=True)
    extensions = ext_result.stdout.strip().split('\n') if ext_result.stdout else []
    has_claude = 'anthropic.claude-code' in extensions
    if has_claude:
        print(f'VSCode Claude Code extension: OK (anthropic.claude-code)')
        return True
    else:
        print('VSCode Claude Code extension: MISSING')
        return False

def install_cc_connect():
    """Install cc-connect globally via npm."""
    print('Installing cc-connect...')
    result = subprocess.run(['npm', 'install', '-g', 'cc-connect'], capture_output=True, text=True)
    if result.returncode == 0:
        print(f'cc-connect installed successfully')
        return True
    else:
        print(f'cc-connect install FAILED: {result.stderr}')
        return False

def install_vscode_claude():
    """Install Claude Code VSCode extension."""
    print('Installing anthropic.claude-code VSCode extension...')
    result = subprocess.run(['code', '--install-extension', 'anthropic.claude-code'], capture_output=True, text=True)
    if result.returncode == 0:
        print(f'Claude Code extension installed successfully')
        return True
    else:
        print(f'Claude Code extension install FAILED: {result.stderr}')
        return False

def main():
    print('=== Environment Check ===')

    cc_ok = check_cc_connect()
    vscode_ok = check_vscode_claude()

    missing = []
    if not cc_ok:
        missing.append('cc-connect')
    if vscode_ok is False:
        missing.append('anthropic.claude-code')

    if missing:
        print(f'\nMissing: {", ".join(missing)}')
        if '--install' in sys.argv:
            for dep in missing:
                if dep == 'cc-connect':
                    install_cc_connect()
                elif dep == 'anthropic.claude-code':
                    install_vscode_claude()
            # Re-check after install
            print('\n=== Re-check after install ===')
            check_cc_connect()
            check_vscode_claude()
        else:
            print('Run with --install to auto-install missing dependencies')
    else:
        print('\nAll dependencies OK')

if __name__ == '__main__':
    main()