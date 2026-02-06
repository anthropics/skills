# AI Code Block

Syntax-highlighted code display with copy, run, and diff capabilities for AI-generated code.

## When to Use
- Displaying AI-generated code
- Code explanations with syntax highlighting
- Before/after code comparisons
- Interactive code playgrounds
- Terminal/command output

## Anatomy

```
┌─────────────────────────────────────────────────────────────┐
│  CodeBlock                                                  │
│  ├─ BlockHeader (language, filename, actions)              │
│  │   ├─ LanguageBadge                                      │
│  │   ├─ Filename                                           │
│  │   └─ ActionButtons (copy, run, download)                │
│  ├─ BlockContent (syntax highlighted code)                 │
│  │   ├─ LineNumbers (optional)                             │
│  │   └─ CodeContent (highlighted)                          │
│  └─ BlockFooter (execution result, apply button)           │
└─────────────────────────────────────────────────────────────┘
```

## Token Usage

```css
/* Code Block Container */
.code-block {
  background: var(--color-surface-sunken);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-lg);
  overflow: hidden;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  line-height: var(--line-height-snug);
}

/* Block Header */
.code-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: var(--spacing-sm) var(--spacing-md);
  background: rgba(0, 0, 0, 0.2);
  border-bottom: 1px solid var(--color-border-default);
}

.language-badge {
  display: inline-flex;
  align-items: center;
  padding: var(--spacing-2xs) var(--spacing-xs);
  background: rgba(37, 99, 235, 0.15);
  color: var(--color-interactive-primary);
  border-radius: var(--radius-sm);
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-medium);
  text-transform: uppercase;
  letter-spacing: 0.05em;
}

.filename {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-muted);
  margin-left: var(--spacing-sm);
}

/* Action Buttons */
.code-actions {
  display: flex;
  gap: var(--spacing-xs);
}

.code-action-btn {
  display: flex;
  align-items: center;
  gap: var(--spacing-2xs);
  padding: var(--spacing-2xs) var(--spacing-xs);
  background: transparent;
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-md);
  color: var(--color-text-muted);
  font-size: var(--font-size-xs);
  cursor: pointer;
  transition: all var(--duration-fast);
}

.code-action-btn:hover {
  background: var(--color-surface-raised);
  border-color: var(--color-border-strong);
  color: var(--color-text-default);
}

.code-action-btn.success {
  background: rgba(34, 197, 94, 0.15);
  border-color: rgba(34, 197, 94, 0.3);
  color: #22C55E;
}

/* Code Content */
.code-content {
  padding: var(--spacing-md);
  overflow-x: auto;
  background: var(--color-surface-sunken);
}

/* Line Numbers */
.code-with-lines {
  display: flex;
  gap: var(--spacing-md);
}

.line-numbers {
  display: flex;
  flex-direction: column;
  color: var(--color-text-muted);
  font-size: var(--font-size-xs);
  text-align: right;
  user-select: none;
  border-right: 1px solid var(--color-border-default);
  padding-right: var(--spacing-sm);
}

.line-number {
  line-height: 1.8;
}

/* Syntax Highlighting (Shiki/Prism compatible) */
.code-content pre {
  margin: 0;
  background: transparent !important;
}

.code-content code {
  font-family: var(--font-mono);
  font-size: inherit;
  background: transparent;
  padding: 0;
}

/* Diff View */
.code-diff {
  display: flex;
  flex-direction: column;
}

.diff-line {
  display: flex;
  padding: 0 var(--spacing-md);
  line-height: 1.8;
}

.diff-line.added {
  background: rgba(34, 197, 94, 0.1);
}

.diff-line.added::before {
  content: '+';
  color: #22C55E;
  margin-right: var(--spacing-sm);
  font-weight: var(--font-weight-bold);
}

.diff-line.removed {
  background: rgba(239, 68, 68, 0.1);
}

.diff-line.removed::before {
  content: '-';
  color: var(--color-status-error);
  margin-right: var(--spacing-sm);
  font-weight: var(--font-weight-bold);
}

.diff-line.unchanged {
  color: var(--color-text-muted);
}

.diff-line.unchanged::before {
  content: ' ';
  margin-right: var(--spacing-sm);
}

/* Apply Changes Button */
.code-footer {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: var(--spacing-sm) var(--spacing-md);
  background: var(--color-surface-raised);
  border-top: 1px solid var(--color-border-default);
}

.apply-btn {
  display: flex;
  align-items: center;
  gap: var(--spacing-xs);
  padding: var(--spacing-xs) var(--spacing-md);
  background: var(--color-interactive-primary);
  color: var(--color-text-inverted);
  border: none;
  border-radius: var(--radius-md);
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-medium);
  cursor: pointer;
  transition: all var(--duration-fast);
}

.apply-btn:hover {
  background: var(--color-interactive-primary-hover);
}

/* Terminal Style */
.terminal-block {
  background: #0D1117;
  border-radius: var(--radius-lg);
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
}

.terminal-header {
  display: flex;
  align-items: center;
  gap: var(--spacing-sm);
  padding: var(--spacing-sm) var(--spacing-md);
  background: rgba(255, 255, 255, 0.05);
  border-bottom: 1px solid rgba(255, 255, 255, 0.1);
}

.terminal-buttons {
  display: flex;
  gap: 6px;
}

.terminal-btn {
  width: 12px;
  height: 12px;
  border-radius: var(--radius-full);
}

.terminal-btn.red { background: #FF5F56; }
.terminal-btn.yellow { background: #FFBD2E; }
.terminal-btn.green { background: #27C93F; }

.terminal-content {
  padding: var(--spacing-md);
  color: #E6EDF3;
  line-height: 1.6;
}

.terminal-prompt {
  color: #7EE787;
}

.terminal-command {
  color: #E6EDF3;
}

.terminal-output {
  color: #8B949E;
}
```

## State Matrix

| Element | Default | Hover | Copied | Running |
|---------|---------|-------|--------|---------|
| Copy Button | ghost | raised | success green | - |
| Run Button | ghost | raised | - | spinner |
| Apply Button | primary | primary-hover | - | loading |
| Code Block | sunken bg | - | - | - |
| Diff Line | context-based | - | - | - |

## Accessibility

```html
<figure class="code-block" role="region" aria-label="Code example: example.tsx">
  <figcaption class="code-header">
    <div class="file-info">
      <span class="language-badge">TSX</span>
      <span class="filename">example.tsx</span>
    </div>
    
    <div class="code-actions">
      <button 
        class="code-action-btn" 
        aria-label="Copy code to clipboard"
        onClick={handleCopy}
      >
        <CopyIcon aria-hidden="true" />
        <span>Copy</span>
      </button>
      
      <button 
        class="code-action-btn" 
        aria-label="Download file"
        onClick={handleDownload}
      >
        <DownloadIcon aria-hidden="true" />
        <span>Download</span>
      </button>
    </div>
  </figcaption>
  
  <div class="code-with-lines">
    <div class="line-numbers" aria-hidden="true">
      <span class="line-number">1</span>
      <span class="line-number">2</span>
      <span class="line-number">3</span>
    </div>
    
    <pre class="code-content">
      <code>const example = "Hello World";</code>
    </pre>
  </div>
</figure>

<!-- Screen reader announcement -->
<div aria-live="polite" aria-atomic="true" class="sr-only">
  Code copied to clipboard
</div>
```

## Example: Basic Code Block

```tsx
function CodeBlock({ code, language, filename, onCopy }) {
  const [copied, setCopied] = useState(false);
  
  const handleCopy = async () => {
    await navigator.clipboard.writeText(code);
    setCopied(true);
    setTimeout(() => setCopied(false), 2000);
    onCopy?.();
  };
  
  return (
    <figure className="code-block">
      <figcaption className="code-header">
        <div className="file-info">
          <span className="language-badge">{language}</span>
          {filename && <span className="filename">{filename}</span>}
        </div>
        
        <div className="code-actions">
          <button 
            className={`code-action-btn ${copied ? 'success' : ''}`}
            onClick={handleCopy}
            aria-label={copied ? 'Copied' : 'Copy code'}
          >
            {copied ? <CheckIcon /> : <CopyIcon />}
            <span>{copied ? 'Copied!' : 'Copy'}</span>
          </button>
        </div>
      </figcaption>
      
      <div className="code-content">
        <pre>
          <code dangerouslySetInnerHTML={{ __html: highlightedCode }} />
        </pre>
      </div>
    </figure>
  );
}
```

## Example: Code Diff View

```tsx
function CodeDiff({ original, modified, filename }) {
  const diff = computeDiff(original, modified);
  
  return (
    <figure className="code-block diff-view">
      <figcaption className="code-header">
        <span className="filename">{filename}</span>
        <span className="diff-stats">
          <span className="added">+{diff.additions}</span>
          <span className="removed">-{diff.deletions}</span>
        </span>
      </figcaption>
      
      <div className="code-diff">
        {diff.lines.map((line, i) => (
          <div 
            key={i} 
            className={`diff-line ${line.type}`}
            aria-label={line.type === 'added' ? 'Added line' : line.type === 'removed' ? 'Removed line' : 'Unchanged line'}
          >
            <span className="diff-content">{line.content}</span>
          </div>
        ))}
      </div>
      
      <footer className="code-footer">
        <span className="diff-summary">
          {diff.additions} additions, {diff.deletions} deletions
        </span>
        <button className="apply-btn">
          <CheckIcon />
          Apply Changes
        </button>
      </footer>
    </figure>
  );
}
```

## Example: Terminal Output

```tsx
function TerminalBlock({ command, output, workingDir = '~' }) {
  return (
    <div className="terminal-block" role="region" aria-label="Terminal output">
      <div className="terminal-header">
        <div className="terminal-buttons" aria-hidden="true">
          <span className="terminal-btn red"></span>
          <span className="terminal-btn yellow"></span>
          <span className="terminal-btn green"></span>
        </div>
        <span className="terminal-title">Terminal</span>
      </div>
      
      <div className="terminal-content">
        <div className="terminal-line">
          <span className="terminal-prompt">➜ {workingDir}</span>
          <span className="terminal-command"> {command}</span>
        </div>
        
        <div className="terminal-output">
          {output.split('\n').map((line, i) => (
            <div key={i}>{line}</div>
          ))}
        </div>
      </div>
    </div>
  );
}
```

## Example: Runnable Code Block

```tsx
function RunnableCodeBlock({ code, language, onRun }) {
  const [isRunning, setIsRunning] = useState(false);
  const [result, setResult] = useState(null);
  
  const handleRun = async () => {
    setIsRunning(true);
    try {
      const output = await onRun(code);
      setResult({ success: true, output });
    } catch (error) {
      setResult({ success: false, error: error.message });
    } finally {
      setIsRunning(false);
    }
  };
  
  return (
    <figure className="code-block runnable">
      <figcaption className="code-header">
        <span className="language-badge">{language}</span>
        
        <button 
          className="code-action-btn run-btn"
          onClick={handleRun}
          disabled={isRunning}
        >
          {isRunning ? <Spinner /> : <PlayIcon />}
          <span>{isRunning ? 'Running...' : 'Run'}</span>
        </button>
      </figcaption>
      
      <div className="code-content">
        <pre><code>{code}</code></pre>
      </div>
      
      {result && (
        <footer className="code-footer execution-result">
          {result.success ? (
            <div className="success-output">{result.output}</div>
          ) : (
            <div className="error-output">{result.error}</div>
          )}
        </footer>
      )}
    </figure>
  );
}
```

## Tokens Used

- **color**: surface-sunken, surface-raised, interactive-primary, interactive-primary-hover, text-default, text-inverted, text-muted, border-default, border-strong, status-success, status-error
- **spacing**: 2xs, xs, sm, md
- **radii**: sm, md, lg
- **typography**: font-mono, size-xs, size-sm, weight-medium
- **motion**: duration-fast
