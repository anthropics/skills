# AI Prompt Input

Smart input component with prompt suggestions, templates, and autocomplete.

## When to Use
- AI image generation interfaces (Midjourney, DALL-E)
- Prompt engineering tools
- AI writing assistants
- Command palettes with AI

## Anatomy

```
┌─────────────────────────────────────────────────────────────┐
│  PromptInput                                                │
│  ├─ PromptField (textarea with expanding height)           │
│  ├─ PromptToolbar (template buttons, modifiers)            │
│  ├─ SuggestionsDropdown (autocomplete, history)            │
│  ├─ TokenCounter (remaining tokens / cost estimate)        │
│  └─ PromptExamples (preset prompts below input)            │
└─────────────────────────────────────────────────────────────┘
```

## Token Usage

```css
/* Main Input */
.prompt-input {
  background: var(--color-surface-raised);
  border: 2px solid var(--color-border-default);
  border-radius: var(--radius-xl);
  padding: var(--spacing-md);
  transition: border-color var(--duration-fast);
}

.prompt-input:focus-within {
  border-color: var(--color-interactive-primary);
  box-shadow: var(--shadow-focus);
}

/* Textarea */
.prompt-textarea {
  background: transparent;
  border: none;
  color: var(--color-text-default);
  font-family: var(--font-sans);
  font-size: var(--font-size-base);
  line-height: var(--line-height-relaxed);
  resize: none;
  min-height: 3rem;
  max-height: 20rem;
}

/* Suggestions Dropdown */
.suggestions {
  background: var(--color-surface-raised);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-lg);
  box-shadow: var(--shadow-dropdown);
  max-height: 300px;
  overflow-y: auto;
}

.suggestion-item {
  padding: var(--spacing-sm) var(--spacing-md);
  cursor: pointer;
}

.suggestion-item:hover,
.suggestion-item[aria-selected="true"] {
  background: var(--color-surface-sunken);
}

/* Token Counter */
.token-counter {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-muted);
}

.token-counter.warning {
  color: var(--color-status-warning);
}

.token-counter.error {
  color: var(--color-status-error);
}

/* Modifier Tags */
.modifier-tag {
  background: var(--color-surface-sunken);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-full);
  padding: var(--spacing-2xs) var(--spacing-sm);
  font-size: var(--font-size-xs);
  font-family: var(--font-mono);
  cursor: pointer;
}

.modifier-tag:hover {
  background: var(--color-interactive-primary);
  color: var(--color-text-inverted);
  border-color: var(--color-interactive-primary);
}
```

## State Matrix

| Element | Default | Focus | Hover | Active | Disabled |
|---------|---------|-------|-------|--------|----------|
| Input Container | border-default | border-primary + shadow-focus | - | - | opacity-50 |
| Suggestion | transparent | selected bg | sunken bg | - | - |
| Modifier Tag | sunken bg | - | primary bg | - | - |
| Token Counter | muted | - | - | - | - |
| Generate Button | primary | primary-hover | - | pressed | - |

## Accessibility

```html
<div role="combobox" aria-expanded="false" aria-haspopup="listbox" aria-controls="suggestions-list">
  <textarea
    role="textbox"
    aria-autocomplete="list"
    aria-controls="suggestions-list"
    aria-activedescendant=""
    placeholder="Describe what you want to create..."
  ></textarea>
  
  <ul id="suggestions-list" role="listbox" aria-label="Prompt suggestions">
    <li role="option" id="suggestion-1">A futuristic city...</li>
    <li role="option" id="suggestion-2">A serene landscape...</li>
  </ul>
</div>

<div aria-live="polite" aria-atomic="true" class="sr-only">
  50 tokens remaining
</div>
```

## Example: Image Generation Prompt

```tsx
function ImagePromptInput({ onGenerate, maxTokens = 1000 }) {
  const [prompt, setPrompt] = useState('');
  const [tokens, setTokens] = useState(0);
  const [showSuggestions, setShowSuggestions] = useState(false);
  
  const modifiers = [
    { label: '--ar 16:9', desc: 'Aspect ratio' },
    { label: '--v 6', desc: 'Version 6' },
    { label: '--style raw', desc: 'Raw style' },
    { label: '--s 750', desc: 'Stylize' },
  ];
  
  return (
    <div className="prompt-input-container">
      <div className="prompt-input" onClick={() => textareaRef.current?.focus()}>
        <textarea
          ref={textareaRef}
          value={prompt}
          onChange={handleInputChange}
          onFocus={() => setShowSuggestions(true)}
          placeholder="A futuristic city at sunset, cyberpunk style, neon lights reflecting on wet streets..."
          rows={3}
        />
        
        <div className="prompt-toolbar">
          <div className="modifier-chips">
            {modifiers.map(mod => (
              <button
                key={mod.label}
                className="modifier-tag"
                onClick={() => appendModifier(mod.label)}
                title={mod.desc}
              >
                {mod.label}
              </button>
            ))}
          </div>
          
          <TokenCounter current={tokens} max={maxTokens} />
        </div>
      </div>
      
      {showSuggestions && (
        <SuggestionsDropdown 
          query={prompt}
          onSelect={setPrompt}
          onClose={() => setShowSuggestions(false)}
        />
      )}
      
      <div className="prompt-examples">
        <span className="label">Try:</span>
        {EXAMPLE_PROMPTS.map(example => (
          <button
            key={example}
            className="example-chip"
            onClick={() => setPrompt(example)}
          >
            {example.slice(0, 40)}...
          </button>
        ))}
      </div>
      
      <button 
        className="generate-btn"
        disabled={!prompt.trim() || tokens > maxTokens}
        onClick={() => onGenerate(prompt)}
      >
        <SparklesIcon />
        Generate Image
      </button>
    </div>
  );
}

function TokenCounter({ current, max }) {
  const percentage = (current / max) * 100;
  const status = percentage > 90 ? 'error' : percentage > 70 ? 'warning' : '';
  
  return (
    <div className={`token-counter ${status}`}>
      {current.toLocaleString()} / {max.toLocaleString()} tokens
      {status === 'error' && ' (Limit exceeded)'}
    </div>
  );
}
```

## Example: Command Palette with AI

```tsx
function AIPromptPalette({ isOpen, onClose, onExecute }) {
  const [query, setQuery] = useState('');
  const [suggestions, setSuggestions] = useState([]);
  
  return (
    <Modal isOpen={isOpen} onClose={onClose} className="prompt-palette">
      <div className="palette-input">
        <CommandIcon className="input-icon" />
        <input
          type="text"
          value={query}
          onChange={e => setQuery(e.target.value)}
          placeholder="Ask AI to do something..."
          autoFocus
        />
        <kbd className="shortcut">ESC</kbd>
      </div>
      
      <div className="palette-suggestions">
        <section>
          <header>AI Actions</header>
          <SuggestionItem 
            icon={<GenerateIcon />}
            title="Generate code"
            subtitle="Create a React component"
            onClick={() => onExecute('generate', query)}
          />
          <SuggestionItem 
            icon={<ExplainIcon />}
            title="Explain this"
            subtitle="Explain the selected code"
            onClick={() => onExecute('explain', query)}
          />
        </section>
        
        <section>
          <header>Recent Prompts</header>
          {recentPrompts.map(prompt => (
            <SuggestionItem
              key={prompt.id}
              icon={<HistoryIcon />}
              title={prompt.text}
              onClick={() => onExecute('repeat', prompt.text)}
            />
          ))}
        </section>
      </div>
    </Modal>
  );
}
```

## Tokens Used

- **color**: surface-raised, surface-sunken, interactive-primary, text-default, text-inverted, text-muted, border-default, status-warning, status-error
- **spacing**: 2xs, sm, md
- **radii**: full, lg, xl
- **shadow**: focus, dropdown
- **typography**: font-sans, font-mono, size-xs, size-base
- **motion**: duration-fast
