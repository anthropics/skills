# AI Chat Interface

Complete chat UI component for AI-powered applications (ChatGPT/Claude-style).

## When to Use
- AI assistant applications
- Customer support bots
- Code assistant interfaces
- Any conversational AI feature

## Anatomy

```
┌─────────────────────────────────────────────────────────────┐
│  ChatInterface                                              │
│  ├─ ChatHeader (model selector, actions)                   │
│  ├─ ChatMessages (scrollable message list)                 │
│  │   ├─ UserMessage                                        │
│  │   ├─ AssistantMessage                                   │
│  │   │   ├─ MessageHeader (avatar, name, time)            │
│  │   │   ├─ MessageContent (text, code, images)           │
│  │   │   ├─ MessageActions (copy, regenerate, feedback)   │
│  │   │   └─ ThinkingIndicator (streaming state)           │
│  │   └─ SystemMessage (errors, notifications)             │
│  ├─ ChatInput (composer with attachments)                  │
│  └─ SuggestedPrompts (quick-start prompts)                 │
└─────────────────────────────────────────────────────────────┘
```

## Token Usage

```css
/* Chat Container */
.chat-interface {
  background: var(--color-surface-default);
  border-radius: var(--radius-lg);
  font-family: var(--font-sans);
}

/* Message Bubbles */
.user-message {
  background: var(--color-interactive-primary);
  color: var(--color-text-inverted);
  border-radius: var(--radius-lg) var(--radius-lg) var(--radius-sm);
  padding: var(--spacing-card-padding);
}

.assistant-message {
  background: var(--color-surface-raised);
  color: var(--color-text-default);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-lg) var(--radius-lg) var(--radius-lg) var(--radius-sm);
}

/* Code Blocks */
.code-block {
  background: var(--color-surface-sunken);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-md);
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
}

/* Input Area */
.chat-input {
  background: var(--color-surface-raised);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-xl);
  padding: var(--spacing-md);
  box-shadow: var(--shadow-card);
}

/* Thinking Indicator */
.thinking {
  color: var(--color-text-muted);
  font-style: italic;
}

.thinking-dots::after {
  content: '';
  animation: dots 1.5s steps(4, end) infinite;
}

@keyframes dots {
  0%, 20% { content: ''; }
  40% { content: '.'; }
  60% { content: '..'; }
  80%, 100% { content: '...'; }
}
```

## State Matrix

| Element | Default | Hover | Focus | Active | Loading |
|---------|---------|-------|-------|--------|---------|
| User Message | primary bg | - | - | - | - |
| Assistant Message | raised bg | border-strong | - | - | - |
| Send Button | primary | primary-hover | ring | pressed | spinner |
| Code Copy | subtle | default | - | - | checkmark |
| Regenerate | ghost | subtle bg | - | - | spinning |
| Feedback | ghost | icon color | - | selected | - |
| Input | raised | - | ring | - | disabled |

## Accessibility

```html
<!-- Semantic structure -->
<section aria-label="Chat conversation" role="log" aria-live="polite" aria-atomic="false">
  <article aria-label="User message">
    <header><span aria-label="You">User</span></header>
    <div class="message-content"></div>
  </article>
  
  <article aria-label="Assistant message">
    <header><span aria-label="AI Assistant">Claude</span></header>
    <div class="message-content"></div>
    <footer class="message-actions">
      <button aria-label="Copy message">Copy</button>
      <button aria-label="Thumbs up">👍</button>
      <button aria-label="Thumbs down">👎</button>
    </footer>
  </article>
</section>

<!-- Screen reader announcements -->
<div aria-live="assertive" aria-atomic="true" class="sr-only">
  Assistant is typing...
</div>
```

## Responsive Behavior

```css
/* Mobile: Full width messages */
@media (max-width: 768px) {
  .chat-interface {
    border-radius: 0;
    height: 100vh;
  }
  
  .message {
    max-width: 90%;
    margin: var(--spacing-sm);
  }
  
  .chat-input {
    position: fixed;
    bottom: 0;
    left: 0;
    right: 0;
    border-radius: var(--radius-lg) var(--radius-lg) 0 0;
  }
}

/* Desktop: Centered with max-width */
@media (min-width: 1024px) {
  .chat-messages {
    max-width: 800px;
    margin: 0 auto;
    padding: var(--spacing-section-y);
  }
}
```

## Example: Basic Chat Message

```tsx
function ChatMessage({ role, content, isStreaming }) {
  return (
    <article className={`message ${role}`}>
      <header className="message-header">
        <Avatar src={role === 'user' ? userAvatar : aiAvatar} />
        <span className="sender-name">{role === 'user' ? 'You' : 'Assistant'}</span>
        <time>{formatTime(timestamp)}</time>
      </header>
      
      <div className="message-content">
        {isStreaming ? (
          <span className="thinking">Thinking<span className="dots">...</span></span>
        ) : (
          <Markdown content={content} />
        )}
      </div>
      
      {!isStreaming && role === 'assistant' && (
        <footer className="message-actions">
          <button aria-label="Copy" onClick={handleCopy}>
            <CopyIcon />
          </button>
          <button aria-label="Regenerate" onClick={handleRegenerate}>
            <RefreshIcon />
          </button>
          <FeedbackButtons onFeedback={handleFeedback} />
        </footer>
      )}
    </article>
  );
}
```

## Example: Chat Input with Attachments

```tsx
function ChatInput({ onSend, disabled }) {
  const [input, setInput] = useState('');
  const [files, setFiles] = useState([]);
  
  return (
    <div className="chat-input-container">
      {files.length > 0 && (
        <div className="attachment-list">
          {files.map(file => (
            <AttachmentChip key={file.id} file={file} onRemove={removeFile} />
          ))}
        </div>
      )}
      
      <div className="input-row">
        <button aria-label="Attach file" className="attach-btn">
          <PaperclipIcon />
        </button>
        
        <textarea
          value={input}
          onChange={e => setInput(e.target.value)}
          placeholder="Message Assistant..."
          rows={1}
          disabled={disabled}
          aria-label="Message input"
        />
        
        <button 
          aria-label="Send message"
          disabled={!input.trim() || disabled}
          className="send-btn"
          onClick={() => onSend(input, files)}
        >
          {disabled ? <Spinner /> : <SendIcon />}
        </button>
      </div>
    </div>
  );
}
```

## Tokens Used

- **color**: surface-default, surface-raised, surface-sunken, interactive-primary, text-default, text-inverted, text-muted, border-default
- **spacing**: card-padding, md, section-y
- **radii**: sm, md, lg, xl
- **shadow**: card
- **typography**: font-sans, font-mono, size-sm, size-base
