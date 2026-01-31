# Streaming/Thinking Indicator

Visual feedback for AI processing, streaming responses, and loading states.

## When to Use
- AI is generating a response
- Processing user input
- Loading model outputs
- File upload/processing
- Multi-step AI workflows

## Anatomy

```
┌─────────────────────────────────────────────────────────────┐
│  ThinkingIndicator                                          │
│  ├─ Container (message bubble or inline)                   │
│  ├─ Avatar/Icon (AI avatar or status icon)                 │
│  ├─ Animation (dots, wave, pulse, shimmer)                 │
│  ├─ Status Text (optional: "Thinking...", "Processing")    │
│  └─ Cancel Action (optional: stop generation)              │
└─────────────────────────────────────────────────────────────┘
```

## Token Usage

```css
/* Base Container */
.thinking-indicator {
  display: flex;
  align-items: center;
  gap: var(--spacing-sm);
  padding: var(--spacing-md);
  color: var(--color-text-muted);
  font-size: var(--font-size-sm);
}

/* Message Bubble Style */
.thinking-bubble {
  background: var(--color-surface-raised);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-lg) var(--radius-lg) var(--radius-lg) var(--radius-sm);
  padding: var(--spacing-card-padding);
  max-width: 80%;
}

/* Inline Style */
.thinking-inline {
  display: inline-flex;
  align-items: center;
  gap: var(--spacing-xs);
  margin-left: var(--spacing-xs);
}

/* Dots Animation */
.thinking-dots {
  display: flex;
  gap: 4px;
}

.thinking-dots span {
  width: 8px;
  height: 8px;
  background: var(--color-interactive-primary);
  border-radius: var(--radius-full);
  animation: bounce 1.4s ease-in-out infinite both;
}

.thinking-dots span:nth-child(1) { animation-delay: -0.32s; }
.thinking-dots span:nth-child(2) { animation-delay: -0.16s; }
.thinking-dots span:nth-child(3) { animation-delay: 0s; }

@keyframes bounce {
  0%, 80%, 100% { transform: scale(0); }
  40% { transform: scale(1); }
}

/* Wave Animation */
.thinking-wave {
  display: flex;
  align-items: center;
  gap: 3px;
  height: 20px;
}

.thinking-wave span {
  width: 3px;
  background: var(--color-interactive-primary);
  border-radius: var(--radius-full);
  animation: wave 1.2s ease-in-out infinite;
}

.thinking-wave span:nth-child(1) { height: 8px; animation-delay: -0.4s; }
.thinking-wave span:nth-child(2) { height: 12px; animation-delay: -0.3s; }
.thinking-wave span:nth-child(3) { height: 16px; animation-delay: -0.2s; }
.thinking-wave span:nth-child(4) { height: 12px; animation-delay: -0.1s; }
.thinking-wave span:nth-child(5) { height: 8px; animation-delay: 0s; }

@keyframes wave {
  0%, 100% { transform: scaleY(0.5); }
  50% { transform: scaleY(1); }
}

/* Pulse Ring */
.thinking-pulse {
  position: relative;
  width: 40px;
  height: 40px;
}

.thinking-pulse::before,
.thinking-pulse::after {
  content: '';
  position: absolute;
  inset: 0;
  border-radius: var(--radius-full);
  background: var(--color-interactive-primary);
  opacity: 0.6;
  animation: pulse-ring 2s cubic-bezier(0, 0.2, 0.8, 1) infinite;
}

.thinking-pulse::after {
  animation-delay: 1s;
}

@keyframes pulse-ring {
  0% { transform: scale(0.8); opacity: 1; }
  100% { transform: scale(2); opacity: 0; }
}

/* Shimmer Effect */
.thinking-shimmer {
  background: linear-gradient(
    90deg,
    var(--color-surface-sunken) 25%,
    var(--color-surface-raised) 50%,
    var(--color-surface-sunken) 75%
  );
  background-size: 200% 100%;
  border-radius: var(--radius-md);
  animation: shimmer 1.5s infinite;
}

@keyframes shimmer {
  0% { background-position: 200% 0; }
  100% { background-position: -200% 0; }
}

/* Progress Steps */
.progress-steps {
  display: flex;
  gap: var(--spacing-sm);
}

.progress-step {
  display: flex;
  align-items: center;
  gap: var(--spacing-xs);
  padding: var(--spacing-xs) var(--spacing-sm);
  border-radius: var(--radius-full);
  font-size: var(--font-size-xs);
  background: var(--color-surface-sunken);
  color: var(--color-text-muted);
  transition: all var(--duration-fast);
}

.progress-step.active {
  background: rgba(37, 99, 235, 0.15);
  color: var(--color-interactive-primary);
}

.progress-step.completed {
  background: rgba(34, 197, 94, 0.15);
  color: #22C55E;
}

.progress-step-icon {
  width: 16px;
  height: 16px;
}

/* Cancel Button */
.cancel-btn {
  display: flex;
  align-items: center;
  gap: var(--spacing-xs);
  padding: var(--spacing-xs) var(--spacing-sm);
  background: var(--color-surface-sunken);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-md);
  font-size: var(--font-size-xs);
  color: var(--color-text-muted);
  cursor: pointer;
  transition: all var(--duration-fast);
}

.cancel-btn:hover {
  background: rgba(239, 68, 68, 0.1);
  border-color: rgba(239, 68, 68, 0.3);
  color: var(--color-status-error);
}
```

## State Matrix

| Element | Default | Active | Completed | Error |
|---------|---------|--------|-----------|-------|
| Dots | bounce animation | - | fade out | - |
| Wave | wave animation | - | fade out | - |
| Pulse | pulse-ring | - | - | - |
| Progress Step | muted | primary bg | green | red |
| Cancel Button | ghost | hover red | - | - |

## Accessibility

```html
<!-- Screen reader announcements -->
<div aria-live="polite" aria-atomic="true" class="sr-only">
  Assistant is thinking
</div>

<div role="status" aria-label="AI is processing your request">
  <div class="thinking-dots" aria-hidden="true">
    <span></span><span></span><span></span>
  </div>
  <span class="sr-only">Thinking</span>
</div>

<!-- Progress with steps -->
<div role="progressbar" aria-valuemin="0" aria-valuemax="3" aria-valuenow="2" aria-label="Processing steps">
  <div class="progress-steps">
    <div class="progress-step completed" aria-label="Step 1: Analyzing request, completed">
      <CheckIcon /> Analyzing
    </div>
    <div class="progress-step active" aria-label="Step 2: Generating response, in progress">
      <Spinner /> Generating
    </div>
    <div class="progress-step" aria-label="Step 3: Formatting output, pending">
      Formatting
    </div>
  </div>
</div>
```

## Example: Chat Thinking State

```tsx
function ChatThinking({ onCancel }) {
  return (
    <article className="thinking-bubble" aria-live="polite">
      <div className="thinking-indicator">
        <AIAvatar className="avatar-small" />
        
        <div className="thinking-dots" aria-hidden="true">
          <span></span>
          <span></span>
          <span></span>
        </div>
        
        <span className="sr-only">Assistant is thinking</span>
        
        {onCancel && (
          <button 
            className="cancel-btn"
            onClick={onCancel}
            aria-label="Stop generating"
          >
            <StopIcon />
            Stop
          </button>
        )}
      </div>
    </article>
  );
}
```

## Example: Multi-Step Processing

```tsx
function ProcessingSteps({ steps, currentStep }) {
  return (
    <div className="processing-indicator">
      <div className="progress-steps">
        {steps.map((step, index) => {
          const isCompleted = index < currentStep;
          const isActive = index === currentStep;
          
          return (
            <div 
              key={step.id}
              className={`progress-step ${isActive ? 'active' : ''} ${isCompleted ? 'completed' : ''}`}
              aria-current={isActive ? 'step' : undefined}
            >
              {isCompleted ? (
                <CheckIcon className="progress-step-icon" />
              ) : isActive ? (
                <Spinner className="progress-step-icon" />
              ) : (
                <span className="step-number">{index + 1}</span>
              )}
              <span>{step.label}</span>
            </div>
          );
        })}
      </div>
      
      {currentStep < steps.length && (
        <p className="current-step-description">
          {steps[currentStep].description}
        </p>
      )}
    </div>
  );
}

// Usage
const steps = [
  { id: 'analyze', label: 'Analyzing', description: 'Understanding your request...' },
  { id: 'search', label: 'Searching', description: 'Finding relevant information...' },
  { id: 'generate', label: 'Generating', description: 'Creating your response...' },
];

<ProcessingSteps steps={steps} currentStep={1} />
```

## Example: Inline Typing Indicator

```tsx
function InlineThinking() {
  return (
    <span className="thinking-inline" role="status" aria-label="AI is typing">
      <span className="thinking-wave" aria-hidden="true">
        <span></span>
        <span></span>
        <span></span>
        <span></span>
        <span></span>
      </span>
    </span>
  );
}
```

## Example: Skeleton Loading for AI

```tsx
function MessageSkeleton() {
  return (
    <div className="message-skeleton" aria-busy="true" aria-label="Loading message">
      <div className="skeleton-header">
        <div className="thinking-shimmer avatar-skeleton"></div>
        <div className="thinking-shimmer name-skeleton"></div>
      </div>
      
      <div className="skeleton-content">
        <div className="thinking-shimmer line-skeleton" style={{ width: '90%' }}></div>
        <div className="thinking-shimmer line-skeleton" style={{ width: '75%' }}></div>
        <div className="thinking-shimmer line-skeleton" style={{ width: '60%' }}></div>
      </div>
    </div>
  );
}
```

## Tokens Used

- **color**: surface-raised, surface-sunken, interactive-primary, text-muted, status-error, status-success
- **spacing**: xs, sm, md, card-padding
- **radii**: full, md, lg
- **typography**: size-xs, size-sm
- **motion**: duration-fast
