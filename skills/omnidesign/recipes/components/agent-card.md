# AI Agent Card

Display card for AI agents, models, or personas with capabilities and status.

## When to Use
- Model selector interfaces
- AI marketplace/agent store
- Multi-agent systems
- Persona selection

## Anatomy

```
┌─────────────────────────────────────────────────────────────┐
│  AgentCard                                                  │
│  ├─ CardHeader (avatar, name, badge)                       │
│  ├─ CardBody (description, capabilities)                   │
│  ├─ CardFooter (status, actions)                           │
│  └─ CapabilityTags (skills, features)                      │
└─────────────────────────────────────────────────────────────┘
```

## Token Usage

```css
/* Card Container */
.agent-card {
  background: var(--color-surface-raised);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-xl);
  padding: var(--spacing-card-padding);
  transition: transform var(--duration-fast), box-shadow var(--duration-fast);
}

.agent-card:hover {
  transform: translateY(-2px);
  box-shadow: var(--shadow-card);
  border-color: var(--color-border-strong);
}

.agent-card.selected {
  border-color: var(--color-interactive-primary);
  box-shadow: 0 0 0 2px var(--color-focus-ring);
}

/* Avatar */
.agent-avatar {
  width: 48px;
  height: 48px;
  border-radius: var(--radius-full);
  background: linear-gradient(135deg, var(--color-interactive-primary), var(--color-interactive-secondary));
  display: flex;
  align-items: center;
  justify-content: center;
  font-weight: var(--font-weight-bold);
  color: var(--color-text-inverted);
}

.agent-avatar img {
  width: 100%;
  height: 100%;
  border-radius: var(--radius-full);
  object-fit: cover;
}

/* Status Badge */
.status-badge {
  font-size: var(--font-size-xs);
  padding: var(--spacing-2xs) var(--spacing-xs);
  border-radius: var(--radius-full);
  font-weight: var(--font-weight-medium);
}

.status-badge.online {
  background: rgba(34, 197, 94, 0.15);
  color: #22C55E;
}

.status-badge.busy {
  background: rgba(245, 158, 11, 0.15);
  color: #F59E0B;
}

.status-badge.offline {
  background: var(--color-surface-sunken);
  color: var(--color-text-muted);
}

/* Capability Tags */
.capability-tag {
  background: var(--color-surface-sunken);
  border: 1px solid var(--color-border-subtle);
  border-radius: var(--radius-sm);
  padding: var(--spacing-2xs) var(--spacing-xs);
  font-size: var(--font-size-xs);
  color: var(--color-text-muted);
}

.capability-tag.highlight {
  background: rgba(37, 99, 235, 0.1);
  border-color: rgba(37, 99, 235, 0.3);
  color: var(--color-interactive-primary);
}

/* Capability Icons */
.capability-icon {
  width: 16px;
  height: 16px;
  color: var(--color-text-muted);
}

.capability-icon.active {
  color: var(--color-interactive-primary);
}
```

## State Matrix

| Element | Default | Hover | Selected | Disabled |
|---------|---------|-------|----------|----------|
| Card | border-default | translateY(-2px) + shadow | border-primary + ring | opacity-50 |
| Avatar | gradient bg | - | ring-2 | grayscale |
| Status Badge | per status | - | - | muted |
| Capability Tag | sunken bg | border-strong | highlight | - |
| Select Button | ghost | subtle bg | primary | - |

## Accessibility

```html
<article 
  class="agent-card" 
  role="button" 
  tabindex="0"
  aria-pressed={isSelected}
  aria-label={`Select ${agent.name}`}
>
  <header class="card-header">
    <div class="agent-avatar" aria-hidden="true">
      <img src={agent.avatar} alt="" />
    </div>
    <div class="agent-info">
      <h3>{agent.name}</h3>
      <span class="status-badge online" aria-label="Status: Online">
        <span class="status-dot" aria-hidden="true"></span>
        Online
      </span>
    </div>
  </header>
  
  <p class="agent-description">{agent.description}</p>
  
  <div class="capabilities" role="list" aria-label="Capabilities">
    {agent.capabilities.map(cap => (
      <span key={cap} class="capability-tag" role="listitem">{cap}</span>
    ))}
  </div>
  
  <footer class="card-footer">
    <span class="model-info">{agent.model}</span>
    <button aria-label={`Use ${agent.name}`}>Select</button>
  </footer>
</article>
```

## Example: Model Selector Grid

```tsx
function ModelSelector({ models, selectedId, onSelect }) {
  return (
    <div className="model-grid" role="radiogroup" aria-label="Select AI model">
      {models.map(model => (
        <AgentCard
          key={model.id}
          model={model}
          isSelected={model.id === selectedId}
          onSelect={() => onSelect(model.id)}
        />
      ))}
    </div>
  );
}

function AgentCard({ model, isSelected, onSelect }) {
  return (
    <article 
      className={`agent-card ${isSelected ? 'selected' : ''}`}
      onClick={onSelect}
      role="radio"
      aria-checked={isSelected}
      tabIndex={0}
      onKeyDown={e => e.key === 'Enter' && onSelect()}
    >
      <header className="card-header">
        <div className="agent-avatar">
          {model.avatar ? (
            <img src={model.avatar} alt="" />
          ) : (
            model.name[0]
          )}
        </div>
        
        <div className="agent-meta">
          <h3 className="agent-name">{model.name}</h3>
          <span className={`status-badge ${model.status}`}>
            <span className="status-dot"></span>
            {model.status}
          </span>
        </div>
        
        {isSelected && <CheckIcon className="selected-icon" aria-hidden="true" />}
      </header>
      
      <p className="agent-description">{model.description}</p>
      
      <div className="capability-list">
        {model.capabilities.map(cap => (
          <span key={cap} className="capability-tag">
            {cap}
          </span>
        ))}
      </div>
      
      <footer className="card-footer">
        <div className="stats">
          <span title="Context window">{formatTokens(model.contextWindow)}</span>
          <span title="Response time">~{model.avgResponseTime}s</span>
        </div>
        
        <button className="select-btn">
          {isSelected ? 'Selected' : 'Use Model'}
        </button>
      </footer>
    </article>
  );
}
```

## Example: AI Agent Store

```tsx
function AgentStore({ agents, onInstall }) {
  const categories = groupByCategory(agents);
  
  return (
    <div className="agent-store">
      {Object.entries(categories).map(([category, agents]) => (
        <section key={category} className="agent-category">
          <h2>{category}</h2>
          <div className="agent-row">
            {agents.map(agent => (
              <AgentStoreCard 
                key={agent.id} 
                agent={agent}
                onInstall={() => onInstall(agent.id)}
              />
            ))}
          </div>
        </section>
      ))}
    </div>
  );
}

function AgentStoreCard({ agent, onInstall }) {
  return (
    <article className="agent-card store-card">
      <header className="card-header">
        <div className="agent-avatar large">
          <img src={agent.avatar} alt="" />
        </div>
        <div>
          <h3>{agent.name}</h3>
          <div className="rating">
            <StarIcon />
            <span>{agent.rating}</span>
            <span className="installs">({formatNumber(agent.installs)} installs)</span>
          </div>
        </div>
      </header>
      
      <p className="description">{agent.description}</p>
      
      <div className="features">
        {agent.features.map(feature => (
          <div key={feature} className="feature-item">
            <CheckIcon className="feature-icon" />
            <span>{feature}</span>
          </div>
        ))}
      </div>
      
      <footer className="card-footer">
        <span className="price">{agent.price === 0 ? 'Free' : `$${agent.price}/mo`}</span>
        <button 
          className="install-btn"
          onClick={onInstall}
          disabled={agent.installed}
        >
          {agent.installed ? 'Installed' : 'Install'}
        </button>
      </footer>
    </article>
  );
}
```

## Tokens Used

- **color**: surface-raised, surface-sunken, interactive-primary, interactive-secondary, text-default, text-inverted, text-muted, border-default, border-strong, border-subtle, focus-ring
- **spacing**: 2xs, xs, card-padding
- **radii**: full, sm, xl
- **shadow**: card
- **typography**: size-xs, weight-medium, weight-bold
- **motion**: duration-fast
