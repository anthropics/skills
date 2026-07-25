# WCAG 2.2 New Success Criteria Reference

These criteria were added in WCAG 2.2 and are commonly missed.

## 2.4.11 Focus Appearance (Level AA)

The focus indicator must have a minimum area of a 2px perimeter around the component and a contrast ratio of at least 3:1 against adjacent colors.

**Pattern:**
```css
:focus-visible {
  outline: 2px solid #005fcc;
  outline-offset: 2px;
}
```

## 2.5.7 Dragging Movements (Level AA)

Any functionality that uses dragging must have a single-pointer alternative (click, tap).

**Pattern:**
```tsx
// Sortable list: support both drag and button-based reorder
<li draggable onDragStart={handleDrag}>
  {item.name}
  <button onClick={() => moveUp(index)} aria-label={`Move ${item.name} up`}>
    Move Up
  </button>
  <button onClick={() => moveDown(index)} aria-label={`Move ${item.name} down`}>
    Move Down
  </button>
</li>
```

## 2.5.8 Target Size (Level AA)

Interactive targets must be at least 24x24 CSS pixels, with exceptions for inline text links and elements where the spacing provides equivalent clearance.

**Pattern:**
```css
button, a, input, select, textarea {
  min-height: 24px;
  min-width: 24px;
}

/* Recommended: 44x44px for touch targets */
@media (pointer: coarse) {
  button, a, input[type="checkbox"], input[type="radio"] {
    min-height: 44px;
    min-width: 44px;
  }
}
```

## 3.3.7 Redundant Entry (Level A)

Information previously entered by the user must be auto-populated or available for selection when needed again in the same process.

**Pattern:**
```tsx
// Multi-step form: persist data across steps
const [formData, setFormData] = useState({});

// Step 2 pre-fills shipping address from billing
<input
  defaultValue={formData.billingAddress || ''}
  autoComplete="shipping street-address"
/>
```

## 3.3.8 Accessible Authentication (Level AA)

Authentication must not require cognitive function tests (e.g., remembering a password, solving a puzzle) unless an alternative is provided.

**Pattern:**
- Support password managers (`autocomplete="current-password"`)
- Offer passkey / biometric authentication
- Allow copy-paste in password fields (never block paste)
- Provide email/SMS OTP as alternative to CAPTCHA
