# Form Patterns

Comprehensive form component patterns including input states (default, focus, error, disabled, loading), error message styling, helper text, and label positioning strategies.

## When to Use

**Use form patterns for:**
- User input collection (login, signup, contact)
- Data entry and validation
- Search interfaces
- Filter and sort controls
- Multi-step wizards

**Don't use for:**
- Simple yes/no questions (use toggle or checkbox)
- Single-field searches (use search input pattern)
- Read-only data display (use text, not form fields)

## Component Anatomy

```
┌─────────────────────────────────────────┐
│  [Label]                                │
│  [Input Field]                          │
│  [Helper Text / Error Message]          │
│                                         │
│  Input States:                          │
│  - Default: Neutral appearance          │
│  - Focus: Border highlight, shadow      │
│  - Error: Red border, error icon        │
│  - Disabled: Grayed out, no interaction │
│  - Loading: Spinner, disabled state     │
└─────────────────────────────────────────┘
```

## State Matrix

| State | Visual Treatment | Tokens Used |
|-------|------------------|-------------|
| **Default** | Border `color.border.default`, background `color.surface.sunken`, text `color.text.default` | `color.border.default`, `color.surface.sunken`, `color.text.default` |
| **Focus** | Border `color.interactive.primary`, shadow with blue tint, outline none | `color.interactive.primary`, `color.focus.ring`, `motion.hover` |
| **Error** | Border `color.status.error`, background tinted red, error icon visible | `color.status.error`, `color.surface.sunken`, `color.text.default` |
| **Disabled** | Border `color.border.subtle`, background `color.surface.sunken`, text `color.text.muted`, cursor not-allowed | `color.border.subtle`, `color.text.muted` |
| **Loading** | Spinner icon visible, input disabled, opacity 80% | `color.interactive.primary`, `motion.hover` |
| **Success** | Border `color.status.success`, checkmark icon visible | `color.status.success` |

## Token Usage

### Colors
- **Default Border**: `color.border.default` (neutral 200)
- **Focus Border**: `color.interactive.primary` (blue 500)
- **Error Border**: `color.status.error` (red 500)
- **Success Border**: `color.status.success` (green 500)
- **Input Background**: `color.surface.sunken` (neutral 50)
- **Label Text**: `color.text.default` (neutral 900)
- **Helper Text**: `color.text.muted` (neutral 500)
- **Error Text**: `color.status.error` (red 500)

### Spacing
- **Label Margin**: `space.stackSm` (2px) below label
- **Input Padding**: `space.inputPadding` (3px) internal padding
- **Form Field Gap**: `space.formGap` (4px) between label and input
- **Error Message Margin**: `space.stackSm` (2px) above error text
- **Helper Text Margin**: `space.stackSm` (2px) above helper text

### Typography
- **Label**: `typography.ui.label` (sm, medium)
- **Input**: `typography.body.default` (base, normal)
- **Helper Text**: `typography.ui.caption` (xs, normal)
- **Error Text**: `typography.ui.caption` (xs, normal) with `color.status.error`

### Shadows & Radii
- **Input Radius**: `radius.button` for rounded corners
- **Focus Shadow**: Subtle shadow with blue tint (0 0 0 3px rgba(59, 130, 246, 0.1))

## Implementation Notes

### CSS/HTML Approach

**Structure:**
```
<div class="form-field">
  <label for="email" class="form-field__label">Email Address</label>
  <div class="form-field__input-wrapper">
    <input 
      type="email" 
      id="email" 
      class="form-field__input" 
      placeholder="you@example.com"
      aria-describedby="email-helper"
      required
    >
    <span class="form-field__icon"></span>
  </div>
  <p id="email-helper" class="form-field__helper">We'll never share your email</p>
</div>

<!-- Error state -->
<div class="form-field form-field--error">
  <label for="password" class="form-field__label">Password</label>
  <div class="form-field__input-wrapper">
    <input 
      type="password" 
      id="password" 
      class="form-field__input" 
      aria-describedby="password-error"
      aria-invalid="true"
    >
    <span class="form-field__icon form-field__icon--error"></span>
  </div>
  <p id="password-error" class="form-field__error">Password must be at least 8 characters</p>
</div>
```

**Key CSS patterns:**
- Use `display: flex; flex-direction: column` for vertical label-input stacking
- Apply `border: 1px solid color.border.default` to input
- Use `padding: space.inputPadding` for internal spacing
- Implement focus state with `border-color: color.interactive.primary` and `box-shadow: 0 0 0 3px rgba(59, 130, 246, 0.1)`
- Use `transition: border-color 200ms ease-out, box-shadow 200ms ease-out` for smooth focus
- Apply `background: color.surface.sunken` for input background
- Use `color: color.text.muted` for placeholder text
- Implement error state with `border-color: color.status.error` and `color: color.status.error` for error text
- Use `cursor: not-allowed; opacity: 0.6` for disabled state
- Implement loading state with spinner icon and `pointer-events: none`

**Validation patterns:**
- Show error message only when field is invalid AND touched (not on initial load)
- Use `aria-invalid="true"` to announce error state to screen readers
- Use `aria-describedby` to link input to helper or error text
- Validate on blur (not on every keystroke) to avoid overwhelming user

**Label positioning:**
- Default: Label above input (vertical stack)
- Alternative: Label inside input (floating label) — requires more complex CSS
- Alternative: Label to left of input (horizontal) — use for compact forms

### React Approach

**Component structure:**
- Create `<FormField>` wrapper managing label, input, helper text, and error state
- Create `<Input>` component accepting `type`, `placeholder`, `error`, `disabled`, `loading` props
- Use `useState` for input value and touched state
- Implement `onBlur` to set touched state and trigger validation
- Use `useCallback` for validation logic

**State management:**
- Track input value with `useState`
- Track touched state with `useState` (show errors only when touched)
- Track validation errors with `useState` or validation library (Zod, Yup)
- Use `useEffect` to validate on value change (debounced)

**Validation:**
- Validate on blur (not on every keystroke)
- Show error message only when field is touched AND invalid
- Use validation library (Zod, React Hook Form) for consistency
- Provide real-time feedback for async validation (email availability, username)

**Accessibility:**
- Use `<label>` with `htmlFor` attribute
- Use `aria-invalid="true"` when field has error
- Use `aria-describedby` to link input to helper or error text
- Use `aria-required="true"` for required fields
- Implement focus management for error messages

## Acceptance Criteria

- [ ] Label uses `typography.ui.label` token
- [ ] Input uses `typography.body.default` token
- [ ] Default border uses `color.border.default` token
- [ ] Focus border uses `color.interactive.primary` token
- [ ] Error border uses `color.status.error` token
- [ ] Input background uses `color.surface.sunken` token
- [ ] Input padding uses `space.inputPadding` token
- [ ] Form field gap uses `space.formGap` token
- [ ] Helper text uses `typography.ui.caption` token
- [ ] Error text uses `color.status.error` token
- [ ] Focus ring visible with 3px blue shadow
- [ ] Error message shows only when field is touched AND invalid
- [ ] Disabled state shows cursor not-allowed and reduced opacity
- [ ] Loading state shows spinner and disables input
- [ ] Respects `prefers-reduced-motion` (instant state changes)
- [ ] All text passes color contrast ratio (4.5:1 for body, 3:1 for large text)

## Accessibility

### ARIA & Semantics
- Use `<label>` with `htmlFor` attribute (not placeholder-only labels)
- Use `<input>` with appropriate `type` attribute (email, password, number, etc.)
- Use `aria-invalid="true"` when field has validation error
- Use `aria-describedby` to link input to helper or error text
- Use `aria-required="true"` for required fields
- Use `aria-label` for icon-only inputs (if no visible label)

### Keyboard Navigation
- Tab order: Label (not focusable) → Input → Helper/Error text (not focusable)
- Focus ring must be visible with 3px shadow, `color.focus.ring`
- Ensure focus ring has sufficient contrast against input background
- Support arrow keys for number inputs
- Support Escape to clear input (optional)

### Screen Readers
- Label text must be descriptive and associated with input
- Error message must be announced when field becomes invalid
- Helper text must be announced to provide context
- Required field must be announced with `aria-required="true"`
- Input type must be announced (email, password, etc.)

### Color & Contrast
- Text must meet WCAG AA (4.5:1 for body, 3:1 for large text)
- Error color must have sufficient contrast against background
- Don't rely on color alone to indicate error (use icon + text)
- Ensure sufficient contrast between input text and background

### Motion
- Respect `prefers-reduced-motion: reduce` by disabling animations
- Focus transition should be instant if reduced motion is preferred
- Loading spinner should not animate if reduced motion is preferred

### Touch Targets
- Input minimum height 44px for touch targets
- Label minimum 44px tall for touch targets
- Ensure sufficient spacing between form fields for touch accuracy

### Validation Patterns
- Show errors only when field is touched (not on initial load)
- Provide clear, actionable error messages
- Suggest corrections when possible (e.g., "Did you mean...?")
- Allow user to submit form even with errors (show summary at top)
- Validate on blur, not on every keystroke
- Support async validation (email availability, username) with loading state

### Mobile Considerations
- Use appropriate input types (email, tel, number) for mobile keyboards
- Ensure input height minimum 44px for touch
- Avoid auto-capitalization for email/username fields
- Disable auto-zoom on focus (use font-size >= 16px)
- Test on actual mobile devices for keyboard behavior
