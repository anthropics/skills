# Test Case Templates

55 ready-to-use, parametrizable Playwright test templates. Each includes TypeScript and JavaScript examples with `{{placeholder}}` markers for customization.

## Usage

Templates are loaded by `/pw:generate` when it detects a matching scenario. You can also reference them directly:

```
/pw:generate "login flow"  → loads templates/auth/login.md
```

## Template Index

### Authentication (8)

| Template | Tests |
|---|---|
| [login.md](auth/login.md) | Email/password login, social login, remember me |
| [logout.md](auth/logout.md) | Logout from nav, session cleanup |
| [sso.md](auth/sso.md) | SSO redirect flow, callback handling |
| [mfa.md](auth/mfa.md) | 2FA code entry, backup codes |
| [password-reset.md](auth/password-reset.md) | Request reset, enter new password, expired link |
| [session-timeout.md](auth/session-timeout.md) | Auto-logout, session refresh |
| [remember-me.md](auth/remember-me.md) | Persistent login, cookie expiry |
| [rbac.md](auth/rbac.md) | Role-based access, forbidden page |

### CRUD Operations (6)

| Template | Tests |
|---|---|
| [create.md](crud/create.md) | Create entity with form |
| [read.md](crud/read.md) | View details, list view |
| [update.md](crud/update.md) | Edit entity, inline edit |
| [delete.md](crud/delete.md) | Delete with confirmation |
| [bulk-operations.md](crud/bulk-operations.md) | Select multiple, bulk actions |
| [soft-delete.md](crud/soft-delete.md) | Archive, restore |

### Checkout (6)

| Template | Tests |
|---|---|
| [add-to-cart.md](checkout/add-to-cart.md) | Add item, update cart |
| [update-quantity.md](checkout/update-quantity.md) | Increase, decrease, remove |
| [apply-coupon.md](checkout/apply-coupon.md) | Valid/invalid/expired codes |
| [payment.md](checkout/payment.md) | Card form, validation, processing |
| [order-confirm.md](checkout/order-confirm.md) | Success page, order details |
| [order-history.md](checkout/order-history.md) | List orders, pagination |

### Search & Filter (5)

| Template | Tests |
|---|---|
| [basic-search.md](search/basic-search.md) | Search input, results |
| [filters.md](search/filters.md) | Category, price, checkboxes |
| [sorting.md](search/sorting.md) | Sort by name, date, price |
| [pagination.md](search/pagination.md) | Page nav, items per page |
| [empty-state.md](search/empty-state.md) | No results, clear filters |

### Forms (6)

| Template | Tests |
|---|---|
| [single-step.md](forms/single-step.md) | Simple form submission |
| [multi-step.md](forms/multi-step.md) | Wizard with progress |
| [validation.md](forms/validation.md) | Required, format, inline errors |
| [file-upload.md](forms/file-upload.md) | Single, multiple, drag-drop |
| [conditional-fields.md](forms/conditional-fields.md) | Show/hide based on selection |
| [autosave.md](forms/autosave.md) | Draft save, restore |

### Dashboard (5)

| Template | Tests |
|---|---|
| [data-loading.md](dashboard/data-loading.md) | Loading state, skeleton, data |
| [chart-rendering.md](dashboard/chart-rendering.md) | Chart visible, tooltips |
| [date-range-filter.md](dashboard/date-range-filter.md) | Date picker, presets |
| [export.md](dashboard/export.md) | CSV/PDF download |
| [realtime-updates.md](dashboard/realtime-updates.md) | Live data, websocket |

### Settings (4)

| Template | Tests |
|---|---|
| [profile-update.md](settings/profile-update.md) | Name, email, avatar |
| [password-change.md](settings/password-change.md) | Current + new password |
| [notification-prefs.md](settings/notification-prefs.md) | Toggle, save prefs |
| [account-delete.md](settings/account-delete.md) | Confirm deletion |

### Onboarding (4)

| Template | Tests |
|---|---|
| [registration.md](onboarding/registration.md) | Signup form, validation |
| [email-verification.md](onboarding/email-verification.md) | Verify link, resend |
| [welcome-tour.md](onboarding/welcome-tour.md) | Step tour, skip |
| [first-time-setup.md](onboarding/first-time-setup.md) | Initial config |

### Notifications (3)

| Template | Tests |
|---|---|
| [in-app.md](notifications/in-app.md) | Badge, dropdown, mark read |
| [toast-messages.md](notifications/toast-messages.md) | Success/error toasts |
| [notification-center.md](notifications/notification-center.md) | List, filter, clear |

### API Testing (5)

| Template | Tests |
|---|---|
| [rest-crud.md](api/rest-crud.md) | GET/POST/PUT/DELETE |
| [graphql.md](api/graphql.md) | Query, mutation |
| [auth-headers.md](api/auth-headers.md) | Token, expired, refresh |
| [error-responses.md](api/error-responses.md) | 400-500 status handling |
| [rate-limiting.md](api/rate-limiting.md) | Rate limit, retry-after |

### Accessibility (3)

| Template | Tests |
|---|---|
| [keyboard-navigation.md](accessibility/keyboard-navigation.md) | Tab order, focus |
| [screen-reader.md](accessibility/screen-reader.md) | ARIA labels, live regions |
| [color-contrast.md](accessibility/color-contrast.md) | Contrast ratios |
