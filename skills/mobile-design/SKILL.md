---
name: mobile-design
description: Design and implementation of production-grade mobile interfaces for React Native / Expo. Applies design standards from top apps (Airbnb, Uber, Instagram). Use this skill for any mobile screen, component, or flow. Ensures clean, modern, organized and professional design.
---

# Mobile Design Skill

This skill guides the creation of React Native / Expo mobile interfaces at the level of the best apps on the market (Airbnb, Uber, Instagram). Every screen should look like it was designed by a senior design team, not by an AI.

## Design reference priorities

By priority order of inspiration:
1. **Airbnb** — primary reference. Clean, airy, perfect visual hierarchy
2. **Uber** — efficiency, clarity, bottom sheets, transactional flows
3. **Instagram** — fluid navigation, immersive feed, polished transitions

### Reference images
**IMPORTANT**: Before starting any new mobile screen or component, check the reference screenshots in `~/.claude/skills/mobile-design/references/`. These images show the expected quality level. Use the Read tool to view them.

The `references/` directory is organized by screen type. Add your own screenshots from apps you admire (Mobbin.com is a great source):

| Folder | What to put in it |
|---|---|
| `references/onboarding/` | Splash screens, welcome, onboarding slides |
| `references/auth/` | Login, phone input, country picker, OTP, signup |
| `references/home-search/` | Home feed, search bar, suggestions |
| `references/search-results/` | Search results, filters, list + map views |
| `references/listing-detail/` | Item detail pages (top section, photos, info) |
| `references/detail-page/` | Immersive detail pages, recap bottom sheets |
| `references/pricing/` | Plans, subscriptions, plan selection |
| `references/payment/` | Checkout, payment methods, confirmations, receipts |
| `references/profile/` | User profile, stats, progression, membership |
| `references/settings/` | Account menu, preferences, settings lists |
| `references/messaging/` | Chat, DM, chatbot, messaging |
| `references/notifications/` | Notification center, badges, alerts |
| `references/empty-states/` | Empty states, no results, empty lists |
| `references/forms/` | Multi-step forms, wizards, filters, upload |
| `references/map/` | Map views, pins, navigation, map bottom sheets |
| `references/content-feed/` | Content feed, cards, explore sections |

**Which refs to check based on the screen you're building:**
| Screen type | Folder(s) to check |
|---|---|
| Onboarding / Welcome | `onboarding/` |
| Login / Signup / OTP | `auth/` |
| Home / Search | `home-search/` |
| Search results | `search-results/` |
| Item / listing detail | `listing-detail/`, `detail-page/` |
| Booking / Pricing | `pricing/` |
| Payment / Checkout | `payment/` |
| User profile | `profile/` |
| Settings / Account | `settings/` |
| Messaging / Chat | `messaging/` |
| Notifications | `notifications/` |
| Empty / Error states | `empty-states/` |
| Forms / Wizards | `forms/` |
| Map | `map/` |
| Lists / Feed | `content-feed/`, `home-search/` |

To add references: place images in the appropriate subfolder of `references/`.

## Core principles

### 1. Strict visual hierarchy
- **One dominant element per screen**: title OR image OR CTA — never all at once
- **Consistent text sizes**: title (20-24px bold), subtitle (16-18px medium), body (14-15px regular), caption (12px regular)
- **Systematic spacing**: use a 4px or 8px grid. No arbitrary spacing
- **Logical grouping**: related elements are close together, distinct groups are separated by whitespace or a thin divider

### 2. Clean and organized
- **No clutter**: every element on screen has a purpose. If it's decorative without function, remove it
- **No unnecessary icons**: plain text > decorative icon. Icons only for navigation and obvious actions
- **Perfect alignment**: all elements aligned on a grid. No 1-2px misalignments
- **Consistent margins**: horizontal padding 16-20px on all screens, never variable

### 3. Native and modern components
- **Bottom sheets** (not centered modals): all modals = bottom sheets with handle bar, swipe down, backdrop tap
- **Buttons**: height 48-50px for main CTAs, border-radius 8-12px, never square corners. Secondary buttons = outline or ghost
- **Inputs**: height 48-50px, border 1px #E0E0E0, border-radius 8-12px, focus state with primary border. Label above (no floating label unless relevant)
- **Cards**: border-radius 12-16px, subtle shadow (shadowOpacity 0.08, shadowRadius 8), or border 1px #F0F0F0
- **Chips/Tags**: border-radius full (999px), horizontal padding 12-16px, height 32-36px

### 4. Colors and contrast
- **Main background**: white (#FFFFFF) or very light gray (#FAFAFA / #F7F7F7)
- **Primary text**: #222222 or #333333 (never pure black #000000)
- **Secondary text**: #717171 (like Airbnb) or #666666
- **Dividers**: #EBEBEB or #F0F0F0 (very subtle, never heavy)
- **Primary color**: use the project's primary color. Use it sparingly: main CTA, active elements, accents. Not everywhere
- **States**: success #008A05, error #C13515, warning #E8A100

### 5. Typography
- **Font**: use the project's defined font with weights: Regular (400), Medium (500), SemiBold (600), Bold (700)
- **No ALL CAPS text** except for very small labels/badges
- **Line height**: 1.4x text size for body, 1.2x for titles
- **No orphan text**: a single word on the last line of a paragraph = rephrase or adjust

### 6. Images and media
- **Consistent ratio**: 3:2 or 4:3 for listing cards, 1:1 for avatars
- **Border-radius**: 12-16px on card images, full circle for avatars
- **Placeholder**: skeleton shimmer during loading, never an empty space
- **Image pagination**: segmented bar (not dots), same style everywhere

### 7. Navigation and structure
- **Bottom tabs**: 5 max, simple icons + labels, active indicator = primary color
- **Headers**: simple and functional. Title centered or left-aligned, back arrow on left, actions on right
- **StatusBar**: always consistent with header (white header → dark-content, dark header → light-content)
- **Safe areas**: respect notches and home indicators on ALL screens

### 8. Lists and scroll
- **FlashList required** (never FlatList) for any scrollable list
- **Pull-to-refresh**: on all data lists
- **Empty state**: illustration or clear message when a list is empty, never a blank screen
- **Loading**: skeleton shimmer, never a centered spinner alone

### 9. Forms
- **KeyboardAvoidingView + ScrollView**: required on ALL forms. Never hide a field behind the keyboard
- **Validation**: error messages below each field in red (#C13515), 12px text
- **Submit button**: always visible, sticky at bottom of screen or after the last field
- **Input states**: default, focused (primary border), error (red border), disabled (opacity 0.5)

### 10. Animations and transitions
- **Subtle and functional**: animations serve UX, not decoration
- **Screen transitions**: use React Navigation native transitions (slide, modal)
- **Micro-interactions**: tactile feedback on buttons (opacity 0.7 on press), like/save animations
- **Duration**: 200-300ms for micro-interactions, 300-500ms for screen transitions
- **No excessive bounce**: fluid animations, no cartoon-like rebounds

## Anti-patterns to ABSOLUTELY avoid

- **No thick borders** (> 1px) on cards or inputs
- **No heavy shadows** (shadowOpacity > 0.15)
- **No irregular spacing** between sections
- **No centered text by default** — left-align except for CTAs and page titles
- **No bright colors everywhere** — primary color is an accent, not a background
- **No floating components** without spatial context
- **No ScrollView for long lists** — always FlashList
- **No overcrowded screens** — if a screen has too many elements, split into scrollable sections
- **No system fonts** or generic fonts — always use the project's defined font
- **No native alert() or confirm()** — always bottom sheets or toasts
- **No blocking loaders** (full screen) except on first load — prefer skeletons

## Checklist before delivering a screen

1. [ ] Spacing follows an 8px grid
2. [ ] Visual hierarchy is clear (one element dominates)
3. [ ] Colors follow the system (primary as accent only)
4. [ ] Text uses the correct font with proper weights
5. [ ] Keyboard doesn't hide any field
6. [ ] Lists use FlashList
7. [ ] Empty/loading/error states are handled
8. [ ] StatusBar matches the header
9. [ ] Safe areas are respected
10. [ ] The screen looks like an Airbnb/Uber app, not a prototype
