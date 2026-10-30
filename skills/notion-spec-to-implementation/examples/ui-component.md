# Example: UI Component Implementation

**User Request**: "Implement the new search component from the design spec"

## Workflow

### 1. Find Spec
```
Notion:notion-search
query: "search component design spec"
```
Found: "Global Search Redesign Spec"

### 2. Fetch & Parse Spec
```
Notion:notion-fetch
```

**Requirements**:
- Instant search with debounced API calls
- Keyboard navigation (↑↓ arrows, Enter, Esc)
- Recent searches history
- Result categories (pages, people, files)
- Mobile responsive
- Accessibility (ARIA labels, screen reader)

### 3. Create Implementation Plan
```
Notion:notion-create-pages
```

**Plan phases**:
- Phase 1: Base component structure
- Phase 2: API integration & debouncing
- Phase 3: Keyboard navigation
- Phase 4: Recent searches
- Phase 5: Polish & accessibility

### 4. Create Tasks
```
Notion:notion-create-pages (7 tasks)
```

**Tasks**:
1. Create SearchInput component
2. Implement useDebounce hook
3. Add keyboard navigation
4. LocalStorage for recent searches
5. Result categorization UI
6. Accessibility audit
7. Mobile responsive styling

### 5. Implement & Track
As each task completed, updated status and added progress notes with screenshots and implementation details.

## Key Outputs

**Implementation Plan** (linked to design spec)
**7 Component Tasks** (in Engineering Tasks database)
**Progress Updates** (with code snippets and demo links)

## Success Factors
- Clear component breakdown
- Separated concerns (logic, UI, accessibility)
- Each task had acceptance criteria
- Referenced design spec throughout
- Included accessibility from start, not afterthought
- Tracked progress with visual updates
