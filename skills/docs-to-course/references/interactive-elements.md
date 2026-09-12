# Interactive Elements Reference

Implementation patterns for every interactive element type used in courses. Pick the elements that best serve each module's teaching goal.

**Formative elements** (embed mid-module, before summative quiz):
- Prediction Questions — activate prior knowledge before introducing a concept
- Mid-Module Knowledge Checks — single inline question after a key concept
- Completion Problems — faded worked examples with blanks to fill
- Retrieval Callbacks — cross-module transfer questions (Module 3+)

**Primary teaching elements:**
- Spec ↔ Plain English Translation Blocks — the core teaching tool
- Code ↔ English Translation Blocks — for code/config examples in docs
- Decision Tree Navigator — for conditional logic and decision points
- State Machine Visualizer — for protocols and stateful systems

**Assessment elements:**
- Multiple-Choice Quizzes (with elaborative feedback)
- Scenario Quiz
- Drag-and-Drop Matching
- "Spot the Bug" Challenge

**Visual elements:**
- Message Flow / Data Flow Animation
- Interactive Architecture Diagram
- Group Chat Animation
- Layer Toggle Demo
- Callout Boxes
- Pattern/Feature Cards
- Flow Diagrams
- Permission/Config Badges
- Glossary Tooltips
- Visual File Tree
- Icon-Label Rows
- Numbered Step Cards

## Table of Contents
### Formative
1. [Prediction Questions](#prediction-questions)
2. [Mid-Module Knowledge Check](#mid-module-knowledge-check)
3. [Completion Problems](#completion-problems)
4. [Retrieval Callbacks](#retrieval-callbacks)

### Teaching
5. [Spec ↔ Plain English Translation Blocks](#spec--plain-english-translation-blocks)
6. [Code ↔ English Translation Blocks](#code--english-translation-blocks)
7. [Decision Tree Navigator](#decision-tree-navigator)
8. [State Machine Visualizer](#state-machine-visualizer)

### Assessment
9. [Multiple-Choice Quizzes (with elaborative feedback)](#multiple-choice-quizzes)
10. [Scenario Quiz](#scenario-quiz)
11. [Drag-and-Drop Matching](#drag-and-drop-matching)
12. ["Spot the Bug" Challenge](#spot-the-bug-challenge)

### Visual
13. [Message Flow / Data Flow Animation](#message-flow--data-flow-animation)
14. [Interactive Architecture Diagram](#interactive-architecture-diagram)
15. [Group Chat Animation](#group-chat-animation)
16. [Layer Toggle Demo](#layer-toggle-demo)
17. [Callout Boxes](#callout-boxes)
18. [Pattern/Feature Cards](#patternfeature-cards)
19. [Flow Diagrams](#flow-diagrams)
20. [Permission/Config Badges](#permissionconfig-badges)
21. [Glossary Tooltips](#glossary-tooltips)
22. [Visual File Tree](#visual-file-tree)
23. [Icon-Label Rows](#icon-label-rows)
24. [Numbered Step Cards](#numbered-step-cards)

---

## Prediction Questions

Place **before** introducing a concept. Activates prior knowledge, creates a curiosity gap, and makes the correct answer more memorable when it arrives. The prediction is never graded — it's a thinking prompt.

**When to use:** any time you're about to introduce a mechanism, rule, or behavior that has a non-obvious outcome. Ask the learner what they'd expect before showing them what actually happens.

**HTML:**
```html
<div class="prediction-block animate-in" id="pred-ttl">
  <div class="prediction-header">
    <span class="prediction-icon" aria-hidden="true">🤔</span>
    <span class="prediction-label">Before we continue — make a prediction</span>
  </div>
  <p class="prediction-question">
    An intermediate DNS resolver receives a response where the authoritative server set a TTL of 300 seconds.
    The resolver has been caching this record for 120 seconds already.
    <strong>What TTL should the resolver report to the client that just asked for this record?</strong>
  </p>
  <div class="prediction-options">
    <button class="pred-option" onclick="selectPrediction(this, 'pred-ttl')" data-value="a">
      300 seconds — pass through the original TTL
    </button>
    <button class="pred-option" onclick="selectPrediction(this, 'pred-ttl')" data-value="b">
      180 seconds — subtract the time already cached
    </button>
    <button class="pred-option" onclick="selectPrediction(this, 'pred-ttl')" data-value="c">
      120 seconds — the time it has held the record
    </button>
    <button class="pred-option" onclick="selectPrediction(this, 'pred-ttl')" data-value="d">
      It depends on the resolver implementation
    </button>
  </div>
  <div class="prediction-reveal" id="pred-ttl-reveal" aria-live="polite">
    <p class="pred-reveal-text" style="display:none"></p>
  </div>
  <button class="pred-commit-btn" onclick="commitPrediction('pred-ttl')"
          aria-label="Lock in prediction and see the answer">
    Lock in my prediction →
  </button>
</div>
```

**JS:**
```javascript
const predictionAnswers = {
  'pred-ttl': {
    correct: 'b',
    reveal: `The correct answer is <strong>180 seconds</strong> — and this is actually a normative requirement in RFC 2181. The resolver must decrement the TTL by the time it has held the record. The reason: TTL is a freshness guarantee from the <em>authoritative source</em>. If a resolver passed through 300 seconds to every client regardless of how long it had cached the record, a client could receive a record that expires sooner than the TTL suggests — breaking the freshness contract. Keep this in mind as we look at the spec language.`
  }
};

window.selectPrediction = function(btn, id) {
  const block = document.getElementById(id);
  block.querySelectorAll('.pred-option').forEach(b => b.classList.remove('selected'));
  btn.classList.add('selected');
  btn.dataset.selected = 'true';
};

window.commitPrediction = function(id) {
  const block = document.getElementById(id);
  const selected = block.querySelector('.pred-option.selected');
  if (!selected) return;

  const data = predictionAnswers[id];
  const isCorrect = selected.dataset.value === data.correct;
  const revealEl = document.getElementById(`${id}-reveal`);
  const textEl = revealEl.querySelector('.pred-reveal-text');

  // Mark all options — correct answer always highlighted
  block.querySelectorAll('.pred-option').forEach(b => {
    b.disabled = true;
    if (b.dataset.value === data.correct) b.classList.add('pred-correct');
    else if (b.dataset.selected) b.classList.add('pred-incorrect');
  });

  textEl.innerHTML = (isCorrect
    ? '<strong>Good intuition!</strong> '
    : '<strong>Interesting — here\'s what the spec requires:</strong> ')
    + data.reveal;
  textEl.style.display = 'block';
  revealEl.style.display = 'block';

  block.querySelector('.pred-commit-btn').style.display = 'none';
};
```

**CSS:**
```css
.prediction-block {
  background: var(--color-surface-warm);
  border: 2px dashed var(--color-border);
  border-radius: var(--radius-lg);
  padding: var(--space-6);
  margin: var(--space-8) 0;
}
.prediction-header {
  display: flex; align-items: center; gap: var(--space-3);
  margin-bottom: var(--space-4);
}
.prediction-label {
  font-family: var(--font-mono);
  font-size: var(--text-xs);
  text-transform: uppercase;
  letter-spacing: 0.08em;
  color: var(--color-text-secondary);
}
.prediction-question {
  margin-bottom: var(--space-5);
  line-height: var(--leading-normal);
}
.prediction-options {
  display: flex; flex-direction: column; gap: var(--space-2);
  margin-bottom: var(--space-5);
}
.pred-option {
  text-align: left;
  padding: var(--space-3) var(--space-4);
  border: 2px solid var(--color-border);
  border-radius: var(--radius-sm);
  background: var(--color-surface);
  cursor: pointer;
  transition: border-color var(--duration-fast), background var(--duration-fast);
  font-size: var(--text-sm);
}
.pred-option:hover:not(:disabled) { border-color: var(--color-accent-muted); }
.pred-option.selected { border-color: var(--color-accent); background: var(--color-accent-light); }
.pred-option.pred-correct { border-color: var(--color-success); background: var(--color-success-light); }
.pred-option.pred-incorrect { border-color: var(--color-error); background: var(--color-error-light); }
.pred-commit-btn {
  background: var(--color-accent); color: white;
  border: none; border-radius: var(--radius-sm);
  padding: var(--space-3) var(--space-6);
  cursor: pointer; font-weight: 600;
  transition: background var(--duration-fast);
}
.pred-commit-btn:hover { background: var(--color-accent-hover); }
.prediction-reveal {
  display: none;
  background: var(--color-info-light);
  border-left: 3px solid var(--color-info);
  border-radius: var(--radius-sm);
  padding: var(--space-4);
  margin-top: var(--space-4);
  font-size: var(--text-sm);
  line-height: var(--leading-normal);
}
```

**Rules:**
- The question must have a definite answer in the documentation — don't use this for genuinely ambiguous scenarios
- All options should be plausible — avoid obvious wrong answers
- The reveal should reference the spec language the learner is about to see, creating a bridge
- Never grade or score predictions; the point is engagement and curiosity, not assessment

---

## Mid-Module Knowledge Check

A single inline question placed immediately after a key concept is introduced, before moving to the next screen. Catches misunderstanding early. Low stakes — feedback is immediate and non-judgmental.

**When to use:** after introducing any concept that subsequent content builds on. If the learner misunderstands X and you introduce Y that depends on X, you compound the confusion. The check gives them a chance to self-correct.

**HTML:**
```html
<div class="inline-check animate-in" role="group" aria-labelledby="check-q1-label">
  <div class="inline-check-header">
    <span class="check-icon" aria-hidden="true">✓</span>
    <span class="check-label" id="check-q1-label">Quick check</span>
  </div>
  <p class="check-question">
    A resolver receives a NOERROR response with an empty answer section. What does this mean?
  </p>
  <div class="check-options">
    <button class="check-option" onclick="checkInline(this, false, 'check-q1')"
            aria-describedby="check-q1-feedback">
      The record doesn't exist
    </button>
    <button class="check-option" onclick="checkInline(this, true, 'check-q1')"
            aria-describedby="check-q1-feedback">
      The record doesn't exist <em>in the queried name</em>, but the response is valid
    </button>
    <button class="check-option" onclick="checkInline(this, false, 'check-q1')"
            aria-describedby="check-q1-feedback">
      An error occurred on the server
    </button>
  </div>
  <div class="check-feedback" id="check-q1-feedback" aria-live="polite"></div>
</div>
```

**JS:**
```javascript
window.checkInline = function(btn, isCorrect, checkId) {
  const container = btn.closest('.inline-check');
  const feedback = document.getElementById(`${checkId}-feedback`);

  container.querySelectorAll('.check-option').forEach(b => b.disabled = true);
  btn.classList.add(isCorrect ? 'check-correct' : 'check-incorrect');

  if (isCorrect) {
    feedback.innerHTML = '<strong>Exactly.</strong> NOERROR with an empty answer is called NODATA — it means the name exists but has no records of the requested type. This is distinct from NXDOMAIN (name doesn\'t exist at all). Keep the distinction in mind for the next section.';
    feedback.className = 'check-feedback show success';
  } else {
    // Highlight the correct one
    container.querySelectorAll('.check-option').forEach(b => {
      if (b.textContent.trim() !== btn.textContent.trim()) {
        b.classList.add('check-hint');
      }
    });
    feedback.innerHTML = '<strong>Not quite.</strong> NOERROR means the query was processed successfully — the server isn\'t reporting an error. But the empty answer section does have a specific meaning. Look at the highlighted option and read on to see why the distinction matters.';
    feedback.className = 'check-feedback show error';
  }
};
```

**CSS:**
```css
.inline-check {
  background: var(--color-surface);
  border: 1px solid var(--color-border);
  border-radius: var(--radius-md);
  padding: var(--space-5);
  margin: var(--space-6) 0;
}
.inline-check-header {
  display: flex; align-items: center; gap: var(--space-2);
  margin-bottom: var(--space-3);
}
.check-label {
  font-family: var(--font-mono);
  font-size: var(--text-xs);
  text-transform: uppercase;
  letter-spacing: 0.08em;
  color: var(--color-text-secondary);
}
.check-question { margin-bottom: var(--space-4); font-size: var(--text-base); }
.check-options { display: flex; flex-direction: column; gap: var(--space-2); }
.check-option {
  text-align: left; padding: var(--space-3) var(--space-4);
  border: 1px solid var(--color-border-light);
  border-radius: var(--radius-sm); background: var(--color-surface);
  cursor: pointer; font-size: var(--text-sm);
  transition: border-color var(--duration-fast);
}
.check-option:hover:not(:disabled) { border-color: var(--color-accent-muted); }
.check-option.check-correct { border-color: var(--color-success); background: var(--color-success-light); }
.check-option.check-incorrect { border-color: var(--color-error); background: var(--color-error-light); }
.check-option.check-hint { border-color: var(--color-success); }
.check-feedback {
  max-height: 0; overflow: hidden; opacity: 0;
  transition: max-height var(--duration-normal), opacity var(--duration-normal);
  margin-top: var(--space-3); font-size: var(--text-sm);
  border-radius: var(--radius-sm); padding: 0;
}
.check-feedback.show {
  max-height: 200px; opacity: 1;
  padding: var(--space-3) var(--space-4);
}
.check-feedback.success { background: var(--color-success-light); color: var(--color-success); }
.check-feedback.error { background: var(--color-error-light); color: var(--color-error); }
```

---

## Completion Problems

A faded worked example — the learner sees a process partially complete and must fill in the missing steps. More challenging than multiple-choice; more supported than open-ended. Bridges the gap between "follow this worked example" and "now do it yourself."

**When to use:** after a fully worked example has been shown. The completion problem uses the same process but with a different input or scenario, with 1–2 steps left blank. Place before the module's summative quiz.

**HTML:**
```html
<div class="completion-problem animate-in" id="cp-ttl-calc">
  <div class="cp-header">
    <span class="cp-badge">Completion Problem</span>
    <p class="cp-instruction">
      A resolver receives a cached record. Fill in the blanks to trace the correct TTL behavior.
    </p>
  </div>

  <div class="cp-scenario">
    <div class="cp-given">
      <strong>Given:</strong> Authoritative server returned TTL = 600s.
      Resolver has held the record for 400s. Client requests the record.
    </div>
  </div>

  <div class="cp-steps">
    <!-- Completed step (shown) -->
    <div class="cp-step completed">
      <div class="cp-step-num" aria-label="Step 1">1</div>
      <div class="cp-step-body">
        <strong>Check cache freshness</strong>
        <p>600s − 400s = 200s remaining. Record is still fresh (> 0).</p>
      </div>
    </div>

    <!-- Blank step (learner fills) -->
    <div class="cp-step blank">
      <div class="cp-step-num" aria-label="Step 2">2</div>
      <div class="cp-step-body">
        <strong>Determine TTL to return to client</strong>
        <div class="cp-input-group">
          <label class="cp-label" for="cp-ttl-input">Return TTL =</label>
          <input type="number" id="cp-ttl-input" class="cp-input"
                 placeholder="?" aria-describedby="cp-ttl-hint" min="0">
          <span class="cp-unit">seconds</span>
        </div>
        <p id="cp-ttl-hint" class="cp-hint">Hint: RFC 2181 §8 — resolvers must decrement TTL by time held</p>
      </div>
    </div>

    <!-- Blank step -->
    <div class="cp-step blank">
      <div class="cp-step-num" aria-label="Step 3">3</div>
      <div class="cp-step-body">
        <strong>What happens when the client caches this response?</strong>
        <div class="cp-choices">
          <label class="cp-choice">
            <input type="radio" name="cp-client-cache" value="a">
            <span>The client may cache for up to 600 seconds</span>
          </label>
          <label class="cp-choice">
            <input type="radio" name="cp-client-cache" value="b">
            <span>The client may cache for up to 200 seconds</span>
          </label>
          <label class="cp-choice">
            <input type="radio" name="cp-client-cache" value="c">
            <span>The client must not cache — TTL has been altered</span>
          </label>
        </div>
      </div>
    </div>
  </div>

  <button class="cp-check-btn" onclick="checkCompletion('cp-ttl-calc')"
          aria-label="Check my answers">Check answers</button>
  <div class="cp-feedback" id="cp-ttl-calc-feedback" aria-live="polite"></div>
</div>
```

**JS:**
```javascript
const completionAnswers = {
  'cp-ttl-calc': {
    checks: [
      {
        type: 'number',
        inputId: 'cp-ttl-input',
        correct: 200,
        tolerance: 0,
        correctMsg: 'Correct — 200 seconds. The resolver subtracts the time held (400s) from the original TTL (600s).',
        wrongMsg: (val) => `Not quite. The resolver held the record for 400s of a 600s TTL — so ${600 - 400}s remain. You entered ${val}s.`
      },
      {
        type: 'radio',
        name: 'cp-client-cache',
        correct: 'b',
        correctMsg: 'Correct. The client receives a TTL of 200s and may cache for up to that long. This preserves the authoritative server\'s freshness guarantee end-to-end.',
        wrongMsg: 'Not quite. The client should respect the TTL the resolver returned (200s), not the original TTL from the authoritative server. The resolver already decremented it.'
      }
    ]
  }
};

window.checkCompletion = function(id) {
  const data = completionAnswers[id];
  const feedback = document.getElementById(`${id}-feedback`);
  const results = [];

  data.checks.forEach(check => {
    if (check.type === 'number') {
      const input = document.getElementById(check.inputId);
      const val = parseInt(input.value, 10);
      const correct = Math.abs(val - check.correct) <= check.tolerance;
      input.classList.add(correct ? 'cp-correct' : 'cp-incorrect');
      results.push({ correct, msg: correct ? check.correctMsg : check.wrongMsg(val) });
    } else if (check.type === 'radio') {
      const selected = document.querySelector(`input[name="${check.name}"]:checked`);
      const correct = selected && selected.value === check.correct;
      results.push({ correct, msg: correct ? check.correctMsg : check.wrongMsg });
    }
  });

  const allCorrect = results.every(r => r.correct);
  feedback.innerHTML = results.map((r, i) =>
    `<div class="cp-result ${r.correct ? 'success' : 'error'}">
      <strong>Step ${i + 2}:</strong> ${r.msg}
    </div>`
  ).join('');
  feedback.className = 'cp-feedback show';
};
```

**CSS:**
```css
.completion-problem {
  background: var(--color-surface-warm);
  border: 2px solid var(--color-border);
  border-radius: var(--radius-lg);
  padding: var(--space-6);
  margin: var(--space-8) 0;
}
.cp-badge {
  display: inline-block;
  font-family: var(--font-mono); font-size: var(--text-xs);
  text-transform: uppercase; letter-spacing: 0.08em;
  background: var(--color-accent); color: white;
  padding: var(--space-1) var(--space-3);
  border-radius: var(--radius-full);
  margin-bottom: var(--space-3);
}
.cp-scenario {
  background: var(--color-bg-code); color: #CDD6F4;
  border-radius: var(--radius-sm);
  padding: var(--space-4) var(--space-5);
  margin: var(--space-4) 0;
  font-size: var(--text-sm);
}
.cp-steps { display: flex; flex-direction: column; gap: var(--space-4); margin: var(--space-5) 0; }
.cp-step { display: flex; gap: var(--space-4); align-items: flex-start; }
.cp-step-num {
  width: 32px; height: 32px; border-radius: 50%; flex-shrink: 0;
  display: flex; align-items: center; justify-content: center;
  font-weight: 700; font-family: var(--font-display);
}
.cp-step.completed .cp-step-num { background: var(--color-success); color: white; }
.cp-step.blank .cp-step-num { background: var(--color-accent); color: white; }
.cp-step.completed .cp-step-body { opacity: 0.8; }
.cp-input-group { display: flex; align-items: center; gap: var(--space-3); margin: var(--space-3) 0; }
.cp-input {
  width: 80px; padding: var(--space-2) var(--space-3);
  border: 2px solid var(--color-border); border-radius: var(--radius-sm);
  font-size: var(--text-base); font-family: var(--font-mono); text-align: center;
}
.cp-input:focus { outline: 2px solid var(--color-accent); outline-offset: 2px; border-color: transparent; }
.cp-input.cp-correct { border-color: var(--color-success); background: var(--color-success-light); }
.cp-input.cp-incorrect { border-color: var(--color-error); background: var(--color-error-light); }
.cp-hint { font-size: var(--text-xs); color: var(--color-text-muted); margin: var(--space-1) 0 0; }
.cp-choices { display: flex; flex-direction: column; gap: var(--space-2); margin-top: var(--space-3); }
.cp-choice { display: flex; align-items: flex-start; gap: var(--space-3); cursor: pointer; font-size: var(--text-sm); }
.cp-check-btn {
  background: var(--color-accent); color: white; border: none;
  border-radius: var(--radius-sm); padding: var(--space-3) var(--space-6);
  cursor: pointer; font-weight: 600; margin-top: var(--space-4);
}
.cp-feedback { display: none; margin-top: var(--space-4); }
.cp-feedback.show { display: flex; flex-direction: column; gap: var(--space-3); }
.cp-result {
  padding: var(--space-3) var(--space-4);
  border-radius: var(--radius-sm); font-size: var(--text-sm);
}
.cp-result.success { background: var(--color-success-light); color: var(--color-success); }
.cp-result.error { background: var(--color-error-light); color: var(--color-error); }
```

---

## Retrieval Callbacks

A question at the start or end of a module (Module 3+) that asks the learner to apply a concept from an earlier module in a new context. Not a review question — a *transfer* question. The callback makes learning feel cumulative.

**When to use:** once per module from Module 3 onward. Place at the top of the module (before new content) or at the bottom (after the summative quiz, as a bridge to the next module).

**Structure:**
- Name the earlier module/concept explicitly ("In Module 2 we saw that...")
- Present a new scenario that requires applying that concept alongside the new content
- Reveal the answer only after the learner commits
- Bridge to the current module's content ("This connects to what we're about to learn about X")

**HTML:**
```html
<div class="retrieval-callback animate-in" id="rcb-m4">
  <div class="rcb-header">
    <span class="rcb-tag" aria-label="Builds on Module 2">↩ Building on Module 2</span>
    <span class="rcb-label">Retrieval challenge</span>
  </div>
  <p class="rcb-context">
    In Module 2 we learned that resolvers cache responses and decrement TTL as time passes.
  </p>
  <p class="rcb-question">
    <strong>New scenario:</strong> A resolver has a cached record with 50 seconds remaining.
    It receives a new query for the same name but a <em>different record type</em>.
    Must it return the cached record? What should it do?
  </p>
  <div class="rcb-options">
    <button class="rcb-option" onclick="commitRcb(this, 'rcb-m4', false)">
      Yes — the name is the same, so the cache entry applies
    </button>
    <button class="rcb-option" onclick="commitRcb(this, 'rcb-m4', false)">
      No — it must discard the cache and query fresh
    </button>
    <button class="rcb-option" onclick="commitRcb(this, 'rcb-m4', true)">
      No — cache entries are keyed by name <em>and</em> type; this is a cache miss
    </button>
  </div>
  <div class="rcb-reveal" id="rcb-m4-reveal" aria-live="polite" style="display:none">
    <p>Cache entries are keyed by the tuple (name, type, class). A query for <code>example.com A</code> and <code>example.com AAAA</code> are separate cache entries even though the name is identical. This matters for Module 4 because...</p>
    <p class="rcb-bridge">This module explores exactly how that tuple works and what happens when it collides. Keep this scenario in mind as we go.</p>
  </div>
</div>
```

**JS:**
```javascript
window.commitRcb = function(btn, id, isCorrect) {
  const block = document.getElementById(id);
  block.querySelectorAll('.rcb-option').forEach(b => {
    b.disabled = true;
    if (b === btn) b.classList.add(isCorrect ? 'rcb-correct' : 'rcb-incorrect');
    if (isCorrect && b !== btn) b.classList.add('rcb-dim');
    if (!isCorrect && b.dataset.correct) b.classList.add('rcb-correct');
  });
  // Mark correct option if wrong
  if (!isCorrect) {
    block.querySelectorAll('.rcb-option').forEach(b => {
      if (b.textContent.includes('name and type')) b.classList.add('rcb-correct');
    });
  }
  document.getElementById(`${id}-reveal`).style.display = 'block';
};
```

**CSS:**
```css
.retrieval-callback {
  background: linear-gradient(135deg, var(--color-bg-warm), var(--color-surface-warm));
  border-left: 4px solid var(--color-accent);
  border-radius: 0 var(--radius-md) var(--radius-md) 0;
  padding: var(--space-5) var(--space-6);
  margin: var(--space-8) 0;
}
.rcb-header {
  display: flex; align-items: center; gap: var(--space-3);
  margin-bottom: var(--space-4);
}
.rcb-tag {
  font-family: var(--font-mono); font-size: var(--text-xs);
  text-transform: uppercase; letter-spacing: 0.06em;
  background: var(--color-accent-light); color: var(--color-accent);
  border: 1px solid var(--color-accent-muted);
  padding: var(--space-1) var(--space-3); border-radius: var(--radius-full);
}
.rcb-label {
  font-size: var(--text-xs); text-transform: uppercase; letter-spacing: 0.06em;
  color: var(--color-text-muted);
}
.rcb-context { color: var(--color-text-secondary); font-size: var(--text-sm); margin-bottom: var(--space-3); }
.rcb-question { margin-bottom: var(--space-4); }
.rcb-options { display: flex; flex-direction: column; gap: var(--space-2); }
.rcb-option {
  text-align: left; padding: var(--space-3) var(--space-4);
  border: 1px solid var(--color-border); border-radius: var(--radius-sm);
  background: var(--color-surface); cursor: pointer; font-size: var(--text-sm);
}
.rcb-option:hover:not(:disabled) { border-color: var(--color-accent-muted); }
.rcb-option.rcb-correct { border-color: var(--color-success); background: var(--color-success-light); }
.rcb-option.rcb-incorrect { border-color: var(--color-error); background: var(--color-error-light); }
.rcb-option.rcb-dim { opacity: 0.45; }
.rcb-reveal {
  margin-top: var(--space-4); padding: var(--space-4);
  background: var(--color-surface); border-radius: var(--radius-sm);
  font-size: var(--text-sm); line-height: var(--leading-normal);
}
.rcb-bridge {
  margin-top: var(--space-3); font-style: italic;
  color: var(--color-text-secondary);
}
```

---

## Decision Tree Navigator

For documentation that describes conditional logic — "if X, do A; if Y, do B; unless Z, in which case..." A clickable decision tree where the learner navigates a real scenario step by step, making choices and seeing the consequences.

**When to use:** any time the documentation contains decision logic, routing rules, priority tables, or "it depends" scenarios. Much more effective than a list of rules.

**HTML:**
```html
<div class="decision-tree" id="dt-rcode" role="region" aria-label="DNS RCODE decision tree">
  <div class="dt-header">
    <span class="dt-label">Interactive: Handling DNS Response Codes</span>
    <button class="dt-reset" onclick="resetDT('dt-rcode')"
            aria-label="Reset decision tree">Start over</button>
  </div>

  <!-- Scenario context -->
  <div class="dt-scenario">
    <strong>Scenario:</strong> Your resolver just received a DNS response.
    Walk through how to handle it correctly.
  </div>

  <!-- Node 0: root -->
  <div class="dt-node active" id="dt-rcode-0" aria-live="polite">
    <p class="dt-question">What is the RCODE in the response header?</p>
    <div class="dt-choices">
      <button class="dt-choice" onclick="dtNavigate('dt-rcode', 0, 'noerror')"
              aria-label="RCODE is NOERROR (0)">
        <span class="dt-choice-label">NOERROR (0)</span>
        <span class="dt-choice-hint">Query processed successfully</span>
      </button>
      <button class="dt-choice" onclick="dtNavigate('dt-rcode', 0, 'nxdomain')"
              aria-label="RCODE is NXDOMAIN (3)">
        <span class="dt-choice-label">NXDOMAIN (3)</span>
        <span class="dt-choice-hint">Name does not exist</span>
      </button>
      <button class="dt-choice" onclick="dtNavigate('dt-rcode', 0, 'servfail')"
              aria-label="RCODE is SERVFAIL (2)">
        <span class="dt-choice-label">SERVFAIL (2)</span>
        <span class="dt-choice-hint">Server could not complete the query</span>
      </button>
    </div>
  </div>

  <!-- Node: NOERROR branch -->
  <div class="dt-node" id="dt-rcode-noerror" hidden>
    <div class="dt-breadcrumb">NOERROR →</div>
    <p class="dt-question">Does the Answer section contain records?</p>
    <div class="dt-choices">
      <button class="dt-choice" onclick="dtNavigate('dt-rcode', 'noerror', 'answer-yes')">
        <span class="dt-choice-label">Yes — records present</span>
      </button>
      <button class="dt-choice" onclick="dtNavigate('dt-rcode', 'noerror', 'answer-no')">
        <span class="dt-choice-label">No — answer section is empty</span>
      </button>
    </div>
  </div>

  <!-- Terminal nodes -->
  <div class="dt-node dt-terminal" id="dt-rcode-answer-yes" hidden>
    <div class="dt-breadcrumb">NOERROR → Records present →</div>
    <div class="dt-outcome success">
      <strong>Cache and return the records.</strong>
      <p>Cache each RR respecting its TTL. Return the answer to the client. This is the happy path.</p>
      <div class="dt-spec-ref">RFC 1035 §3.2 — each resource record is cached independently with its own TTL.</div>
    </div>
  </div>

  <div class="dt-node dt-terminal" id="dt-rcode-answer-no" hidden>
    <div class="dt-breadcrumb">NOERROR → Empty answer →</div>
    <div class="dt-outcome warning">
      <strong>This is NODATA — cache the negative response.</strong>
      <p>The name exists but has no records of the requested type. Cache this negative result using the SOA TTL from the authority section to prevent hammering the authoritative server.</p>
      <div class="dt-spec-ref">RFC 2308 §3 — negative caching of NODATA responses.</div>
    </div>
  </div>

  <div class="dt-node dt-terminal" id="dt-rcode-nxdomain" hidden>
    <div class="dt-breadcrumb">NXDOMAIN →</div>
    <div class="dt-outcome warning">
      <strong>Cache the negative response, return NXDOMAIN to client.</strong>
      <p>The name does not exist. Cache for the SOA minimum TTL. Distinguish from NODATA: NXDOMAIN means the name is gone entirely — not just this record type.</p>
      <div class="dt-spec-ref">RFC 2308 §2 — NXDOMAIN caching and SOA TTL.</div>
    </div>
  </div>

  <div class="dt-node dt-terminal" id="dt-rcode-servfail" hidden>
    <div class="dt-breadcrumb">SERVFAIL →</div>
    <div class="dt-outcome error">
      <strong>Do not cache. Retry with backoff or return error to client.</strong>
      <p>SERVFAIL indicates a server-side failure — the authoritative server may be temporarily unreachable or misconfigured. Caching this would poison the cache.</p>
      <div class="dt-spec-ref">RFC 4035 §5.3 — SERVFAIL is used by DNSSEC validators to signal validation failure; behavior varies by context.</div>
    </div>
  </div>

  <!-- Path history -->
  <div class="dt-path" id="dt-rcode-path" aria-live="polite"></div>
</div>
```

**JS:**
```javascript
const dtGraphs = {
  'dt-rcode': {
    // adjacency: nodeId → { choiceValue: nextNodeId }
    0: { noerror: 'noerror', nxdomain: 'nxdomain', servfail: 'servfail' },
    noerror: { 'answer-yes': 'answer-yes', 'answer-no': 'answer-no' },
  }
};

const dtPaths = {};

window.dtNavigate = function(treeId, fromNode, choice) {
  const tree = document.getElementById(treeId);
  const graph = dtGraphs[treeId];
  const nextId = graph[fromNode]?.[choice];
  if (!nextId) return;

  // Hide current node
  const current = tree.querySelector('.dt-node.active');
  if (current) current.classList.remove('active');

  // Show next node
  const next = document.getElementById(`${treeId}-${nextId}`);
  if (next) {
    next.hidden = false;
    next.classList.add('active');
    next.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  }

  // Track path
  if (!dtPaths[treeId]) dtPaths[treeId] = [];
  dtPaths[treeId].push(choice);
  const pathEl = document.getElementById(`${treeId}-path`);
  if (pathEl) pathEl.textContent = 'Your path: ' + dtPaths[treeId].join(' → ');
};

window.resetDT = function(treeId) {
  const tree = document.getElementById(treeId);
  tree.querySelectorAll('.dt-node').forEach(n => {
    n.hidden = true;
    n.classList.remove('active');
  });
  const root = document.getElementById(`${treeId}-0`);
  root.hidden = false;
  root.classList.add('active');
  dtPaths[treeId] = [];
  const pathEl = document.getElementById(`${treeId}-path`);
  if (pathEl) pathEl.textContent = '';
};
```

**CSS:**
```css
.decision-tree {
  background: var(--color-surface-warm);
  border: 1px solid var(--color-border);
  border-radius: var(--radius-lg);
  padding: var(--space-6);
  margin: var(--space-8) 0;
}
.dt-header {
  display: flex; justify-content: space-between; align-items: center;
  margin-bottom: var(--space-5);
}
.dt-label {
  font-family: var(--font-mono); font-size: var(--text-xs);
  text-transform: uppercase; letter-spacing: 0.08em;
  color: var(--color-text-secondary);
}
.dt-reset {
  font-size: var(--text-xs); padding: var(--space-1) var(--space-3);
  border: 1px solid var(--color-border); border-radius: var(--radius-sm);
  background: var(--color-surface); cursor: pointer;
}
.dt-scenario {
  background: var(--color-bg-code); color: #CDD6F4;
  padding: var(--space-3) var(--space-4); border-radius: var(--radius-sm);
  font-size: var(--text-sm); margin-bottom: var(--space-5);
}
.dt-node { animation: fadeSlideUp 0.25s var(--ease-out); }
.dt-question { font-weight: 600; margin-bottom: var(--space-4); }
.dt-choices { display: flex; flex-direction: column; gap: var(--space-2); }
.dt-choice {
  display: flex; flex-direction: column; gap: var(--space-1);
  text-align: left; padding: var(--space-4);
  border: 2px solid var(--color-border); border-radius: var(--radius-sm);
  background: var(--color-surface); cursor: pointer;
  transition: border-color var(--duration-fast), transform var(--duration-fast);
}
.dt-choice:hover { border-color: var(--color-accent); transform: translateX(4px); }
.dt-choice:focus-visible { outline: 2px solid var(--color-accent); outline-offset: 2px; }
.dt-choice-label { font-weight: 600; font-family: var(--font-mono); font-size: var(--text-sm); }
.dt-choice-hint { font-size: var(--text-xs); color: var(--color-text-secondary); }
.dt-breadcrumb {
  font-family: var(--font-mono); font-size: var(--text-xs);
  color: var(--color-text-muted); margin-bottom: var(--space-3);
}
.dt-outcome {
  padding: var(--space-5); border-radius: var(--radius-md);
  border-left: 4px solid;
}
.dt-outcome.success { background: var(--color-success-light); border-color: var(--color-success); }
.dt-outcome.warning { background: var(--color-accent-light); border-color: var(--color-accent); }
.dt-outcome.error { background: var(--color-error-light); border-color: var(--color-error); }
.dt-spec-ref {
  margin-top: var(--space-3); font-size: var(--text-xs);
  font-family: var(--font-mono); color: var(--color-text-muted);
}
.dt-path {
  margin-top: var(--space-4); font-size: var(--text-xs);
  color: var(--color-text-muted); font-family: var(--font-mono);
}
@keyframes fadeSlideUp {
  from { opacity: 0; transform: translateY(8px); }
  to   { opacity: 1; transform: translateY(0); }
}
```

---

## State Machine Visualizer

For documentation describing protocols, lifecycle states, or any system with explicit states and transitions (connection states, record lifecycle, authentication flows). Shows states as nodes and transitions as labeled edges. The learner triggers transitions by clicking.

**When to use:** any time the documentation has a state diagram, lifecycle table, or "when in state X, upon event Y, transition to state Z" language.

**HTML:**
```html
<div class="state-machine" id="sm-tcp" role="region" aria-label="TCP connection state machine">
  <div class="sm-header">
    <span class="sm-label">TCP Connection States (simplified)</span>
    <div class="sm-controls">
      <button class="sm-trigger" onclick="smTrigger('sm-tcp', 'syn_sent')"
              aria-label="Send SYN">Send SYN</button>
      <button class="sm-trigger" onclick="smTrigger('sm-tcp', 'established')"
              aria-label="Receive SYN-ACK">SYN-ACK received</button>
      <button class="sm-trigger" onclick="smTrigger('sm-tcp', 'fin_wait')"
              aria-label="Send FIN">Send FIN</button>
      <button class="sm-trigger" onclick="smTrigger('sm-tcp', 'closed')"
              aria-label="Close">Close</button>
      <button class="sm-reset-btn" onclick="smReset('sm-tcp')"
              aria-label="Reset to initial state">Reset</button>
    </div>
  </div>

  <div class="sm-canvas">
    <div class="sm-state" id="sm-tcp-closed" data-state="closed" aria-current="true">
      <span class="sm-state-name">CLOSED</span>
      <span class="sm-state-desc">No connection</span>
    </div>
    <div class="sm-arrow sm-arrow-right" aria-hidden="true">→<span class="sm-arrow-label">SYN</span></div>
    <div class="sm-state" id="sm-tcp-syn_sent" data-state="syn_sent">
      <span class="sm-state-name">SYN_SENT</span>
      <span class="sm-state-desc">Waiting for SYN-ACK</span>
    </div>
    <div class="sm-arrow sm-arrow-right" aria-hidden="true">→<span class="sm-arrow-label">SYN-ACK</span></div>
    <div class="sm-state" id="sm-tcp-established" data-state="established">
      <span class="sm-state-name">ESTABLISHED</span>
      <span class="sm-state-desc">Data transfer active</span>
    </div>
    <div class="sm-arrow sm-arrow-down" aria-hidden="true">↓<span class="sm-arrow-label">FIN</span></div>
    <div class="sm-state" id="sm-tcp-fin_wait" data-state="fin_wait">
      <span class="sm-state-name">FIN_WAIT_1</span>
      <span class="sm-state-desc">Closing initiated</span>
    </div>
    <div class="sm-arrow sm-arrow-right" aria-hidden="true">→<span class="sm-arrow-label">ACK + FIN</span></div>
    <div class="sm-state" id="sm-tcp-closed2" data-state="closed">
      <span class="sm-state-name">CLOSED</span>
      <span class="sm-state-desc">Connection terminated</span>
    </div>
  </div>

  <div class="sm-info" id="sm-tcp-info" aria-live="polite">
    <strong>Current state: CLOSED</strong>
    <p>No active connection. Waiting for either a passive open (listen) or an active open (connect).</p>
  </div>
</div>
```

**JS:**
```javascript
const smDefinitions = {
  'sm-tcp': {
    states: {
      closed:      { label: 'CLOSED',      desc: 'No active connection. Waiting for passive or active open.' },
      syn_sent:    { label: 'SYN_SENT',    desc: 'Active open initiated. SYN sent, waiting for SYN-ACK from the server.' },
      established: { label: 'ESTABLISHED', desc: 'Three-way handshake complete. Data transfer is active. This is the normal operating state.' },
      fin_wait:    { label: 'FIN_WAIT_1',  desc: 'Close initiated by this side. FIN sent, waiting for acknowledgement.' },
    },
    current: 'closed'
  }
};

window.smTrigger = function(machineId, targetState) {
  const sm = smDefinitions[machineId];
  const stateData = sm.states[targetState];
  if (!stateData) return;

  // Deactivate current
  const machine = document.getElementById(machineId);
  machine.querySelectorAll('.sm-state').forEach(el => {
    el.classList.remove('sm-active');
    el.removeAttribute('aria-current');
  });

  // Activate new state
  const stateEl = document.getElementById(`${machineId}-${targetState}`);
  if (stateEl) {
    stateEl.classList.add('sm-active');
    stateEl.setAttribute('aria-current', 'true');
  }

  sm.current = targetState;

  // Update info panel
  const info = document.getElementById(`${machineId}-info`);
  info.innerHTML = `<strong>Current state: ${stateData.label}</strong><p>${stateData.desc}</p>`;
};

window.smReset = function(machineId) {
  smTrigger(machineId, 'closed');
};
```

**CSS:**
```css
.state-machine {
  background: var(--color-surface-warm);
  border: 1px solid var(--color-border);
  border-radius: var(--radius-lg);
  padding: var(--space-6);
  margin: var(--space-8) 0;
}
.sm-header {
  display: flex; flex-wrap: wrap; gap: var(--space-4);
  justify-content: space-between; align-items: center;
  margin-bottom: var(--space-5);
}
.sm-label {
  font-family: var(--font-mono); font-size: var(--text-xs);
  text-transform: uppercase; letter-spacing: 0.08em;
  color: var(--color-text-secondary);
}
.sm-controls { display: flex; flex-wrap: wrap; gap: var(--space-2); }
.sm-trigger {
  padding: var(--space-2) var(--space-4);
  border: 1px solid var(--color-accent-muted); border-radius: var(--radius-sm);
  background: var(--color-accent-light); color: var(--color-accent);
  cursor: pointer; font-size: var(--text-xs); font-weight: 600;
  transition: background var(--duration-fast), border-color var(--duration-fast);
}
.sm-trigger:hover { background: var(--color-accent); color: white; }
.sm-trigger:focus-visible { outline: 2px solid var(--color-accent); outline-offset: 2px; }
.sm-reset-btn {
  padding: var(--space-2) var(--space-4);
  border: 1px solid var(--color-border); border-radius: var(--radius-sm);
  background: var(--color-surface); cursor: pointer; font-size: var(--text-xs);
}
.sm-canvas {
  display: flex; flex-wrap: wrap; align-items: center;
  gap: var(--space-2); margin: var(--space-5) 0;
  overflow-x: auto; padding-bottom: var(--space-2);
}
.sm-state {
  display: flex; flex-direction: column; align-items: center;
  padding: var(--space-4) var(--space-5);
  border: 2px solid var(--color-border);
  border-radius: var(--radius-md);
  background: var(--color-surface);
  min-width: 120px; text-align: center;
  transition: all var(--duration-normal) var(--ease-out);
}
.sm-state.sm-active {
  border-color: var(--color-accent);
  background: var(--color-accent-light);
  box-shadow: 0 0 0 3px var(--color-accent-light), var(--shadow-md);
  transform: scale(1.04);
}
.sm-state-name {
  font-family: var(--font-mono); font-size: var(--text-xs);
  font-weight: 700; letter-spacing: 0.05em;
}
.sm-state-desc { font-size: var(--text-xs); color: var(--color-text-secondary); margin-top: var(--space-1); }
.sm-arrow {
  display: flex; flex-direction: column; align-items: center;
  color: var(--color-text-muted); font-size: 1.25rem; position: relative;
}
.sm-arrow-label {
  font-size: var(--text-xs); font-family: var(--font-mono);
  color: var(--color-text-muted); white-space: nowrap;
}
.sm-info {
  background: var(--color-surface); border-radius: var(--radius-sm);
  padding: var(--space-4); margin-top: var(--space-4); font-size: var(--text-sm);
  border-left: 3px solid var(--color-accent);
}
```

---

## Spec ↔ Plain English Translation Blocks

The primary teaching element for docs-to-course. Shows verbatim text from the documentation on the left (styled as a blockquote to signal "official language") and a plain-English translation on the right that explains what it means, why it matters, and what to watch out for.

**HTML:**
```html
<div class="translation-block animate-in">
  <div class="translation-spec">
    <span class="translation-label">SPEC</span>
    <blockquote class="spec-excerpt">
      <p>Each RR in the answer section MUST have a TTL no greater than the TTL field in the original record set, and MUST NOT have a TTL of zero unless the original record set had a TTL of zero.</p>
    </blockquote>
    <cite class="spec-cite">RFC 2181, Section 5.2</cite>
  </div>
  <div class="translation-english">
    <span class="translation-label">PLAIN ENGLISH</span>
    <div class="translation-lines">
      <p class="tl"><strong>What it means:</strong> When a DNS server passes along an answer, it can't extend how long that answer lives — only shorten it or keep it the same.</p>
      <p class="tl"><strong>Why it matters:</strong> This prevents "TTL inflation" where a middleman could make a record appear fresher than the authority intended, undermining cache poisoning defenses.</p>
      <p class="tl"><strong>Watch out for:</strong> A TTL of zero is special — it means "don't cache this at all." The spec protects this signal from being stripped by intermediaries.</p>
    </div>
  </div>
</div>
```

**CSS:**
```css
.translation-block {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 0;
  border-radius: var(--radius-md);
  overflow: hidden;
  box-shadow: var(--shadow-md);
  margin: var(--space-8) 0;
}
.translation-spec {
  background: var(--color-bg-code);
  color: #CDD6F4;
  padding: var(--space-6);
  font-family: var(--font-body);
  font-size: var(--text-sm);
  line-height: 1.8;
  position: relative;
}
.spec-excerpt {
  margin: var(--space-4) 0 var(--space-3);
  padding-left: var(--space-4);
  border-left: 3px solid var(--color-accent-muted);
  font-style: italic;
  color: #CDD6F4;
}
.spec-cite {
  font-size: var(--text-xs);
  font-family: var(--font-mono);
  color: var(--color-text-muted);
  letter-spacing: 0.03em;
}
.translation-english {
  background: var(--color-surface-warm);
  padding: var(--space-6);
  font-size: var(--text-sm);
  line-height: 1.7;
  border-left: 3px solid var(--color-accent);
}
.translation-label {
  position: absolute;
  top: var(--space-2);
  right: var(--space-3);
  font-size: var(--text-xs);
  font-family: var(--font-mono);
  text-transform: uppercase;
  letter-spacing: 0.1em;
  opacity: 0.5;
}
.translation-english .translation-label {
  position: static;
  display: block;
  margin-bottom: var(--space-3);
  color: var(--color-text-muted);
}
.tl { margin: var(--space-3) 0; }
.tl:first-child { margin-top: 0; }
/* Responsive: stack vertically on mobile */
@media (max-width: 768px) {
  .translation-block { grid-template-columns: 1fr; }
  .translation-english { border-left: none; border-top: 3px solid var(--color-accent); }
}
```

**Rules:**
- Show the spec text **verbatim** — never paraphrase or condense the left panel
- Choose **naturally self-contained** passages (2-5 sentences) rather than truncating longer sections
- The right panel has three parts: **What it means** (the plain translation), **Why it matters** (the practical consequence), and optionally **Watch out for** (the gotcha)
- Keep each panel to about the same visual height — if the spec excerpt is short, keep the translation concise too

---

## Code ↔ English Translation Blocks

Used when the documentation contains code examples, configuration snippets, or protocol message formats. Shows the code on the left and a plain English translation on the right, line by line.

**HTML:**
```html
<div class="translation-block animate-in">
  <div class="translation-code">
    <span class="translation-label">CODE</span>
    <pre><code>
<span class="code-line"><span class="code-keyword">const</span> response = <span class="code-keyword">await</span> <span class="code-function">fetch</span>(url, {</span>
<span class="code-line">  <span class="code-property">method</span>: <span class="code-string">'POST'</span>,</span>
<span class="code-line">  <span class="code-property">headers</span>: { <span class="code-string">'Authorization'</span>: apiKey }</span>
<span class="code-line">});</span>
    </code></pre>
  </div>
  <div class="translation-english">
    <span class="translation-label">PLAIN ENGLISH</span>
    <div class="translation-lines">
      <p class="tl">Send a request to the URL and wait for a response...</p>
      <p class="tl">We're sending data (POST), not just asking for it (GET)...</p>
      <p class="tl">Include our API key so the server knows who we are...</p>
      <p class="tl">End of the request setup.</p>
    </div>
  </div>
</div>
```

**CSS:**
```css
.translation-block {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 0;
  border-radius: var(--radius-md);
  overflow: hidden;
  box-shadow: var(--shadow-md);
  margin: var(--space-8) 0;
}
.translation-code {
  background: var(--color-bg-code);
  color: #CDD6F4;
  padding: var(--space-6);
  font-family: var(--font-mono);
  font-size: var(--text-sm);
  line-height: 1.7;
  position: relative;
  overflow-x: hidden;  /* NO horizontal scrollbar — ever */
}
.translation-code pre,
.translation-code code {
  white-space: pre-wrap;       /* wrap long lines instead of scrolling */
  word-break: break-word;      /* break mid-word if needed */
  overflow-x: hidden;
}
.translation-english {
  background: var(--color-surface-warm);
  padding: var(--space-6);
  font-size: var(--text-sm);
  line-height: 1.7;
  border-left: 3px solid var(--color-accent);
}
.translation-label {
  position: absolute;
  top: var(--space-2);
  right: var(--space-3);
  font-size: var(--text-xs);
  text-transform: uppercase;
  letter-spacing: 0.1em;
  opacity: 0.5;
}
.translation-english .translation-label {
  color: var(--color-text-muted);
}
/* Responsive: stack vertically on mobile */
@media (max-width: 768px) {
  .translation-block { grid-template-columns: 1fr; }
  .translation-english { border-left: none; border-top: 3px solid var(--color-accent); }
}
```

**Rules:**
- Each English line should correspond to 1-2 code lines
- Use conversational language, not technical jargon
- Highlight the "why" not just the "what" — e.g., "Include our API key so the server knows who we are" not "Set the Authorization header"

---

## Multiple-Choice Quizzes

Summative assessment placed at the end of each module. 3–5 scenario-based questions. Every question presents a new situation the learner hasn't seen and asks them to *apply* knowledge — not recite it.

**Elaborative feedback is required for every distractor.** Do not just reveal the correct answer. For each wrong option, write:
1. Why this answer is wrong — what reasoning flaw it represents
2. What would have to be true for this answer to be correct

This turns wrong attempts into learning events. See the data structure below for how to store per-option feedback.

**HTML:**
```html
<div class="quiz-container" role="group" aria-labelledby="quiz-m3-heading">
  <h3 class="quiz-heading" id="quiz-m3-heading">Module 3 Quiz</h3>

  <div class="quiz-question-block" data-question="q1" data-correct="option-b">
    <div class="quiz-scenario-tag" aria-label="Scenario question">Scenario</div>
    <h4 class="quiz-question">
      A client receives a DNS response with TTL 0 for a record it previously cached with TTL 300.
      The client cached the record 60 seconds ago. What should it do?
    </h4>
    <div class="quiz-options" role="radiogroup" aria-label="Answer options">
      <button class="quiz-option" data-value="option-a" onclick="selectOption(this)"
              role="radio" aria-checked="false">
        <div class="quiz-option-radio" aria-hidden="true"></div>
        <span>Keep the cached record — 240 seconds remain on the original TTL</span>
      </button>
      <button class="quiz-option" data-value="option-b" onclick="selectOption(this)"
              role="radio" aria-checked="false">
        <div class="quiz-option-radio" aria-hidden="true"></div>
        <span>Discard the cached record immediately — TTL 0 means do not cache</span>
      </button>
      <button class="quiz-option" data-value="option-c" onclick="selectOption(this)"
              role="radio" aria-checked="false">
        <div class="quiz-option-radio" aria-hidden="true"></div>
        <span>Cache the record with the new TTL of 0, expiring it at the next query</span>
      </button>
    </div>
    <div class="quiz-feedback" id="q1-feedback" aria-live="polite"></div>
  </div>

  <button class="quiz-check-btn" onclick="checkQuiz('module-3-quiz')"
          aria-label="Check answers">Check Answers</button>
  <button class="quiz-reset-btn" onclick="resetQuiz('module-3-quiz')"
          aria-label="Try again">Try Again</button>
</div>
```

**JS pattern — with elaborative feedback per distractor:**
```javascript
// Define elaborative feedback for every option, not just the correct one
const quizData = {
  'module-3-quiz': {
    q1: {
      correct: 'option-b',
      feedback: {
        'option-a': {
          // Explain the reasoning flaw, not just "wrong"
          wrong: `This would be correct if TTL 0 were simply a lower TTL than the cached value. But TTL 0 has a specific normative meaning in RFC 1035: the record MUST NOT be cached. It's a signal from the authoritative server, not a duration. The new response supersedes the cached entry regardless of remaining TTL.`,
          correctReinforcement: null
        },
        'option-b': {
          wrong: null,
          correctReinforcement: `Exactly. TTL 0 is a normative "do not cache" signal from the authoritative server. RFC 1035 §3.2.1 states that TTL 0 means the RR can only be used for the transaction in progress. Any cached copy must be discarded.`
        },
        'option-c': {
          wrong: `Close, but caching a record with TTL 0 contradicts what TTL 0 means. A cached record with TTL 0 would expire immediately on the next query — effectively not caching it — but the spec is more direct: TTL 0 means the record MUST NOT be stored in cache at all. The distinction matters when a record has been deliberately made uncacheable for security reasons.`,
          correctReinforcement: null
        }
      }
    }
  }
};

window.selectOption = function(btn) {
  const block = btn.closest('.quiz-question-block');
  block.querySelectorAll('.quiz-option').forEach(o => {
    o.classList.remove('selected');
    o.setAttribute('aria-checked', 'false');
  });
  btn.classList.add('selected');
  btn.setAttribute('aria-checked', 'true');
};

window.checkQuiz = function(quizId) {
  const container = document.getElementById(quizId) ||
    document.querySelector(`[data-quiz-id="${quizId}"]`);
  const data = quizData[quizId];
  if (!container || !data) return;

  container.querySelectorAll('.quiz-question-block').forEach(q => {
    const qId = q.dataset.question;
    const selected = q.querySelector('.quiz-option.selected');
    const feedback = q.querySelector('.quiz-feedback');
    if (!selected || !data[qId]) return;

    const selectedValue = selected.dataset.value;
    const correctValue = data[qId].correct;
    const isCorrect = selectedValue === correctValue;
    const feedbackData = data[qId].feedback[selectedValue];

    selected.classList.add(isCorrect ? 'correct' : 'incorrect');
    if (!isCorrect) {
      q.querySelector(`[data-value="${correctValue}"]`).classList.add('correct');
    }

    feedback.innerHTML = isCorrect
      ? `<strong>Correct.</strong> ${feedbackData.correctReinforcement}`
      : `<strong>Not quite.</strong> ${feedbackData.wrong}`;
    feedback.className = `quiz-feedback show ${isCorrect ? 'success' : 'error'}`;
    q.querySelectorAll('.quiz-option').forEach(o => o.disabled = true);
  });
};

window.resetQuiz = function(quizId) {
  const container = document.getElementById(quizId) ||
    document.querySelector(`[data-quiz-id="${quizId}"]`);
  if (!container) return;
  container.querySelectorAll('.quiz-option').forEach(o => {
    o.classList.remove('selected', 'correct', 'incorrect');
    o.setAttribute('aria-checked', 'false');
    o.disabled = false;
  });
  container.querySelectorAll('.quiz-feedback').forEach(f => {
    f.className = 'quiz-feedback';
    f.innerHTML = '';
  });
};
```

**CSS for quiz states:**
```css
.quiz-option {
  display: flex; align-items: center; gap: var(--space-3);
  padding: var(--space-3) var(--space-4);
  border: 2px solid var(--color-border);
  border-radius: var(--radius-sm);
  background: var(--color-surface);
  cursor: pointer; width: 100%;
  transition: border-color var(--duration-fast), background var(--duration-fast);
}
.quiz-option:hover { border-color: var(--color-accent-muted); }
.quiz-option.selected { border-color: var(--color-accent); background: var(--color-accent-light); }
.quiz-option.correct { border-color: var(--color-success); background: var(--color-success-light); }
.quiz-option.incorrect { border-color: var(--color-error); background: var(--color-error-light); }
.quiz-option-radio {
  width: 18px; height: 18px; border-radius: 50%;
  border: 2px solid var(--color-border);
  transition: all var(--duration-fast);
}
.quiz-option.selected .quiz-option-radio {
  border-color: var(--color-accent);
  background: var(--color-accent);
  box-shadow: inset 0 0 0 3px white;
}
.quiz-feedback {
  max-height: 0; overflow: hidden; opacity: 0;
  transition: max-height var(--duration-normal), opacity var(--duration-normal);
}
.quiz-feedback.show { max-height: 200px; opacity: 1; padding: var(--space-3); margin-top: var(--space-2); border-radius: var(--radius-sm); }
.quiz-feedback.success { background: var(--color-success-light); color: var(--color-success); }
.quiz-feedback.error { background: var(--color-error-light); color: var(--color-error); }
```

---

## Drag-and-Drop Matching

For matching concepts to descriptions. Supports both mouse (HTML5 Drag API) and touch.

**HTML:**
```html
<div class="dnd-container">
  <div class="dnd-chips">
    <div class="dnd-chip" draggable="true" data-answer="actor-a">Actor A</div>
    <div class="dnd-chip" draggable="true" data-answer="actor-b">Actor B</div>
    <div class="dnd-chip" draggable="true" data-answer="actor-c">Actor C</div>
  </div>
  <div class="dnd-zones">
    <div class="dnd-zone" data-correct="actor-a">
      <p class="dnd-zone-label">Description for Actor A</p>
      <div class="dnd-zone-target">Drop here</div>
    </div>
    <!-- more zones -->
  </div>
  <button onclick="checkDnD()">Check Matches</button>
  <button onclick="resetDnD()">Reset</button>
</div>
```

**JS (mouse + touch):**
```javascript
// MOUSE: HTML5 Drag API
chips.forEach(chip => {
  chip.addEventListener('dragstart', (e) => {
    e.dataTransfer.setData('text/plain', chip.dataset.answer);
    chip.classList.add('dragging');
  });
  chip.addEventListener('dragend', () => chip.classList.remove('dragging'));
});

zones.forEach(zone => {
  const target = zone.querySelector('.dnd-zone-target');
  target.addEventListener('dragover', (e) => { e.preventDefault(); target.classList.add('drag-over'); });
  target.addEventListener('dragleave', () => target.classList.remove('drag-over'));
  target.addEventListener('drop', (e) => {
    e.preventDefault();
    target.classList.remove('drag-over');
    const answer = e.dataTransfer.getData('text/plain');
    const chip = document.querySelector(`[data-answer="${answer}"]`);
    target.textContent = chip.textContent;
    target.dataset.placed = answer;
    chip.classList.add('placed');
  });
});

// TOUCH: Custom implementation (HTML5 drag doesn't work on mobile)
chips.forEach(chip => {
  chip.addEventListener('touchstart', (e) => {
    e.preventDefault();
    const touch = e.touches[0];
    const clone = chip.cloneNode(true);
    clone.classList.add('touch-ghost');
    clone.style.cssText = `position:fixed; z-index:1000; pointer-events:none;
      left:${touch.clientX - 40}px; top:${touch.clientY - 20}px;`;
    document.body.appendChild(clone);
    chip._ghost = clone;
    chip._answer = chip.dataset.answer;
  }, { passive: false });

  chip.addEventListener('touchmove', (e) => {
    e.preventDefault();
    const touch = e.touches[0];
    if (chip._ghost) {
      chip._ghost.style.left = (touch.clientX - 40) + 'px';
      chip._ghost.style.top = (touch.clientY - 20) + 'px';
    }
    // Highlight zone under finger
    const el = document.elementFromPoint(touch.clientX, touch.clientY);
    zones.forEach(z => z.querySelector('.dnd-zone-target').classList.remove('drag-over'));
    if (el && el.closest('.dnd-zone-target')) {
      el.closest('.dnd-zone-target').classList.add('drag-over');
    }
  }, { passive: false });

  chip.addEventListener('touchend', (e) => {
    if (chip._ghost) { chip._ghost.remove(); chip._ghost = null; }
    const touch = e.changedTouches[0];
    const el = document.elementFromPoint(touch.clientX, touch.clientY);
    if (el && el.closest('.dnd-zone-target')) {
      const target = el.closest('.dnd-zone-target');
      target.textContent = chip.textContent;
      target.dataset.placed = chip._answer;
      chip.classList.add('placed');
    }
  });
});
```

---

## Group Chat Animation

iMessage/WeChat-style chat showing components "talking" to each other. Messages appear one by one with typing indicators.

**HTML:**
```html
<div class="chat-window">
  <div class="chat-messages" id="chat-messages">
    <div class="chat-message" data-msg="0" data-sender="actor-a" style="display:none">
      <div class="chat-avatar" style="background: var(--color-actor-1)">A</div>
      <div class="chat-bubble">
        <span class="chat-sender" style="color: var(--color-actor-1)">Actor A</span>
        <p>Hey Background, I need the data for this item.</p>
      </div>
    </div>
    <!-- more messages... -->
  </div>

  <div class="chat-typing" id="chat-typing" style="display:none">
    <div class="chat-avatar" id="typing-avatar">?</div>
    <div class="chat-typing-dots">
      <span class="typing-dot"></span>
      <span class="typing-dot"></span>
      <span class="typing-dot"></span>
    </div>
  </div>

  <div class="chat-controls">
    <button onclick="playChatNext()">Next Message</button>
    <button onclick="playChatAll()">Play All</button>
    <button onclick="resetChat()">Replay</button>
    <span class="chat-progress">0 / N messages</span>
  </div>
</div>
```

**JS:**
```javascript
let chatIndex = 0;
const chatMessages = document.querySelectorAll('#chat-messages .chat-message');

// Actor color/avatar mapping
const actors = {
  'actor-a': { initials: 'A', color: 'var(--color-actor-1)' },
  'actor-b': { initials: 'B', color: 'var(--color-actor-2)' },
  'actor-c': { initials: 'C', color: 'var(--color-actor-3)' },
};

window.playChatNext = function() {
  if (chatIndex >= chatMessages.length) return;
  const msg = chatMessages[chatIndex];
  const sender = msg.dataset.sender;

  // Show typing indicator with correct avatar
  const typing = document.getElementById('chat-typing');
  const avatar = document.getElementById('typing-avatar');
  avatar.textContent = actors[sender].initials;
  avatar.style.background = actors[sender].color;
  typing.style.display = 'flex';

  setTimeout(() => {
    typing.style.display = 'none';
    msg.style.display = 'flex';
    msg.style.animation = 'fadeSlideUp 0.3s var(--ease-out)';
    chatIndex++;
    updateChatProgress();
  }, 800);
};

window.playChatAll = function() {
  const interval = setInterval(() => {
    if (chatIndex >= chatMessages.length) { clearInterval(interval); return; }
    playChatNext();
  }, 1200);
};
```

**CSS for typing dots:**
```css
.typing-dot {
  width: 8px; height: 8px; border-radius: 50%;
  background: var(--color-text-muted);
  animation: typingBounce 1.4s infinite;
}
.typing-dot:nth-child(2) { animation-delay: 0.2s; }
.typing-dot:nth-child(3) { animation-delay: 0.4s; }
@keyframes typingBounce {
  0%, 60%, 100% { transform: translateY(0); }
  30% { transform: translateY(-6px); }
}
```

---

## Message Flow / Data Flow Animation

Step-by-step visualization of data moving between components. User clicks "Next Step" to advance.

**HTML:**
```html
<div class="flow-animation">
  <div class="flow-actors">
    <div class="flow-actor" id="flow-actor-1">
      <div class="flow-actor-icon">A</div>
      <span>Actor 1</span>
    </div>
    <div class="flow-actor" id="flow-actor-2">
      <div class="flow-actor-icon">B</div>
      <span>Actor 2</span>
    </div>
    <div class="flow-actor" id="flow-actor-3">
      <div class="flow-actor-icon">C</div>
      <span>Actor 3</span>
    </div>
  </div>

  <div class="flow-packet" id="flow-packet"></div>

  <div class="flow-step-label" id="flow-label">Click "Next Step" to begin</div>

  <div class="flow-controls">
    <button onclick="flowNext()">Next Step</button>
    <button onclick="flowReset()">Restart</button>
    <span class="flow-progress">Step 0 / N</span>
  </div>
</div>
```

**JS pattern:**
```javascript
const flowSteps = [
  { from: 'actor-1', to: 'actor-2', label: 'User clicks button → Actor 1 detects click event', highlight: 'actor-1' },
  { from: 'actor-1', to: 'actor-2', label: 'Actor 1 sends message to Actor 2', highlight: 'actor-2', packet: true },
  { from: 'actor-2', to: 'external', label: 'Actor 2 calls external API', highlight: 'actor-2', cloud: true },
  // etc.
];

let flowStep = 0;
window.flowNext = function() {
  if (flowStep >= flowSteps.length) return;
  const step = flowSteps[flowStep];

  // Remove previous highlights
  document.querySelectorAll('.flow-actor').forEach(a => a.classList.remove('active'));

  // Highlight current actor
  document.getElementById(`flow-${step.highlight}`).classList.add('active');

  // Animate packet if needed
  if (step.packet) {
    animatePacket(step.from, step.to);
  }

  // Update label
  document.getElementById('flow-label').textContent = step.label;
  flowStep++;
};
```

**CSS for active actor glow:**
```css
.flow-actor.active {
  box-shadow: 0 0 0 3px var(--color-accent), 0 0 20px rgba(217, 79, 48, 0.2);
  transform: scale(1.05);
  transition: all var(--duration-normal) var(--ease-out);
}
```

---

## Interactive Architecture Diagram

Full-system diagram where hovering/clicking a component shows a description tooltip.

**HTML:**
```html
<div class="arch-diagram">
  <div class="arch-zone arch-zone-browser">
    <h4 class="arch-zone-label">Browser</h4>
    <div class="arch-component" data-desc="Injects UI into the web page, reads DOM, captures user actions"
         onclick="showArchDesc(this)">
      <div class="arch-icon">📄</div>
      <span>Component A</span>
    </div>
    <!-- more components -->
  </div>
  <div class="arch-zone arch-zone-external">
    <h4 class="arch-zone-label">External Services</h4>
    <!-- API cards -->
  </div>
  <div class="arch-description" id="arch-desc">Click any component to learn what it does</div>
</div>
```

---

## Layer Toggle Demo

Shows how different layers (e.g., HTML/CSS/JS, or data/logic/UI) build on each other. Three tabs switch between views.

**HTML:**
```html
<div class="layer-demo">
  <div class="layer-tabs">
    <button class="layer-tab active" onclick="showLayer('html')">HTML</button>
    <button class="layer-tab" onclick="showLayer('css')">+ CSS</button>
    <button class="layer-tab" onclick="showLayer('js')">+ JS</button>
  </div>
  <div class="layer-viewport">
    <div class="layer" id="layer-html" style="display:block">
      <!-- Raw unstyled version -->
    </div>
    <div class="layer" id="layer-css" style="display:none">
      <!-- Styled version -->
    </div>
    <div class="layer" id="layer-js" style="display:none">
      <!-- Interactive version -->
    </div>
  </div>
  <p class="layer-description" id="layer-desc">This is the raw HTML...</p>
</div>
```

---

## "Spot the Bug" Challenge

Show code with a deliberate bug. User clicks the buggy line. Reveal explains the issue.

**HTML:**
```html
<div class="bug-challenge">
  <h3>Find the bug in this code:</h3>
  <div class="bug-code">
    <div class="bug-line" data-line="1" onclick="checkBugLine(this, false)">
      <span class="line-num">1</span>
      <code>chrome.runtime.onMessage.addListener((msg, sender, sendResponse) => {</code>
    </div>
    <div class="bug-line" data-line="2" onclick="checkBugLine(this, false)">
      <span class="line-num">2</span>
      <code>  if (msg.action === 'fetchData') {</code>
    </div>
    <div class="bug-line bug-target" data-line="3" onclick="checkBugLine(this, true)">
      <span class="line-num">3</span>
      <code>    fetch(url).then(r => r.json()).then(data => sendResponse(data));</code>
    </div>
    <div class="bug-line" data-line="4" onclick="checkBugLine(this, false)">
      <span class="line-num">4</span>
      <code>  }</code>
    </div>
    <div class="bug-line" data-line="5" onclick="checkBugLine(this, false)">
      <span class="line-num">5</span>
      <code>});</code>
    </div>
  </div>
  <div class="bug-feedback" id="bug-feedback"></div>
</div>
```

**JS:**
```javascript
window.checkBugLine = function(el, isCorrect) {
  const feedback = el.closest('.bug-challenge').querySelector('.bug-feedback');
  if (isCorrect) {
    el.classList.add('correct');
    feedback.innerHTML = '<strong>Found it!</strong> The listener uses an async operation (fetch) but doesn\'t return true. Chrome closes the message channel before the response can be sent. Fix: add <code>return true;</code> at the end.';
    feedback.className = 'bug-feedback show success';
  } else {
    el.classList.add('incorrect');
    feedback.innerHTML = 'Not this line — look for where the async timing might cause problems...';
    feedback.className = 'bug-feedback show error';
    setTimeout(() => { el.classList.remove('incorrect'); feedback.className = 'bug-feedback'; }, 2000);
  }
};
```

---

## Scenario Quiz

"What would a senior engineer do?" — situational questions with explanations.

Same HTML/CSS/JS pattern as Multiple-Choice Quizzes, but with longer scenario descriptions and more detailed explanations. Wrap each question in a scenario context block:

```html
<div class="scenario-block">
  <div class="scenario-context">
    <span class="scenario-label">Scenario</span>
    <p>Your app processes a 3-hour podcast transcript. The API has a 16,000 token limit. What do you do?</p>
  </div>
  <!-- quiz-options here -->
</div>
```

---

## Callout Boxes

"Aha!" moments — universal CS insights. Max 2 per module.

```html
<div class="callout callout-accent">
  <div class="callout-icon">💡</div>
  <div class="callout-content">
    <strong class="callout-title">Key Insight</strong>
    <p>This pattern — splitting responsibilities into focused roles — is one of the most important ideas in software engineering. Engineers call it "separation of concerns."</p>
  </div>
</div>
```

**Variants:**
- `callout-accent`: vermillion left border, light accent background (for CS insights)
- `callout-info`: teal left border, light info background (for "good to know")
- `callout-warning`: red left border, light error background (for common mistakes)

---

## Pattern/Feature Cards

Grid of cards highlighting engineering patterns, tech stack components, or key concepts.

```html
<div class="pattern-cards">
  <div class="pattern-card" style="border-top: 3px solid var(--color-actor-1)">
    <div class="pattern-icon" style="background: var(--color-actor-1)">🔄</div>
    <h4 class="pattern-title">Caching</h4>
    <p class="pattern-desc">Store results to avoid redundant work — like keeping leftovers instead of cooking a new meal every time.</p>
  </div>
  <!-- more cards -->
</div>
```

```css
.pattern-cards {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
  gap: var(--space-4);
}
.pattern-card {
  background: var(--color-surface);
  border-radius: var(--radius-md);
  padding: var(--space-6);
  box-shadow: var(--shadow-sm);
  transition: transform var(--duration-normal) var(--ease-out), box-shadow var(--duration-normal);
}
.pattern-card:hover {
  transform: translateY(-4px);
  box-shadow: var(--shadow-md);
}
```

---

## Flow Diagrams

**Horizontal flow (desktop):**
```html
<div class="flow-steps">
  <div class="flow-step">
    <div class="flow-step-num">1</div>
    <p>User clicks button</p>
  </div>
  <div class="flow-arrow">→</div>
  <div class="flow-step">
    <div class="flow-step-num">2</div>
    <p>Component A detects click</p>
  </div>
  <div class="flow-arrow">→</div>
  <!-- more steps -->
</div>
```

Arrows rotate to `↓` on mobile via CSS transform.

---

## Permission/Config Badges

For annotating config files, permissions, or settings:

```html
<div class="badge-list">
  <div class="badge-item">
    <code class="badge-code">storage</code>
    <span class="badge-desc">Save data between sessions (like browser bookmarks)</span>
  </div>
  <div class="badge-item">
    <code class="badge-code">activeTab</code>
    <span class="badge-desc">Access the currently open tab (only when the user clicks)</span>
  </div>
</div>
```

```css
.badge-item {
  display: flex; align-items: center; gap: var(--space-4);
  padding: var(--space-3) var(--space-4);
  border: 1px solid var(--color-border-light);
  border-radius: var(--radius-sm);
  transition: border-color var(--duration-fast);
}
.badge-item:hover { border-color: var(--color-accent-muted); }
.badge-code {
  font-family: var(--font-mono);
  font-size: var(--text-sm);
  background: var(--color-bg-code);
  color: #CBA6F7;
  padding: var(--space-1) var(--space-3);
  border-radius: var(--radius-sm);
  white-space: nowrap;
}
```

---

## Glossary Tooltips

The most important accessibility feature for non-technical learners. Any technical term in the course text should be wrapped in a tooltip that shows a plain-English definition on hover (desktop) or tap (mobile). The learner never has to leave the page or Google anything.

**HTML — mark up terms inline:**
```html
<p>The extension uses a
  <span class="term" data-definition="A service worker is a background script that runs independently of the web page — like a behind-the-scenes assistant that's always on, even when you're not looking at the page.">service worker</span>
  to handle API calls.
</p>
```

**CSS:**
```css
.term {
  border-bottom: 1.5px dashed var(--color-accent-muted);
  cursor: pointer;    /* NOT cursor: help — pointer feels clickable and inviting */
  position: relative;
}
.term:hover, .term.active {
  border-bottom-color: var(--color-accent);
  color: var(--color-accent);
}

/* The tooltip bubble — uses position: fixed and is appended to document.body
   via JS so it is NEVER clipped by ancestor overflow: hidden containers
   (like translation blocks). See JS section below for positioning logic. */
.term-tooltip {
  position: fixed;        /* CRITICAL: fixed, not absolute — prevents clipping */
  background: var(--color-bg-code);
  color: #CDD6F4;
  padding: var(--space-3) var(--space-4);
  border-radius: var(--radius-sm);
  font-size: var(--text-sm);
  font-family: var(--font-body);
  line-height: var(--leading-normal);
  width: max(200px, min(320px, 80vw));
  box-shadow: var(--shadow-lg);
  pointer-events: none;
  opacity: 0;
  transition: opacity var(--duration-fast);
  z-index: 10000;        /* Above everything, including nav */
}
/* Arrow pointing down */
.term-tooltip::after {
  content: '';
  position: absolute;
  top: 100%;
  left: 50%;
  transform: translateX(-50%);
  border: 6px solid transparent;
  border-top-color: var(--color-bg-code);
}
.term-tooltip.visible {
  opacity: 1;
}

/* If tooltip goes off-screen top, flip to below */
.term-tooltip.flip {
  bottom: auto;
  top: calc(100% + 8px);
}
.term-tooltip.flip::after {
  top: auto;
  bottom: 100%;
  border-top-color: transparent;
  border-bottom-color: var(--color-bg-code);
}
```

**JS — position: fixed tooltips appended to body (never clipped by overflow):**
```javascript
// Tooltip container — appended to body so it's never clipped
let activeTooltip = null;

function positionTooltip(term, tip) {
  const rect = term.getBoundingClientRect();
  const tipWidth = 300; // approximate
  let left = rect.left + rect.width / 2 - tipWidth / 2;
  // Clamp to viewport
  left = Math.max(8, Math.min(left, window.innerWidth - tipWidth - 8));

  // Try above first
  let top = rect.top - 8;
  tip.style.left = left + 'px';

  // Position above by default, flip below if no room
  document.body.appendChild(tip);
  const tipHeight = tip.offsetHeight;
  if (rect.top - tipHeight - 8 < 0) {
    // Flip below
    tip.style.top = (rect.bottom + 8) + 'px';
    tip.classList.add('flip');
  } else {
    tip.style.top = (rect.top - tipHeight - 8) + 'px';
    tip.classList.remove('flip');
  }
}

document.querySelectorAll('.term').forEach(term => {
  const tip = document.createElement('span');
  tip.className = 'term-tooltip';
  tip.textContent = term.dataset.definition;

  // Hover for desktop
  term.addEventListener('mouseenter', () => {
    if (activeTooltip && activeTooltip !== tip) {
      activeTooltip.classList.remove('visible');
      activeTooltip.remove();
    }
    positionTooltip(term, tip);
    requestAnimationFrame(() => tip.classList.add('visible'));
    activeTooltip = tip;
  });

  term.addEventListener('mouseleave', () => {
    tip.classList.remove('visible');
    setTimeout(() => { if (!tip.classList.contains('visible')) tip.remove(); }, 150);
    activeTooltip = null;
  });

  // Tap for mobile
  term.addEventListener('click', (e) => {
    e.stopPropagation();
    if (activeTooltip && activeTooltip !== tip) {
      activeTooltip.classList.remove('visible');
      activeTooltip.remove();
    }
    if (tip.classList.contains('visible')) {
      tip.classList.remove('visible');
      tip.remove();
      activeTooltip = null;
    } else {
      positionTooltip(term, tip);
      requestAnimationFrame(() => tip.classList.add('visible'));
      activeTooltip = tip;
    }
  });
});

// Close tooltips when clicking elsewhere
document.addEventListener('click', () => {
  if (activeTooltip) {
    activeTooltip.classList.remove('visible');
    activeTooltip.remove();
    activeTooltip = null;
  }
});
```

**Rules:**
- Mark up EVERY technical term on first use in each module (API, DOM, callback, async, endpoint, middleware, etc.)
- Keep definitions to 1-2 sentences max, in everyday language
- Use a metaphor in the definition when it helps — e.g., "A **callback** is like leaving your phone number at a restaurant so they can call you when your table is ready"
- Don't mark the same term twice within the same screen — only on first appearance per module
- The dashed underline should be subtle enough not to distract but visible enough that curious learners discover it

---

## Visual File Tree

Use instead of paragraphs listing "this folder does X, that folder does Y." Much easier to scan.

```html
<div class="file-tree">
  <div class="ft-folder open">
    <span class="ft-name">app/</span>
    <span class="ft-desc">Pages and API routes</span>
    <div class="ft-children">
      <div class="ft-folder">
        <span class="ft-name">api/</span>
        <span class="ft-desc">Backend endpoints the frontend calls</span>
      </div>
      <div class="ft-file">
        <span class="ft-name">layout.tsx</span>
        <span class="ft-desc">The shell that wraps every page</span>
      </div>
    </div>
  </div>
  <div class="ft-folder">
    <span class="ft-name">components/</span>
    <span class="ft-desc">Reusable UI building blocks</span>
  </div>
  <div class="ft-folder">
    <span class="ft-name">lib/</span>
    <span class="ft-desc">Shared logic and utilities</span>
  </div>
</div>
```

```css
.file-tree { font-family: var(--font-mono); font-size: var(--text-sm); }
.ft-folder, .ft-file {
  padding: var(--space-2) var(--space-3);
  border-left: 2px solid var(--color-border-light);
  margin-left: var(--space-4);
}
.ft-folder > .ft-name { color: var(--color-accent); font-weight: 600; }
.ft-folder > .ft-name::before { content: '📁 '; }
.ft-file > .ft-name::before { content: '📄 '; }
.ft-desc {
  color: var(--color-text-secondary);
  font-family: var(--font-body);
  margin-left: var(--space-2);
  font-size: var(--text-xs);
}
.ft-children { margin-left: var(--space-4); }
```

---

## Icon-Label Rows

For listing components, features, or concepts visually. Replaces bullet-point paragraphs.

```html
<div class="icon-rows">
  <div class="icon-row">
    <div class="icon-circle" style="background: var(--color-actor-1)">🖥️</div>
    <div>
      <strong>Frontend (Next.js)</strong>
      <p>What the user sees and interacts with</p>
    </div>
  </div>
  <div class="icon-row">
    <div class="icon-circle" style="background: var(--color-actor-2)">⚡</div>
    <div>
      <strong>API Routes</strong>
      <p>Backend logic that runs on the server</p>
    </div>
  </div>
  <div class="icon-row">
    <div class="icon-circle" style="background: var(--color-actor-3)">🗄️</div>
    <div>
      <strong>Database (Supabase)</strong>
      <p>Where all the data is stored permanently</p>
    </div>
  </div>
</div>
```

```css
.icon-rows { display: flex; flex-direction: column; gap: var(--space-4); }
.icon-row {
  display: flex; align-items: center; gap: var(--space-4);
  padding: var(--space-4);
  background: var(--color-surface);
  border-radius: var(--radius-md);
  box-shadow: var(--shadow-sm);
}
.icon-row p { margin: 0; color: var(--color-text-secondary); font-size: var(--text-sm); }
.icon-circle {
  width: 48px; height: 48px; border-radius: 50%;
  display: flex; align-items: center; justify-content: center;
  font-size: 1.25rem; flex-shrink: 0;
}
```

---

## Numbered Step Cards

For sequences that would otherwise be a numbered paragraph list. Visual, scannable, and each step stands alone.

```html
<div class="step-cards">
  <div class="step-card">
    <div class="step-num">1</div>
    <div class="step-body">
      <strong>User pastes a YouTube URL</strong>
      <p>The frontend captures the URL and extracts the video ID</p>
    </div>
  </div>
  <div class="step-card">
    <div class="step-num">2</div>
    <div class="step-body">
      <strong>API fetches the transcript</strong>
      <p>A server-side route calls an external service to get the video's text</p>
    </div>
  </div>
  <div class="step-card">
    <div class="step-num">3</div>
    <div class="step-body">
      <strong>AI analyzes the content</strong>
      <p>The transcript is sent to an AI model that extracts key moments</p>
    </div>
  </div>
</div>
```

```css
.step-cards { display: flex; flex-direction: column; gap: var(--space-3); }
.step-card {
  display: flex; align-items: flex-start; gap: var(--space-4);
  padding: var(--space-4) var(--space-5);
  background: var(--color-surface);
  border-radius: var(--radius-md);
  border-left: 3px solid var(--color-accent);
  box-shadow: var(--shadow-sm);
}
.step-num {
  width: 32px; height: 32px; border-radius: 50%;
  background: var(--color-accent);
  color: white; font-weight: 700;
  display: flex; align-items: center; justify-content: center;
  font-family: var(--font-display);
  flex-shrink: 0;
}
.step-body p { margin: var(--space-1) 0 0; color: var(--color-text-secondary); font-size: var(--text-sm); }
```
