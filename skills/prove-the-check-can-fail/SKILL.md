---
name: prove-the-check-can-fail
description: Before trusting a test, linter, scanner, monitor or CI gate, prove it can fail — run it against a known-bad input and watch it reject. Use when a check reports success and you are about to act on that, when a gate has never gone red, when a scan returns "0 issues found", when deciding whether a green CI run is evidence, when a flaky gate seems fixed, or when writing a new check and choosing its controls. Includes a control harness that classifies any check as trustworthy, blind, overtight or inverted.
---

# Prove the check can fail

A check that has never failed has never been tested. Its green is a habit, not evidence.

This skill is about the moment *before* you believe a result: how to establish that the
thing reporting success is capable of reporting failure. Every law below has a measurement
behind it, and every one of them produced a wrong conclusion first.

## When to use it

- A check, scan, test or monitor says "clean" and you are about to ship, merge or report.
- A gate has been green since it was written. That is a warning sign, not a comfort.
- A flaky gate looks repaired.
- You are writing a new check and choosing what its controls should be.

## When NOT to use it

- To decide *what* to measure in a domain (performance budgets, accessibility rules,
  security baselines) — those are domain skills. This decides whether the number you are
  looking at deserves belief.
- As a substitute for the check itself.

## The harness

```bash
scripts/control-harness.sh --good <arg> --bad <arg> -- <command...>
```

The fixture is appended as the command's last argument. Four verdicts:

| known-good | known-bad | verdict | meaning |
|---|---|---|---|
| pass | **fail** | **TRUSTWORTHY** | the only outcome that earns belief |
| pass | pass | **BLIND** | it cannot see the thing it claims to check |
| fail | fail | **OVERTIGHT** | nothing can ever pass; the gate will get switched off |
| fail | pass | **INVERTED** | wired backwards |

`examples/` has a working check, a blind one, and an overtight one so you can see all four.
Exit code `0` only for TRUSTWORTHY, so the harness itself works as a meta-gate in CI.

## THE LAWS, EACH WITH ITS MEASUREMENT

### 1. The tool is a suspect before the subject is

When a check reports a problem, run it against a known-good input **first**. Measured: a
text scanner matched a verb stem and flagged three ordinary phrases as clinical diagnosis —
**8 false violations**, every one of them written up as a product defect. The product was
fine. The scanner was broken.

Corollary: if your check is reporting many findings, that is weak evidence of many defects
and strong evidence of one broken pattern.

### 2. A negative control must reproduce the real thing, not a lookalike

Measured: a gate asked "is another build running?" with `pgrep -f <tool>`, which matches any
process whose **command line mentions** the tool — including the author's own
`until ! pgrep -f <tool>` wait loop. 150 samples, **83 false alarms**, and the first positive
coincided exactly with starting that loop.

The subtle part: this gate *had* a negative control. It used a decoy process whose command
line mentioned the tool — so the control proved the gate catches **mentions** and was
recorded as proving it catches **executions**. A control that does not reproduce the real
topology certifies the wrong behaviour.

Fixing it needs `pgrep -x` plus a `ps -o comm=` basename check, and a control built from a
**real execution** (copy a small binary to the tool's name, re-sign it so the kernel does not
kill it, run it in a separate session — an unsigned copy dies instantly and the control
silently never runs).

### 3. An empty scan is not a pass

If the input glob matches nothing, a naive check reports "0 issues → clean". Measured: a
content scanner pointed at a wrong path printed `violations=0` and would have been recorded
as evidence. Silence is the cheapest way for a check to lie. Make zero-input an explicit
red.

### 4. An exit code dies in a pipe

`mycheck | tail -1` returns `tail`'s status. Measured **twice in one session**: a script that
correctly exited `1` was reported as `rc=0`, purely because the probe piped it — and on the
second occasion I briefly recorded the tool as broken before noticing my own pipe. Run the
thing you are judging **bare**, or use `pipefail`/`PIPESTATUS`.

### 5. "Syntax OK" is not "it runs"

Measured: a translated script passed `ast.parse` and crashed on the first real invocation
with `NameError` — an identifier the rewrite had missed. Parsing proves the file is
well-formed, nothing more. Execute it.

### 6. Declare the unit before you count

Uniqueness, coverage and duplication are meaningless until you say *what* the unit is, and
both defaults are wrong. Measured in both directions on one dataset:

- Merging two fields into one key **hid** 28 duplicate values, because the other field always
  differed so the merged key always differed.
- Counting the fields separately **invented** a defect: it reported those 28 as a
  template-content violation, when the product renders the two fields together and the
  combined output was 286/286 unique. Two users saw the same headline; none saw the same
  output.

So state the gated unit, make it the thing the user actually receives, and report the others
as informational.

### 7. A short passing streak is not a repair

Measured: a flaky gate failed twice, took a plausible patch, then **passed twice** — and the
patch was about to be recorded as the fix. Extending the experiment, the same patch failed
**three times in a row**. Two-for-two is Fisher two-tailed p ≈ 0.33: nothing.

Worse, a later round produced the trap in reverse: the patched arm passed under a load **four
times higher** than the failing arm, which felt like strong evidence — until the negative
control (patch reverted) also passed. The repair was never demonstrated. Keep the change if
it is right on its own merits, but write "not proven" next to it.

### 8. A check must not destroy its own evidence

Measured: a runner wrote every execution to the same log path. Four tests failed; the lines
identifying *which* operation was lost were overwritten by the next two runs. The diagnosis
became unrecoverable and only a filtered summary survived. Give each run its own timestamped
artifact and symlink the stable name to the newest.

### 9. The instrument can be the cause

Measured: the "is a foreign build running?" sampler called a wrapper every few seconds, and
that wrapper spawns the very process the gate flags. The detector was detecting itself. Also
measured: a measurement counter published state changes *during* input delivery, perturbing
what it measured.

Before blaming the subject, remove the instrument and see whether the symptom survives.

### 10. A silent lock can freeze a rail for days

Measured: a `.git/index.lock` left by a crashed process ten days earlier blocked every commit
since. An automated committer retried on schedule, saw the lock, and returned **silently** —
no alarm, no log line, nothing. Health checks that read artifact *age* reported "stale" but
could not say why, so the cause was hunted in disk, network and credentials.

```bash
# before trusting any scheduled writer, check whether something is holding its door shut
L=.git/index.lock
if [ -e "$L" ]; then
  AGE=$(( $(date +%s) - $(stat -f %m "$L") ))      # macOS; GNU: stat -c %Y
  LIVE=$(pgrep -x git | wc -l | tr -d ' ')
  echo "lock: $(stat -f %z "$L") bytes, ${AGE}s old, live git processes: $LIVE"
  # LIVE>0  -> another process owns it. Do NOT remove it.
  # LIVE=0 and old -> stale; this is the case git's own message describes.
fi
```

Two conditions together, never one: no live process **and** meaningful age. Removing a lock
while a process holds it corrupts someone else's work.

## Workflow

1. Build a **known-bad** input that violates exactly the thing the check claims to enforce.
2. Build a **known-good** input that should pass.
3. Run `control-harness.sh`. Anything other than TRUSTWORTHY means the check is not yet
   evidence.
4. Only then run it against the real subject, and run it **bare** so the exit code survives.
5. If it goes red, re-read law 1 before writing the finding down.

## Acceptance

```text
known-good : exit 0
known-bad  : exit <non-zero>
VERDICT    : TRUSTWORTHY
```

Without this, "the check passed" is a sentence about habit, not about the subject.

## Verification record

| Arm | Result |
|---|---|
| working check vs good/bad fixtures | **TRUSTWORTHY**, harness exit `0` |
| check that only asserts key presence | **BLIND** — passed the known-bad input, harness exit `1` |
| check demanding an impossible format | **OVERTIGHT** — rejected the known-good input too |
| fixtures deliberately swapped | **INVERTED** |
| a check that prints nothing and exits 0 | BLIND **plus** an explicit "printed nothing — verify it ran" warning |

All five arms run from the shipped `examples/`.
