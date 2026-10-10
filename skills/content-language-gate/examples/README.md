# Runnable example

```bash
python3 ../scripts/language-gate.py rules.json fixture
```

**This example exits `1` on purpose.** `fixture/content/pack-repeats.json` contains a
deliberate duplicate (`"You want to be seen where you are."` appears in two rules), so the
originality check goes red and names it. That is the gate demonstrating itself.

To see a clean run, scan only the clean pack:

```bash
mkdir -p /tmp/clean/content && cp fixture/content/pack-clean.json /tmp/clean/content/
python3 ../scripts/language-gate.py rules.json /tmp/clean     # -> LANGUAGE GATE CLEAN, exit 0
```

Two more arms worth trying, because they are what makes the gate trustworthy:

- Point `content.glob` at a path that matches nothing → `NOTHING WAS SCANNED`, exit `1`.
  An empty scan is never reported as clean.
- Replace `forbidden` with a pattern that matches nothing → the gate declares itself
  **BLIND** and names every decoy it failed to catch, instead of reporting your content clean.

All fixture content is synthetic.
