# Runnable example

```bash
python3 ../scripts/language-gate.py rules.json fixture
```

This example exits `0`. It is the **design case**, and it is the interesting one:
`fixture/content/pack-repeats.json` deliberately reuses one headline across three nuance
variants, so you get

```text
ORIGINALITY output   : repeats=0  PASS     <- gated unit: what the user receives
originality headline : repeats=2  INFO     <- ungated: shared headline is the design
```

A shared headline is not a defect when the support line differs. A duplicated **output** is.
To see that, add two rules with identical `text` *and* `short` — the gated unit goes red and
names the pair.

Two more arms worth trying, because they are what makes the gate trustworthy:

- Point `content.glob` at a path that matches nothing → `NOTHING WAS SCANNED`, exit `1`.
  An empty scan is never reported as clean.
- Replace `forbidden` with a pattern that matches nothing → the gate declares itself
  **BLIND** and names every decoy it failed to catch, instead of reporting your content clean.

All fixture content is synthetic.
