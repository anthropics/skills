# Runnable examples

Three checks against the same two fixtures, so you can see every verdict the harness gives.

```bash
H=../scripts/control-harness.sh

bash $H --good ok.json --bad broken.json -- python3 check-good.py       # TRUSTWORTHY, exit 0
bash $H --good ok.json --bad broken.json -- python3 check-blind.py      # BLIND,       exit 1
bash $H --good ok.json --bad broken.json -- python3 check-overtight.py  # OVERTIGHT,   exit 1
bash $H --good broken.json --bad ok.json -- python3 check-good.py       # INVERTED,    exit 1
```

`broken.json` differs from `ok.json` in one way: `version` is an empty string.

- `check-good.py` requires a non-empty version → rejects it.
- `check-blind.py` only checks that the `version` **key exists** → an empty string passes.
  This is the most common way a check lies: asserting presence where the requirement was
  validity.
- `check-overtight.py` demands `X.Y.Z+build`, which neither fixture has → nothing can pass,
  and a gate nobody can pass gets switched off.

To see the silent-no-op warning:

```bash
printf '#!/bin/bash\nexit 0\n' > /tmp/silent.sh && chmod +x /tmp/silent.sh
bash $H --good ok.json --bad broken.json -- bash /tmp/silent.sh
```

All fixture content is synthetic.
