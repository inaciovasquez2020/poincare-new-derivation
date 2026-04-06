from pathlib import Path
import re

pat = re.compile(r'^\s*axiom\s+([A-Za-z0-9_']+)\s*:', re.M)
for p in sorted(Path("lean/Poincare").rglob("*.lean")):
    txt = p.read_text()
    hits = pat.findall(txt)
    if hits:
        print(f"[AXIOMS] {p}")
        for h in hits:
            print(f"  - {h}")
