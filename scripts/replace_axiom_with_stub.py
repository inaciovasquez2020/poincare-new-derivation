from pathlib import Path
import re
import sys

if len(sys.argv) != 3:
    raise SystemExit("usage: python3 scripts/replace_axiom_with_stub.py <file> <name>")

p = Path(sys.argv[1])
name = sys.argv[2]
txt = p.read_text()

pat = re.compile(rf'^(\s*)axiom\s+{re.escape(name)}\s*:(.*(?:\n(?!\s*(?:axiom|theorem|lemma|def|end\b|namespace\b|import\b)).*)*)', re.M)
m = pat.search(txt)
if not m:
    raise SystemExit(f"axiom {name} not found in {p}")

indent = m.group(1)
sig = m.group(2).rstrip()
replacement = f"{indent}theorem {name} :{sig} := by\n{indent}  sorry"
txt = txt[:m.start()] + replacement + txt[m.end():]
p.write_text(txt)
print(f"rewrote {p}: axiom {name} -> theorem {name} := by sorry")
