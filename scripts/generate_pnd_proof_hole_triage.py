from pathlib import Path
import re
from collections import defaultdict

ROOT = Path(".")
OUT = Path("docs/status/PND_PROOF_HOLE_TRIAGE_2026_05_01.md")

lean_files = [
    p for p in ROOT.rglob("*.lean")
    if ".lake" not in p.parts and ".git" not in p.parts
]

patterns = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"^\s*axiom\s+[A-Za-z0-9_'.]+", re.M),
}

rows = []
totals = defaultdict(int)

for p in sorted(lean_files):
    text = p.read_text(errors="ignore")
    counts = {k: len(rx.findall(text)) for k, rx in patterns.items()}
    total = sum(counts.values())
    if total:
        for k, v in counts.items():
            totals[k] += v
        rows.append((str(p), counts["sorry"], counts["admit"], counts["axiom"], total))

rows.sort(key=lambda r: (-r[4], r[0]))

md = []
md.append("# PND Proof-Hole Triage — 2026-05-01")
md.append("")
md.append("Conditional.")
md.append("")
md.append(f"- Total `sorry`: **{totals['sorry']}**")
md.append(f"- Total `admit`: **{totals['admit']}**")
md.append(f"- Total `axiom`: **{totals['axiom']}**")
md.append(f"- Total holes: **{totals['sorry'] + totals['admit'] + totals['axiom']}**")
md.append("")
md.append("This is a proof-hole inventory only. It does not assert theorem-level closure.")
md.append("")
md.append("| File | sorry | admit | axiom | total |")
md.append("|---|---:|---:|---:|---:|")
for file, sorry, admit, axiom, total in rows:
    md.append(f"| `{file}` | {sorry} | {admit} | {axiom} | {total} |")
md.append("")
md.append("## First reduction target")
md.append("")
md.append("Target the largest local concentration first: `lean/Poincare/FinalConstructive.lean`.")
md.append("")
md.append("Permitted first move:")
md.append("")
md.append("1. Replace exactly one `by sorry` in `lean/Poincare/FinalConstructive.lean` with either a proof or a named local theorem statement.")
md.append("")
md.append("No unconditional Poincaré theorem is asserted.")
md.append("")

OUT.write_text("\n".join(md))
print(OUT)
