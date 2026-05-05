from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

perelman = ROOT / "lean/Poincare/PerelmanPL.lean"
quarantine = ROOT / "lean/Poincare/ContradictionQuarantine.lean"
status = ROOT / "docs/status/PERELMAN_PL_CONDITIONAL_CLOSURE_2026_05_05.md"
artifact = ROOT / "artifacts/poincare/perelman_pl_conditional_closure_2026_05_05.json"

for path in [perelman, quarantine, status, artifact]:
    assert path.exists(), f"missing {path}"

p = perelman.read_text()
q = quarantine.read_text()
s = status.read_text()
a = artifact.read_text()

for token in [
    "axiom Perelman_PL",
    "CONDITIONAL_EXTERNAL_THEOREM_ONLY",
    "theorem conditional_PL_poincare_recognition",
    "Perelman_PL K",
]:
    assert token in p, f"missing PerelmanPL token: {token}"

for token in [
    "theorem applyMoveImpl_identity",
    "applyMoveImpl K m = K",
    "theorem current_applyMoveImpl_blocks_strict_descent",
    "¬ Phi (applyMoveImpl K m) < Phi K",
]:
    assert token in q, f"missing quarantine token: {token}"

for token in [
    "This is not theorem-level Lean closure.",
    "It does not prove the Poincare conjecture inside this repository.",
    "FRONTIER/CONDITIONAL",
    "Do not describe this repository as",
]:
    assert token in s, f"missing status token: {token}"

for token in [
    '"status": "CONDITIONAL_EXTERNAL_THEOREM_ONLY"',
    '"theorem_closure": false',
    '"frontier_preserved": true',
    '"external_axiom": "Perelman_PL"',
]:
    assert token in a, f"missing artifact token: {token}"

for forbidden in [
    '"theorem_closure": true',
    '"status": "SOLVED"',
    '"status": "THEOREM_CLOSED"',
]:
    assert forbidden not in a, f"forbidden artifact token present: {forbidden}"

print("Perelman PL conditional closure verified: CONDITIONAL_EXTERNAL_THEOREM_ONLY / FRONTIER_PRESERVED")
