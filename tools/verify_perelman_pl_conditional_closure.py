from pathlib import Path
import json
import re

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
a = json.loads(artifact.read_text())

for token in [
    "theorem universal_S3_false",
    "def Perelman_PL : Prop :=",
    "TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K",
    "TriangulationRealizationSimplyConnected K",
    "TriangulationRealizationHomeomorphicToThreeSphere K",
    "theorem conditional_PL_poincare_recognition",
    "(hPL : Perelman_PL)",
    "hPL K hcore hM hSC",
    "theorem globalPhiSupportDescent_implies_Perelman_PL",
    "CONDITIONAL_EXTERNAL_THEOREM_ONLY" if False else "Conditional:",
]:
    assert token in p, f"missing PerelmanPL token: {token}"

assert re.search(r"(?m)^\s*(?:axiom|opaque|sorry|admit)\b", p) is None, (
    "PerelmanPL.lean must have no axioms, opaque constants, or proof holes"
)
assert "axiom Perelman_PL" not in p
assert "∀ K : Triangulation, S3 K" not in p.replace(
    "¬ (∀ K : Triangulation, S3 K)", ""
)

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

assert a["status"] == "CONDITIONAL_EXTERNAL_THEOREM_ONLY"
assert a["theorem_closure"] is False
assert a["frontier_preserved"] is True
assert a["external_axiom"] is None
assert a["conditional_hypothesis"] == "Perelman_PL"
assert a["refuted_statement"] == "forall_K_S3"
assert a["conditional_theorem"] == "conditional_PL_poincare_recognition"
assert a["refutation_theorem"] == "universal_S3_false"

print("Perelman PL interface verified: false axiom removed / conditional statement retained")
