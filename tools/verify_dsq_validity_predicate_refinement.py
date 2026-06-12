#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQValidityPredicateRefinement.lean")
text = path.read_text()

required = [
    "import Regge.DSQEdgeCoordBinding",
    "structure DSQValidityPredicateRefinement where",
    "binding : DSQEdgeCoordBinding",
    "isValidInput : binding.inputShape → Prop",
    "def DSQ_VALIDITY_PREDICATE_REFINEMENT : Prop :=",
    "theorem dsq_validity_predicate_refinement_surface_open",
    "Classical.choice dsq_edgecoord_binding_surface_open",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required surface fragment: {needle}")

for forbidden in ["axiom ", "opaque ", "sorry", "admit"]:
    if forbidden in text:
        raise SystemExit(f"forbidden proof-debt marker found: {forbidden}")

print("DSQ_VALIDITY_PREDICATE_REFINEMENT_SURFACE_FOUND")
