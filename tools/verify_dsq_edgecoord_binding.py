#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQEdgeCoordBinding.lean")
text = path.read_text()

required = [
    "import Regge.DSQInputShape",
    "structure DSQReggeComplex where",
    "structure DSQEdgeCoordBinding where",
    "inputShape : Type 1",
    "realizesDSQInputShape : inputShape = DSQInputShape",
    "def DSQ_EDGECOORD_BINDING_TO_REGGE_COMPLEX : Prop :=",
    "theorem dsq_edgecoord_binding_surface_open",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required surface fragment: {needle}")

for forbidden in ["axiom ", "opaque ", "sorry", "admit"]:
    if forbidden in text:
        raise SystemExit(f"forbidden proof-debt marker found: {forbidden}")

print("DSQ_EDGECOORD_BINDING_SURFACE_FOUND")
