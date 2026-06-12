#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQMetricValidityTheoremTarget.lean")
text = path.read_text()

required = [
    "import Regge.DSQMetricValidityInputSurface",
    "structure DSQMetricValidityTheoremTarget where",
    "surface : DSQMetricValidityInputSurface",
    "theoremStatement : Prop",
    "realizesMetricValidityStatement :",
    "def DSQ_METRIC_VALIDITY_THEOREM_TARGET : Prop :=",
    "theorem dsq_metric_validity_theorem_target_surface_open",
    "Classical.choice dsq_metric_validity_input_surface_open",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required target-shell fragment: {needle}")

for forbidden in ["axiom ", "opaque ", "sorry", "admit"]:
    if forbidden in text:
        raise SystemExit(f"forbidden proof-debt marker found: {forbidden}")

for premature in [
    "def DSQ_METRIC_VALIDITY_THEOREM : Prop",
    "theorem dsq_metric_validity_theorem :",
    "def DSQ_EUCLIDEAN_REALIZABILITY",
    "def DSQ_VOLUME_SQUARED_SURFACE",
]:
    if premature in text:
        raise SystemExit(f"forbidden premature target found: {premature}")

print("DSQ_METRIC_VALIDITY_THEOREM_TARGET_SURFACE_FOUND")
