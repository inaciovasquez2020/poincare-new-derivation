#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQConcreteMetricValidityPredicate.lean")
text = path.read_text()

required = [
    "import Regge.DSQMetricValidityTheoremTarget",
    "def DSQConcreteMetricCarrierPredicate",
    "0 < c.vertexCount ∧ 0 < c.edgeCount ∧ 0 < c.simplexCount",
    "structure DSQConcreteMetricValidityPredicate where",
    "target : DSQMetricValidityTheoremTarget",
    "carrierPredicate : Prop",
    "realizesCarrierPredicate :",
    "def DSQ_CONCRETE_METRIC_VALIDITY_PREDICATE : Prop :=",
    "theorem dsq_concrete_metric_validity_predicate_surface_open",
    "Classical.choice dsq_metric_validity_theorem_target_surface_open",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required predicate fragment: {needle}")

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

print("DSQ_CONCRETE_METRIC_VALIDITY_PREDICATE_SURFACE_FOUND")
