#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQEuclideanRealizabilitySurface.lean")
text = path.read_text()

required = [
    "namespace Regge",
    "def EuclideanRealizable2",
    "theorem euclideanRealizable2_equilateral",
    "theorem not_euclideanRealizable2_collinear",
    "abbrev DSQTriangleEdgeLengths",
    "def DSQTriangleMetricValid",
    "structure DSQEuclideanRealizabilitySurface",
    "def DSQ_EUCLIDEAN_REALIZABILITY_SURFACE",
    "theorem dsq_euclidean_realizability_surface_open",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required surface: {needle}")

for forbidden in [
    "namespace DSQ",
    "cmDet2",
    "cmDet2_pos_of_realizable",
    "def DSQ_METRIC_VALIDITY_THEOREM",
    "theorem DSQ_METRIC_VALIDITY_THEOREM",
    "axiom DSQ_METRIC_VALIDITY_THEOREM",
    "sorry",
    "admit",
    "axiom",
    "opaque",
]:
    if forbidden in text:
        raise SystemExit(f"forbidden theorem escalation found: {forbidden}")

print("DSQ_EUCLIDEAN_REALIZABILITY_SURFACE_FOUND")
