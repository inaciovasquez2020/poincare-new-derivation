#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQTriangleEuclideanInputSurfaceBridge.lean")
text = path.read_text()

required = [
    "import Regge.DSQEuclideanRealizabilitySurface",
    "import Regge.DSQMetricValidityInputSurface",
    "private def DSQTriangleEuclideanEdgeCoordBinding",
    "inputShape := DSQInputShape",
    "realizesDSQInputShape := rfl",
    "vertexCount := 3",
    "edgeCount := 3",
    "simplexCount := 1",
    "private def DSQTriangleEuclideanPredicateRefinement",
    "def DSQTriangleEuclideanMetricValidityInputSurface",
    "def DSQTriangleEuclideanMetricValid",
    "EuclideanRealizable2 (S.dSq e₀) (S.dSq e₁) (S.dSq e₂)",
    "metricValid := DSQTriangleEuclideanMetricValid",
    "structure DSQTriangleEuclideanInputSurfaceBridge",
    "source : DSQEuclideanRealizabilitySurface",
    "target : DSQMetricValidityInputSurface",
    "def DSQ_TRIANGLE_EUCLIDEAN_INPUT_SURFACE_BRIDGE",
    "theorem dsq_triangle_euclidean_input_surface_bridge_open",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required surface: {needle}")

for forbidden in [
    "def DSQ_METRIC_VALIDITY_THEOREM",
    "theorem DSQ_METRIC_VALIDITY_THEOREM",
    "axiom DSQ_METRIC_VALIDITY_THEOREM",
    "cmDet2_pos_of_realizable",
    "CayleyMenger",
    "VolumeSquared",
    "ReggeGeometryIntegration",
    "sorry",
    "admit",
    "axiom",
    "opaque",
]:
    if forbidden in text:
        raise SystemExit(f"forbidden theorem escalation found: {forbidden}")

print("DSQ_TRIANGLE_EUCLIDEAN_INPUT_SURFACE_BRIDGE_FOUND")
