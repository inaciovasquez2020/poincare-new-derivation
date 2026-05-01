# PND Proof-Hole Triage — 2026-05-01

Conditional.

- Total `sorry`: **55**
- Total `admit`: **0**
- Total `axiom`: **31**
- Total holes: **86**

This is a proof-hole inventory only. It does not assert theorem-level closure.

| File | sorry | admit | axiom | total |
|---|---:|---:|---:|---:|
| `lean/Poincare/FinalConstructive.lean` | 30 | 0 | 0 | 30 |
| `lean/Oblivion/CanonicalCodes.lean` | 16 | 0 | 0 | 16 |
| `lean/Regge/HolonomyMatrixModel.lean` | 0 | 0 | 11 | 11 |
| `Poincare/GreedyDescent.lean` | 5 | 0 | 0 | 5 |
| `lean/Regge/ReggeComplete.lean` | 2 | 0 | 3 | 5 |
| `lean/Regge/ReggeMathComplete.lean` | 0 | 0 | 5 | 5 |
| `lean/Regge/Core.lean` | 0 | 0 | 2 | 2 |
| `lean/Regge/HolonomyDerived.lean` | 0 | 0 | 2 | 2 |
| `lean/Regge/Pachner.lean` | 0 | 0 | 2 | 2 |
| `Poincare/Foundations.lean` | 0 | 0 | 1 | 1 |
| `lean/Cyclone/CycleBasisLift.lean` | 1 | 0 | 0 | 1 |
| `lean/Oblivion/LASRStandalone.lean` | 1 | 0 | 0 | 1 |
| `lean/Poincare/GreedySelectorCorrect.lean` | 0 | 0 | 1 | 1 |
| `lean/Poincare/VertexDefectPhiPos.lean` | 0 | 0 | 1 | 1 |
| `lean/Regge/FinalClosure.lean` | 0 | 0 | 1 | 1 |
| `lean/Regge/Holonomy.lean` | 0 | 0 | 1 | 1 |
| `lean/Regge/ReggeFinal.lean` | 0 | 0 | 1 | 1 |

## First reduction target

Target the largest local concentration first: `lean/Poincare/FinalConstructive.lean`.

Permitted first move:

1. Replace exactly one `by sorry` in `lean/Poincare/FinalConstructive.lean` with either a proof or a named local theorem statement.

No unconditional Poincaré theorem is asserted.
