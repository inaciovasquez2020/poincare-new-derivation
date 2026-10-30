# Perelman PL Conditional Closure — corrected 2026-10-30

Status: CONDITIONAL_EXTERNAL_THEOREM_ONLY

## Correction

The previous declaration `axiom Perelman_PL : ∀ K : Triangulation, S3 K`
was **false**. In this repository `S3 K` abbreviates
`PhiSupport K = 0`, not homeomorphism to the 3-sphere. The represented
four-dimensional cross-polytope boundary has `PhiSupport = 32 > 0`.

`lean/Poincare/PerelmanPL.lean` now proves `universal_S3_false`
and introduces **no axiom**. `Perelman_PL` is a `Prop` definition:
a closed-core realization which is an honest closed connected topological
3-manifold and simply connected is homeomorphic to the Euclidean unit
3-sphere. This formulation preserves the appropriate topological conclusion;
it does not assert zero defect.

`conditional_PL_poincare_recognition` takes `hPL : Perelman_PL` as
an explicit hypothesis and applies it to `K`. The external result is
not supplied or proved by this repository.

`globalPhiSupportDescent_implies_Perelman_PL` records the existing
conditional route from the currently unproved strict global descent
premise. It makes no independent descent claim.

## Verification boundary

This is not theorem-level Lean closure.
It does not prove the Poincare conjecture inside this repository.
The project remains FRONTIER/CONDITIONAL; other pre-existing axioms,
native-decision audit findings, and unclosed global descent obligations
remain outside this isolated correction.

The `applyMoveImpl_identity` and
`current_applyMoveImpl_blocks_strict_descent` quarantine results still
apply. The legacy `applyMoveImpl` is not an executable strict descent
construction.

Do not describe this repository as a machine-checked independent proof
of Poincare, a finished Pachner descent proof, or a completed Clay result.
