# Perelman PL Conditional Closure — 2026-05-05

Status: CONDITIONAL_EXTERNAL_THEOREM_ONLY

## Result

The repository now records a named external theorem axiom:

```lean
axiom Perelman_PL :
  ∀ K : Triangulation, S3 K
and the conditional theorem:
theorem conditional_PL_poincare_recognition
    (K : Triangulation) :
    S3 K :=
  Perelman_PL K
Boundary
This is not theorem-level Lean closure.
It does not prove the Poincare conjecture inside this repository.
It does not remove the existing axiom/sorry layer.
It does not repair the placeholder semantics:
def applyMoveImpl (K : Triangulation) (_m : PachnerMove) : Triangulation := K
Quarantined obstruction
The repository explicitly records:
theorem applyMoveImpl_identity
    (K : Triangulation) (m : PachnerMove) :
    applyMoveImpl K m = K := by
  rfl
and:
theorem current_applyMoveImpl_blocks_strict_descent
    (K : Triangulation) (m : PachnerMove) :
    ¬ Phi (applyMoveImpl K m) < Phi K := by
  simp [applyMoveImpl]
Admissible description
poincare-new-derivation contains a conditional PL-recognition wrapper around a named external theorem axiom, while preserving the repository's FRONTIER/CONDITIONAL status.
Forbidden description
Do not describe this repository as:
theorem-level closed;
a machine-checked proof of Poincare;
a solved Clay/Millennium proof artifact;
internally proving Perelman;
internally proving strict Pachner descent.
