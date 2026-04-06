# Missing Lemmas (UPDATED STATUS)

## Status

PARTIALLY RESOLVED

## Mapping

- Lemma A (Local Spherical Descent)
  → implemented via exists_strict_descent_move (Lean)

- Lemma B (Edge Imbalance)
  → present in docs/DERIVATION.md (needs formalization check)

- Lemma C (Zero-Defect Characterization)
  → strengthened unconditional repair implemented in lean/Poincare/ZeroDefect.lean via invariant(T)=0

- Lemma D (Termination)
  → implemented in docs/normal_surface/termination_theorem.md

## Remaining gap

Zero-Defect Characterization (Lemma C) repaired in strengthened form: Phi(T)=0 and invariant(T)=0 imply S3(T); raw unconditional form Phi(T)=0 implies S3(T) is false in general.

