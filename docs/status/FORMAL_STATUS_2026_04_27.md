# Formal Status — 2026-04-27

Status: Deprecated / Conditional Sketch

## Build status

The repository builds, but build success is not theorem verification.

## Theorem status

This repository currently contains project-defined axioms and `sorry` proof holes.

- `axiom` is a trusted assumption, not a proof.
- `sorry` is a proof hole.
- Any result depending on project axioms or sorries is Conditional.
- No axiom-dependent or sorry-dependent result should be described as proved, closed, final, terminal, unconditional, or machine-verified.

## Current status

- Current classification: Deprecated / Conditional Sketch
- Strongest verified theorem: none asserted at repository level
- Weakest missing theorem: remove every load-bearing axiom and sorry, and formalize the core topological definitions against accepted Lean topology definitions
- Conditional inventory: `docs/status/DEPRECATED_CONDITIONAL_STATUS_2026_04_27.md`

## Boundary rule

If `axiom + admit + sorry > 0`, no Poincare-proof claim is allowed.
