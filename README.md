# Poincaré Conjecture — New Derivation Attempt

**Status:** Conditional / Not proven.

## Scope

A combinatorial descent program on triangulated closed simply connected 3-manifolds.

## Core object

For a finite triangulation \(T\) of a closed 3-manifold, define
\[
\Phi(T)=\sum_{v\in T}|d(v)-6|,
\]
where \(d(v)\) is the number of tetrahedra incident to \(v\).

## Admissible local moves

\[
\mathcal M=\{(1\leftrightarrow 4),(2\leftrightarrow 3)\}.
\]

These preserve homeomorphism type.

## Structural program

1. Define admissible Pachner-type local moves.  
2. Define a defect functional \(\Phi\).  
3. Prove strict local descent: \(\exists T'\) with \(\Phi(T')<\Phi(T)\) for non-spherical \(T\).  
4. Prove finite termination.  
5. Prove \(\Phi(T)=0\) characterizes the spherical model.

## Current state

Intermediate claims include unproved or false steps.

## Minimal valid status

Conditional on:

- Local spherical descent lemma:
\[
\forall T\not\simeq S^3,\ \exists T'\in\mathcal M(T)\ \text{s.t.}\ \Phi(T')<\Phi(T).
\]

- Zero-defect characterization:
\[
\Phi(T)=0 \;\Longrightarrow\; T\simeq S^3.
\]

## Repository additions

- Hypergraph Current terminal Wall (Chronicles), conditional closure.  
- EF-signature invariant and non-collision lemma.  
- Structured collision experiments (near-injective regime).  
- Spectral correction: HS operator requires squared resolvent decay.  


## LocalDelta

- `lean/Poincare/LocalDelta.lean` now records local Pachner-move delta classification.
- This module classifies local `ΔΦ` from degree multisets and does not claim strict descent.

## Formal Status

Status: Deprecated / Conditional Sketch

Build status:
- A successful build means the checked root target compiles.
- It does not imply that axiom-dependent or sorry-dependent results prove the Poincare conjecture.

Theorem status:
- This repository currently contains project-defined `axiom` declarations and `sorry` proof holes.
- `axiom` is a trusted assumption, not a proof.
- `sorry` is a proof hole.
- Any result depending on project axioms or sorries is Conditional.

Current status:
- Strongest verified theorem: `exists_recurrent_highFanEdgeState` (finite recurrent high-fan supported-edge state checkpoint); this does not prove `Poincare.JIID`.
- Weakest missing theorem: remove every load-bearing axiom and sorry, and formalize the core topological definitions against accepted Lean topology definitions
- Conditional inventory: `docs/status/DEPRECATED_CONDITIONAL_STATUS_2026_04_27.md`

## Lean proof portfolio classification

This repository is governed by [`docs/status/LEAN_PROOF_PORTFOLIO_CLASSIFICATION.md`](docs/status/LEAN_PROOF_PORTFOLIO_CLASSIFICATION.md). Its role in the portfolio is explicitly classified as proof-facing, conditional frontier, infrastructure/documentation, or legacy/scaffold.

## External status

This repository is governed by [`docs/status/EXTERNAL_STATUS_LOCK.md`](docs/status/EXTERNAL_STATUS_LOCK.md). Build success, CI success, dashboards, ledgers, axioms, admits, `sorry`, or placeholder witnesses do not constitute theorem-level closure.
