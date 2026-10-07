# Poincaré Conjecture — New Derivation Attempt

**Status:** Conditional / Not proven.

## Scope

A combinatorial descent program on triangulated closed simply connected 3-manifolds. The current repository frontier is a formally developed local obstruction/descent framework; it does **not** establish an unconditional proof of the Poincaré conjecture.

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

The program seeks a rigorous descent/obstruction route:

1. Define admissible Pachner-type local moves.
2. Define a defect functional \(\Phi\).
3. Establish local descent or a structural obstruction when descent is unavailable.
4. Control recurrent high-fan behavior.
5. Establish the remaining global implications needed for an unconditional Poincaré theorem.

The current work has advanced substantially through the local obstruction/descent layers, but the final global closure is not established.

## Current frontier

The latest merged work (#105–#112) develops and constrains recurrent high-fan configurations:

- **#105:** repeated retained local fan location has a unique transverse carrier.
- **#106:** repeated retained local fan data determines the chord endpoints.
- **#107:** recurrence at a repeated fan location admits a local shortening reduction.
- **#108:** distinct retained-neighbor choices give distinct FanChordTransition states.
- **#109:** represented triangular faces admit an exact cross-face tetrahedron completion.
- **#111:** the first-ear two-sided obstruction branch was carried through verification work.
- **#112:** a realized exact-three Move32 site yields either strict \(\Phi\)-support descent or a source-face obstruction; in the no-degree-four branch, that obstruction forces a nonself high-incidence source edge.

These are local/structural results. They do **not** by themselves exclude every possible recurrent high-fan configuration and do not prove `Poincare.JIID` or the Poincaré conjecture.

## LocalDelta

- `lean/Poincare/LocalDelta.lean` records local Pachner-move delta classification.
- The module classifies local `ΔΦ` from degree multisets and does not claim strict global descent.
- The repository also contains a concrete nonuniform 2-to-3 positive-sign certificate.

## Minimal valid conditional status

A global conditional closure can be stated only relative to the remaining load-bearing assumptions/lemmas, including:

- Local spherical descent:
\[
\forall T\not\simeq S^3,\ \exists T'\in\mathcal M(T)\ \text{s.t.}\ \Phi(T')<\Phi(T).
\]
- Zero-defect characterization:
\[
\Phi(T)=0 \;\Longrightarrow\; T\simeq S^3.
\]

The current local frontier does not establish these two global statements unconditionally.

## Formal Status

**Status:** Conditional / Open frontier

This repository contains project-defined `axiom` declarations and `sorry` proof holes. An `axiom` is a trusted assumption, not a proof; `sorry` is a proof hole. Results depending on these are conditional.

Build or CI success establishes artifact/build integrity only. It does not establish an unconditional Poincaré theorem.

The repository's proof-facing classification and external-status boundary are maintained in:

- `docs/status/LEAN_PROOF_PORTFOLIO_CLASSIFICATION.md`
- `docs/status/EXTERNAL_STATUS_LOCK.md`
- `docs/status/DEPRECATED_CONDITIONAL_STATUS_2026_04_27.md`

## Research boundary

The present frontier should be treated as a **frozen mathematical stopping point** unless a specific new obstruction, proof gap, or verification failure is identified.

The appropriate next work is independent verification, dependency auditing, and documentation of the existing results—not speculative expansion of the global claim.

## Submission scope

`docs/status/` contains the repository's submission-scope and status documents separating independently verified results, conditional reductions, computational evidence, formal verification artifacts, and remaining open problems.

## Bottom line

This repository contains a substantial formalized conditional research program for a new combinatorial route toward Poincaré. The local obstruction/descent framework has been materially strengthened, but the repository does **not** claim an unconditional proof of the Poincaré conjecture.
