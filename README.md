# Poincaré Conjecture — New Derivation Attempt

**Status:** Conditional / Not proven.

## Scope

A combinatorial descent program on triangulated closed simply connected 3-manifolds. The current repository frontier is a formally developed local obstruction/descent framework; it does **not** establish an unconditional proof of the Poincaré conjecture.

## Core object

For the repository's finite tetrahedron-list model $K$, let
$V(K)$ be the distinct vertices appearing in its tetrahedra and let
$d_K(v)$ count occurrences of $v$ among those tetrahedra. Under the
no-repeated-vertices condition supplied by `ClosedTriangulationCore K`,
this is the number of incident tetrahedra. The actual supported-vertex
defect used by the descent program is

$$
\Phi_{\mathrm{support}}(K)
   =\sum_{v\in V(K)} |d_K(v)-4|.
$$

Lean: `lean/Poincare/Triangulation.lean` defines `targetDegree := 4`,
`vertexDefect` and `PhiSupport`. Do not confuse `PhiSupport` with
`Phi`: the latter folds over `allVerts` **with multiplicities**, whereas
`PhiSupport` folds over `vertexSupport` with duplicates removed.
The earlier README's degree-six reference was inconsistent with this
degree-four formalization and is superseded here.

The predicate named `S3 K` in this minimal combinatorial source is
currently **defined as** `normalized K`, where
`normalized K := PhiSupport K = 0`. Its name alone does **not** establish
a geometric homeomorphism $|K|\cong S^3$; that conclusion requires
separate topological hypotheses and proofs.

## Admissible local moves

$$
\mathcal M=\{(1\leftrightarrow 4),(2\leftrightarrow 3)\}.
$$

These preserve homeomorphism type.

## Structural program

The program seeks a rigorous descent/obstruction route:

1. Define admissible Pachner-type local moves.
2. Define a defect functional $\Phi$.
3. Establish local descent or a structural obstruction when descent is unavailable.
4. Control recurrent high-fan behavior.
5. Establish the remaining global implications needed for an unconditional Poincaré theorem.

The current work has advanced substantially through the local obstruction/descent layers, but the final global closure is not established.

## Current frontier

[PR #181](https://github.com/inaciovasquez2020/poincare-new-derivation/pull/181) adds an ordered arbitrary-position 1→4 insertion and proves an obstruction to literal list equality with the existing head-inserting inverse. Positional closed-core preservation and global descent remain open.

Earlier merged work (#105–#112) develops and constrains recurrent high-fan configurations:

- **#105:** repeated retained local fan location has a unique transverse carrier.
- **#106:** repeated retained local fan data determines the chord endpoints.
- **#107:** recurrence at a repeated fan location admits a local shortening reduction.
- **#108:** distinct retained-neighbor choices give distinct FanChordTransition states.
- **#109:** represented triangular faces admit an exact cross-face tetrahedron completion.
- **#111:** the first-ear two-sided obstruction branch was carried through verification work.
- **#112:** a realized exact-three Move32 site yields either strict $\Phi$-support descent or a source-face obstruction; in the no-degree-four branch, that obstruction forces a nonself high-incidence source edge.

These are local/structural results. They do **not** by themselves exclude every possible recurrent high-fan configuration and do not prove `Poincare.JIID` or the Poincaré conjecture.

## LocalDelta

- `lean/Poincare/LocalDelta.lean` records local Pachner-move delta classification for the **degree-four** `defect` function.
- The module classifies local signed `Δ` values of the degree-four defect from degree multisets and does not claim strict global descent.
- The repository also contains a concrete nonuniform 2-to-3 positive-sign certificate.

## Verified incidence-count identity (scoped)

At remote main revision `ea6b6c5f22858b5e7fc3c38e616303147b62e69b`,
`lean/Poincare/PhiSupportEulerCount.lean` proves:

```lean
theorem ClosedTriangulationCore.PhiSupport_eq_four_mul_tets_sub_vertices
    {K : Triangulation} (hcore : ClosedTriangulationCore K) :
    PhiSupport K = 4 * (K.tets.length - (vertexSupport K).length)
```

This is an **incidence-counting identity**, conditional on the explicit
`ClosedTriangulationCore K` hypothesis (distinct vertices per tetrahedron,
no duplicate tetrahedron vertex sets, and exactly two incident tetrahedra
at each represented triangular face). It does not assert global descent,
topological sphere recognition, or the Poincaré conjecture. The subtraction
in the displayed Lean theorem is natural-number subtraction.

The existing [Lean CI run](https://github.com/inaciovasquez2020/poincare-new-derivation/actions/runs/42221418648)
built `Poincare.PhiSupportEulerCount` and checked `#print axioms`.
Reported dependencies were `[Classical.choice, Quot.sound, propext]`.
This is a prior remote CI receipt, **not** an independently reproduced
Mac build. Full global JIID remains **OPEN**.

Reproduce under the repository's pinned toolchain
(`leanprover/lean4:v4.30.0-rc1`):

```bash
set -euo pipefail
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
lake build Poincare.PhiSupportEulerCount
printf '%s\n' 'import Poincare.PhiSupportEulerCount' '#print axioms Poincare.ClosedTriangulationCore.PhiSupport_eq_four_mul_tets_sub_vertices' > "$tmp/axioms.lean"
lake env lean "$tmp/axioms.lean"
```

## Minimal valid conditional status

A global conditional closure can be stated only relative to the remaining load-bearing assumptions/lemmas, including:

- Global strict descent (not established):
$$
\forall T\not\simeq S^3,\ \exists T'\in\mathcal M(T)\ \text{s.t.}\ \Phi_{\mathrm{support}}(T')<\Phi_{\mathrm{support}}(T).
$$
- Geometric zero-defect characterization (not supplied by the definitional alias `S3 K := normalized K`):
$$
\Phi_{\mathrm{support}}(T)=0 \;\Longrightarrow\; |T|\cong S^3.
$$

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
