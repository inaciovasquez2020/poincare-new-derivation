# Infinity stress test: the global-rigidity boundary

Status: **RESEARCH DESIGN — no new Lean theorem or Poincaré proof claimed.**

Target repository: `poincare-new-derivation`.

## 1. What “break the proved theorem with infinity” means

The Poincaré theorem concerns a **closed** (compact, without boundary), connected, simply connected 3-manifold. Its conclusion does not extend to arbitrary noncompact 3-manifolds: ℝ^3 is simply connected and noncompact, so it is not homeomorphic to S^3. Thus removing compactness breaks the theorem's conclusion without contradicting the theorem.

This is the first stress test: every proposed generalization must retain an explicit compactness/closedness hypothesis, or replace it with a separately proved condition strong enough to recover the required global conclusion.

A second, logically distinct infinity problem occurs inside a proof: a sequence of valid local moves may be infinite. Local legality alone implies neither termination nor convergence, and finite-state recurrence alone implies only recurrence, not contradiction.

## 2. The finite-to-infinite fault line in this repository

The current proof architecture contains useful finite combinatorial reductions:

- `PhiSupport` descent is a strict decrease of a natural-number-valued defect when the descent branch applies.
- `GlobalDegreeFourDescent` packages a topology-preserving descent from a degree-four vertex under its stated hypotheses.
- The high-fan route can produce finite recurrence of edge keys or mixed re-entry keys.
- `XGATE_CYCLIC_RIGIDITY_FRONTIER.md` correctly records that repeated local location can force successor-edge equality, but does not yet force equality of the full retained state or exclude longer recurrent cycles.

These facts must not be silently composed into a global termination theorem. In particular, when the process follows the no-descent branch, `PhiSupport` is constant because the triangulation is fixed; it is not a decreasing measure on the obstruction-state trajectory.

## 3. The repaired proof shape

Separate the argument into three gates.

### Gate A — finite certified descent

For a finite closed triangulation core (K), establish a transition theorem with explicit outputs:

1. a legal topology-preserving move with strictly smaller `PhiSupport`;
2. a certified terminal/zero-defect configuration; or
3. a high-fan obstruction state whose complete retained data is recorded.

Only branch (1) consumes the natural-number measure. Since `PhiSupport K` is a natural number, a chain of strict decreases has length at most its initial value. This proves termination **only if every nonterminal state is guaranteed to take branch (1) or branch (2)**. A remaining obstruction branch blocks that conclusion.

### Gate B — close the obstruction without pretending recurrence is descent

For a high-fan or mixed re-entry trajectory, define the full state to include every datum needed to determine the next-step relation: central edge, oriented location, adjacent link triangles, transverse carrier, chord endpoints, and witness/re-entry data.

Then prove one of the following from the actual manifold and link hypotheses:

- **Well-founded shortening:** every admissible recurrent obstruction contains a strictly smaller obstruction under a specified well-founded measure; or
- **Geometric exclusion:** every periodic full-state obstruction forces a prohibited local configuration, a legal move, or a topology-preserving strict descent.

Finite recurrence of a projected key is insufficient. Even periodicity of the full state is not a contradiction unless one of these geometric closure lemmas rules it out. A deterministic continuation can help only if determinism is proved from the geometry, not imposed as a convenience.

### Gate C — global recognition

After the obstruction is closed, separately prove the chain:

`finite closed triangulation core`
`\u2192` terminating topology-preserving reduction
`\u2192` zero-defect/terminal classification
`\u2192` genuine topological recognition of (S^3).

Do not identify the legacy predicate `S3 K := PhiSupport K = 0` with topological recognition. Use the normalized closed-core/topological interface and prove that the terminal classification entails the geometric conclusion. Only then may the result be connected to a Poincaré statement.

## 4. Explicit infinity audit

Any proposed extension must answer all of these:

1. **Compactness:** Where is finiteness of the triangulation or compactness of the realized manifold used?
2. **Local finiteness:** If an infinite triangulation is admitted, are vertex links finite and are local moves well-defined?
3. **Finite defect:** Is `PhiSupport` finite and well-defined? If not, what replaces its natural-number descent?
4. **Escape to infinity:** Can the sequence of moves drift through infinitely many disjoint regions while every local step remains legal?
5. **Limit validity:** If finite stages converge, what topology and compactness theorem produce a limiting triangulation/manifold, and why does it preserve the required hypotheses?
6. **Recognition:** Why does the terminal invariant characterize (S^3), rather than merely a local combinatorial condition?

No answer may be inferred solely from the classical Poincaré theorem: that theorem classifies the compact closed case; it does not supply the missing transition, termination, or limit lemmas for this framework.

## 5. Weakest missing result and priority

**Rank 1 — cyclic rigidity for the full retained high-fan/re-entry state.** Prove well-founded shortening or geometric exclusion under the already stated `ClosedTriangulationCore`, closed-connected 3-manifold, connected-link, no-degree-four, no-Move23, no-descent, and no-high-edge assumptions. This is the immediate blocker identified by the current frontier document.

**Rank 2 — total progress alternative.** Show every positive-defect state either has a certified topology-preserving strict descent or enters a state covered by Rank 1. Without this, natural-number descent does not prove termination.

**Rank 3 — zero-defect recognition.** Prove that the terminal condition entails the intended topological (S^3) conclusion on the correct normalized domain, without relying on a predicate that merely renames zero defect.

**Rank 4 — noncompact extension, if desired.** State a different theorem with explicit hypotheses controlling local finiteness, finite defect, escape to infinity, and limiting topology. The ordinary Poincaré conclusion must not be asserted for arbitrary noncompact manifolds.

## 6. Formal boundary

`BOUNDARY := ¬ Poincare.JIID`

This is a statement of the current proof boundary, not a claim that JIID is false. No global theorem follows from this design note. The next formal change should be the single weakest lemma: a cycle-shortening or geometric-exclusion invariant for the full retained state, proved from existing hypotheses and then tested against an explicit abstract finite-state countermodel to prevent projected-key reasoning from reappearing.
