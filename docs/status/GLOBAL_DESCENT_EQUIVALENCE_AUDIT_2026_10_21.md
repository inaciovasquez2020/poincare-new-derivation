# Global descent equivalence audit

**Status:** proved reduction / open target remains open  
**Date:** 2026-10-21  
**Scope:** Lean statement-level audit of the current global `PhiSupport` descent route.

## Result added

`lean/Poincare/GlobalDescentEquivalence.lean` proves

```text
SimplyConnectedGlobalPhiSupportDescent
  ↔ EverySimplyConnectedCoreHasNormalizedHomeomorphicTriangulation
```

The forward implication is the existing strong-induction argument. The reverse implication is immediate: a normalized representative has `PhiSupport = 0`, which is strictly below any positive starting defect, and the required carrier homeomorphism is part of the representative-existence statement.

## Why this matters

This identifies the exact logical burden. The current global descent hypothesis is not an intermediate local lemma that follows merely by composing the degree-four site theorem with induction. It is equivalent to the universal normalization statement the descent program is intended to establish.

The current local result
`ClosedTriangulationCore.exists_topology_preserving_PhiSupport_descent_or_no_degree_four`
handles the degree-four branch and explicitly leaves the alternative
`∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4`.
The cross-polytope witness has eight represented vertices, degree eight at each represented vertex, and `PhiSupport = 32`; it is a concrete closed-core 3-sphere example showing that positive defect and the honest 3-sphere topology do not force a degree-four vertex. The repository also certifies that no single legal 3-to-2 move strictly lowers its `PhiSupport`, while a legal 2-to-3 followed by two 3-to-2 moves gives a topology-preserving block with lower defect. These are useful finite obstructions and a concrete escape block, but they do not establish a universal descent theorem for arbitrary triangulations.

## What is and is not proved

**Proved by this change**
- The global descent proposition and universal normalized-representative proposition are logically equivalent, under the exact existing Lean definitions.
- The equivalence uses no new axioms and no unverified geometric claim.

**Not proved by this change**
- Universal normalized-representative existence.
- A well-founded global high-fan/cycle-shortening argument.
- The unconditional Poincaré conjecture.
- That the local Pachner block observed for the cross-polytope extends to every positive-defect simply connected closed 3-manifold.

## Mathematical next obligation

To advance the conjecture, a future theorem must establish universal normalized-representative existence by an independent argument, or prove a genuinely local/global move theorem whose hypotheses are strictly weaker than that universal conclusion and whose termination is independently justified. Repackaging the global descent hypothesis under another name would not close the proof.
