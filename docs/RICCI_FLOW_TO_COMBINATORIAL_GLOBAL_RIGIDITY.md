# From Ricci-Flow Extinction to Combinatorial Global Rigidity: Proof Obligations

Status: research note; analogy and proof plan only. This document does **not** prove the Poincare conjecture, global cyclic rigidity, or a new theorem about Ricci flow.

## 1. What survives the infinity stress test

The round-sphere family
\[
g_R(t)=(R^2-4t)g_{\mathrm{unit}},\qquad T_R=R^2/4
\]
shows that compact examples can have extinction times tending to infinity as their scale tends to infinity. Its pointed limit is stationary Euclidean flow. This breaks the invalid inference that finite extinction of every compact approximant must pass to a noncompact pointed limit with a uniform finite time.

It does not break Perelman's finite-extinction theorem for each qualifying closed initial 3-manifold. The theorem's conclusion is pointwise in the initial metric; a uniform bound across a family requires uniform control of the data entering the estimate.

## 2. The transferable proof pattern

The Colding–Minicozzi width argument has four logically distinct pieces:

1. **Admissible state:** a smooth closed 3-manifold and a Ricci flow in the theorem's domain.
2. **Persistent nonnegative quantity:** sweepout width W(t) >= 0 while the relevant component survives.
3. **Controlled evolution:** a differential inequality whose negative term is strong enough after accounting for curvature-dependent terms.
4. **Contradiction:** integration would force W(t) < 0 if the flow survived beyond a finite threshold.

The contradiction depends on all four pieces. A local decrease statement alone is not a global termination proof.

## 3. Combinatorial analogue for the triangulation program

For a triangulation or move graph, the analogous obligations should be written explicitly rather than inferred from repeated local success.

- **State space:** specify the triangulations and equivalence relation; distinguish a finite search graph from the full, potentially infinite move graph.
- **Admissible transitions:** prove each allowed move preserves the intended manifold/topological class.
- **Potential:** define a natural-number-valued or otherwise well-founded invariant Phi on every state in the theorem's domain.
- **Strict descent or bounded recurrence:** prove each nonterminal state has an admissible transition that strictly decreases Phi, or prove a separate global theorem that rules out infinite nonterminal paths.
- **Terminal classification:** prove that a terminal state has the exact desired structure; do not identify “no move found by this search” with mathematical terminality.
- **Coverage:** prove that the invariant and transition claims apply to every allowed state, not just states reached in a finite experiment.

If the only result is that a move decreases Phi when a particular local configuration exists, then the missing step is to show that every nonterminal state must eventually expose such a configuration, or to find a different global invariant. That is the combinatorial analogue of the gap between a local evolution inequality and a uniform global conclusion.

## 4. Infinity / escape audit

Any proposed global descent theorem should explicitly rule out these failure modes:

1. **Scale escape:** the potential or bound changes under rescaling/relabeling, so a family evades a claimed uniform threshold.
2. **State-space escape:** an infinite sequence of legal moves continues without reaching a terminal state.
3. **Cycle:** moves return to a previous state or to an equivalent state without net descent.
4. **Branching ambiguity:** a local move exists but choices do not yield a globally coherent descent path.
5. **Domain leakage:** a lemma is proved for a restricted class, but the conclusion is asserted for a larger class.
6. **False terminal inference:** finite search exhaustion is treated as proof that no global continuation exists.

A finite-state countermodel can diagnose a missing logical implication, but it is not a counterexample to the Poincare conjecture unless it is realized by a valid closed 3-manifold triangulation and all move hypotheses are verified.

## 5. Proof frontier and next theorem target

The next useful theorem is not “local descent implies Poincare.” It is a precise bridge lemma of the form:

> For every admissible nonterminal triangulation in the stated class, there exists a topology-preserving legal move to an admissible state with strictly smaller well-founded potential.

This statement is only a target until its hypotheses, potential, move, and universal quantifier are fully specified and proved. If such a lemma is false, the correct next step is to construct a valid counterexample to that lemma and refine the potential or narrow the theorem's domain—not to claim a counterexample to Poincare.

## 6. What is and is not established

**Established in this research thread:** the round-sphere scaling calculation; the pointed Euclidean limit on bounded regions; the distinction between pointwise finite extinction and uniform family bounds; the integrated width estimate under its stated hypotheses.

**Not established:** a diameter-only uniform extinction-time bound or its impossibility; a global well-founded potential for the user's triangulation move system; global cyclic rigidity; Poincare.JIID; or a proof of the Poincare conjecture by the user's approach.

## References

- T. H. Colding and W. P. Minicozzi II, *Estimates for the extinction time for the Ricci flow on certain 3-manifolds and a question of Perelman*, J. Amer. Math. Soc. 18 (2005), arXiv:math/0308090.
- T. H. Colding and W. P. Minicozzi II, *Width and finite extinction time of Ricci flow*, Geom. Topol. 12 (2008), arXiv:0707.0108.
