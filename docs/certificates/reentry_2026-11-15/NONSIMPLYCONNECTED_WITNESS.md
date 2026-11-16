# Nonsimply-connected witnessed-reentry regression certificate (2026-11-15)

**Status:** COMPUTATION_PASS for one finite explicit example; Lean NOT_RUN. **Full JIID: OPEN.**

The compact JSON stores 51 tetrahedra of a 16-vertex closed simplicial complex, exact-three old edge (2,4), obstructing opposite face (3,7,12), complementary edge (13,15), its exact-three incident tetrahedra, the resulting three-edge cycle, and a 12-edge mod-2 cocycle. The independent verifier checks:
- distinct tetrahedra and exactly two tetrahedra at every triangle;
- exact old/new edge incidences, both obstructed opposite faces, and nonself transition;
- zero boundary of the three-edge cycle;
- zero cocycle parity on **every** represented triangle;
- odd cycle/cocycle pairing, proving the three-edge cycle nonbounding over F₂ in this finite complex.

Run from repository root:

```sh
python3 scripts/experiments/verify_reentry_compact.py docs/certificates/reentry_2026-11-15/nonsimplyconnected_witness_compact.json
```

The full 115-move generator and independent replay were run and verified separately in the research session; the *compact* repository certificate does **not** include that full trace, and the checker does **not** independently prove a PL identification with S²×S¹. Accordingly, the repository scope is intentionally limited to a closed triangular-incidence complex with an explicit nonboundary cycle. The complete trace should be archived in a subsequent audited change if its full reproducibility is required.

This example refutes **unrestricted local witnessed-reentry exclusion** without a simple-connectedness/homology hypothesis. It does **not** refute the proposed exclusion for simply connected closed combinatorial 3-manifolds.

The universal bridge from a witnessed reentry to a global nonbounding cocycle, and the bridge from geometric simple connectedness to F₂ simplicial H₁ vanishing, remain OPEN in Lean. No global Pachner-descent proof is claimed. Existing Lean source and proof declarations are unchanged.
