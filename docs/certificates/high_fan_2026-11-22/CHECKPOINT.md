# High-fan geometric filling and cyclic-rigidity checkpoint

Date: 2026-11-22
Base HEAD: 0e44ea28333f5fc5e59f5cbfd84a2424303e6954

## Lean-verified results

- Genuine perpetual geometric high-fan trajectory.
- Nonconsecutive recurrent supported-edge trajectory.
- Closed geometric recurrence loop.
- Null-homotopy under the stated simple-connectedness assumption.
- Finite dyadic common-coface filling without a no-high-edge assumption.
- Successive genuine high-fan edges have disjoint endpoints.

The two newly integrated sources were compiled in an isolated
Lean 4.30.0-rc1 environment against the existing repository sources
and a separately compiled 24-module dependency overlay.

Permitted axioms:
- propext
- Classical.choice
- Quot.sound

## Exact finite tests

Boundary of the four-simplex:
- Five tetrahedra.
- PhiSupport = 0.
- All 65,535 nonempty subsets of a 16-cell constant filling passed.
- Strict PhiSupport descent impossible.

Boundary of the four-dimensional cross-polytope:
- 16 tetrahedra, eight vertices, PhiSupport = 32.
- 32 legal 2-3 moves, each increasing PhiSupport by 4.
- No initial legal 3-2 move.
- Two-step endpoints: 49 distinct labeled states, all PhiSupport 32.
- Four alternating-move endpoints: 1,561, all PhiSupport 32.

Cyclic polytope boundary C(6,4):
- Nine tetrahedra, six vertices.
- 72 ordered realizations of the specified four-tetrahedron
  different-transverse return pattern.
- Both return edges have incidence three in those realizations.
- No high-incidence two-cycle counterexample established.

The finite tests are not unrestricted mathematical proofs.

## Open obligations

- Different-transverse high-incidence two-cycle exclusion.
- Longer-cycle rigidity with retained transition witnesses.
- Boundary-to-interior transition compatibility sufficient for descent.
- Global topology-preserving PhiSupport descent.
- Independent Poincare derivation.

GLOBAL_POINCARE := OPEN

This checkpoint does not assert a proof of any open obligation.
