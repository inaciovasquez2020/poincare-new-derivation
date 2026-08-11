# Public Theorem Status

Date: 2026-08-11

Status: **CONDITIONAL CONSTRUCTIVE FRONTIER**

This repository contains a Lean 4 constructive combinatorial program related
to the Poincaré conjecture using triangulations, Pachner moves, vertex-link
topology, explicit geometric-carrier homeomorphisms, and the defect functional
`PhiSupport`.

## Strongest validated checkpoint

The validated public checkpoint reaches:

`Poincare.Move41Site.exists_represented_fiveTetCluster_nodup_of_targetPresent`

Validated infrastructure also includes:

- the `PhiSupport` defect calculus;
- exact Pachner-move degree/defect bookkeeping;
- the cross-polytope obstruction to normalization using only 2→3 / 3→2 moves;
- an explicit topology-preserving 2→3 → 3→2 → 3→2 escape;
- genuine Move23, Move32, and Move41 geometric-carrier homeomorphisms;
- exact Move41 degree and `PhiSupport` balance;
- topology-preserving strict Move41 descent under its certified criterion;
- degree-four vertex-link tetrahedral-boundary classification;
- the corrected degree-four Move41-or-target dichotomy;
- the overlap-connectivity counterexample/obstruction;
- connected-link propagation;
- target-present degree-four vertex-link closure;
- exact represented Move41 source tetrahedra;
- a represented five-tetrahedron target-present cluster;
- pairwise distinctness of that cluster.

## Current open frontier

The next unresolved theorem is the exact common-face closure of the
target-present five-tetrahedron cluster.

Subsequent major open objects include:

1. corrected global degree-four classification;
2. arbitrary manifold vertex-link Euler characteristic two;
3. universal positive-`PhiSupport` coverage;
4. topology-preserving global strict `PhiSupport` descent;
5. normalization by strong induction;
6. `Poincare.JIID`.

## Explicit non-claim

This checkpoint does **not** prove the Poincaré conjecture.

The following are explicitly open:

- `Poincare.exists_topology_preserving_PhiSupport_descent`
- `Poincare.exists_normalized_homeomorphic_triangulation`
- `Poincare.JIID`

Compilation, CI, intermediate certificates, or repository status must not be
interpreted as closure of these remaining objects.

The unfinished continuation after this checkpoint is preserved separately and
is not part of the validated public default branch.
