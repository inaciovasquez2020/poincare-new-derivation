# Finite Pachner witnessed-reentry search (2026-11-15)

**Evidence status: COMPUTATION_PASS for the specified 6- and 7-vertex reachable components only.**
**Global conjecture: OPEN. Lean kernel verification: NOT_RUN.**

## Scope

The seed is the boundary of the 4-simplex, followed by all labeled iterated 1-to-4 tetrahedron subdivisions up to the requested vertex count. From those seeds, breadth-first search visits all labeled triangulations reachable by legal 2-to-3 and 3-to-2 moves **without changing vertex count**. This is **not** an enumeration of all closed 3-manifold triangulations or all triangulations of S³ at a given vertex count.

The detector tests a necessary configuration for `Move32SourceFaceWitnessedReentry`: an obstructed degree-three shared edge, two tetrahedra on its opposite face with distinct complementary vertices, a nonself complementary edge, exactly three tetrahedra around the new edge, and an obstruction at the new edge's opposite triangle. The reference detector and the independent detector agree on witness presence for tested states. The independent audit also tests closed triangular-face incidence, Euler characteristic, connected spherical vertex links, and local move exchange bookkeeping.

## Reproducibility

Run from the repository root (Python 3, standard library only):

```sh
tmp="$(mktemp -d)"
python3 scripts/experiments/poincare_full_reentry_test.py \
  --vertices 6 7 --seconds-per-case 35 \
  --max-states 150000 --output "$tmp/reentry_receipt.json"
```

Do not overwrite the historical receipt on an ordinary rerun. The harness returns exit code **0** only when all requested components complete without finding a witness, **2** when any component is incomplete or finds a witness, and **3** for an audit error. Always inspect the JSON statuses; code 2 does not discriminate between an actual witness and a resource limit.

Recorded run: Python 3.13.5. Script SHA-256:
- `poincare_full_reentry_test.py`: `adf218d97700b9eda8056c834cb0f8ea4d843e550c530ee4ac62e84a5f2947e1`
- `poincare_reentry_bfs.py`: `f8f0f26638ef3432a12d5ade964f62231032bba134efe11a73a3d2dcaf3b6f4d`

Results independently reproduced from the attached scripts:
- Six vertices: 25 states, 120 directed moves, 120 obstructed 3-to-2 sites, zero complementary edges present; COMPLETE_NO_WITNESS.
- Seven vertices: 2,145 states, 18,480 directed moves, 6,300 obstructed 3-to-2 sites, zero complementary edges present; COMPLETE_NO_WITNESS.
- Aggregate: 2,170 states, 18,600 directed moves, 6,420 obstructed 3-to-2 sites, zero qualifying reentry witnesses.
- Recorded eight-vertex search: **INCOMPLETE** at the state cap; the earlier generator discovered 150,002 states despite a nominal 150,000 cap. Do **not** interpret this as a pass. The newer harness guards the cap and reports INCOMPLETE.

The `full_reentry_receipt.json` records per-case state-stream digests and source hashes; `eight_vertex_incomplete_receipt.json` documents only the historical incomplete search. No claim of exhaustive eight-vertex coverage.

## Mathematical boundary

Neither zero reentry witnesses in these finite components nor termination of pure 3-to-2 sequences establishes `SimplyConnectedStabilizedPathDescent`. Fan/reentry cycle exclusion and universal certified unlocking remain **OPEN**. No sorry-free Lean theorem was produced by this experiment. Do not count these receipts as Poincaré proof completion, an independent mathematical review, or a repository CI run.

The remote commit carrying this evidence must be audited independently for exact files, permission changes, workflow effects, and source parity before any merge.
