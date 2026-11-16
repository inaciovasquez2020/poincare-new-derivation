# G2 cyclic-face verification checkpoint — 2026-11-16

## Scope and evidence

This is a **research checkpoint and receipt index**, not an integrated Lean module or a proof of the independent Poincaré conjecture. The Lean sources below were compiled **only on the researcher's Mac** in isolated temporary files; they have **not** been copied into this GitHub branch. The reported compiler and axiom results are taken from the user's Mac terminal transcripts. No GitHub CI run at the new branch is asserted.

- Authoritative source repository commit for these Mac checks: `efb1c31bc95e5a1218e80ac2bfc3b9d42d1317e1`
- Toolchain: `leanprover/lean4:v4.30.0-rc1`
- Allowed audited axioms: `propext`, `Classical.choice`, `Quot.sound`
- Mac worktree inspected clean at the indicated source commit; repository remained unchanged during the isolated proofs.
- Local-only Mac source paths are **evidence locators, not portable GitHub artifacts**. Their continued availability depends on the Mac's temporary directory.

## G2 exact intersection and fan results

Reported `LEAN_EXIT_CODE := 0` and `AXIOM_AUDIT := PASS` at the exact source commit:

1. Four actual geometric dual-flag triangle intersection configurations: singleton at edge barycenter, shared face–edge segment, shared tetrahedron–edge segment, and identical-support triangle. Verified Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.L0Luvpu0qG/G2AllFourExactIntersections.lean`.
2. All-case package `Poincare.PR199G2.closedCore_all_pairwise_dualFlag_intersections`, together with the existing cyclic-fan constructor `Poincare.ClosedTriangulationCore.exists_ambientEdgeCyclicFan_of_topologicalThreeManifold`. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.88urt87dj2/G2CyclicGluingBoundaryAudit.lean`.
3. `ambientFan_covers_dualFlag_tet`: each geometric dual flag's tetrahedron is covered by the cyclic fan. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.rnS1KSXSzq/G2FanDualFlagTetCoverage.lean`.
4. `ambientFan_tet_range_eq_incident` and `ambientFan_dualFlag_unique_tet_index`: exact tetrahedron range and unique fan index per flag tetrahedron. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.LaU0XrMBSY/G2ExactFanTetIndexFixed.lean`.
5. `ambientFan_adjacent_common_face_support`: graph-adjacent fan tetrahedra have a nondegenerate common triangular face. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.ha9Tx4A3yC/G2AdjacentCommonFaceSupport.lean`.
6. `ambientFan_common_face_forces_graph_adjacency`, `ambientFan_graph_adjacency_iff_common_third_vertex`: graph adjacency corresponds to distinct incident tetrahedra sharing a third vertex away from the edge endpoints. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.TQUzySpvvS/G2CommonFaceGraphAdjacency.lean`.
7. `ambientFan_vertexLinkStar_degreeTwo` and `ambientFan_all_graph_neighbors_classified`: specialize the existing `ClosedTriangulationCore.vertexLinkStarDegreeTwo` theorem to the cyclic fan. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.sDPLZ08dC4/G2FanDegreeTwoBridge.lean`.
8. `ambientFan_cycle_subgraph_degreeTwo`: every represented cycle vertex has exactly two neighbors in the walk subgraph. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.Dclsz97Gk2/G2CycleSubgraphDegreeTwo.lean`.
9. `finite_spanning_equal_degrees_eq_top`: generic finite spanning subgraph equality, using `Finset.univ.filter` and equal vertex degrees. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.VpAUqXOjaU/G2FiniteGraphEqualityPropFixed.lean`.
10. `ambientFan_cycle_subgraph_eq_top`: the spanning fan cycle contains all edges of the represented link-star graph. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.0GtYpD2C1i/G2ActualCycleGraphEquality.lean`.
11. `ambientFan_cycle_adjacency_iff_common_face`: adjacency in the walk subgraph iff the corresponding distinct ambient tetrahedra share a third vertex away from the central edge. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.Csnv9ySqg4/G2CycleFaceCorrespondence.lean`.
12. An integrated replay of nine load-bearing G2 prerequisites succeeded (`LEAN_EXIT_CODE=0`, axiom audit PASS) in `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.xds7mTHi1F/G2IntegratedAcceptance.lean`.
13. `four_common_vertices_force_same_support` and `unique_shared_face_third_vertex`: four distinct common tetrahedron vertices force equal support; distinct supports imply uniqueness of the third vertex of a shared face through the fixed edge. Both passed at the exact source commit with the allowed axioms. Mac source: `/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.gknDpworEX/G2UniqueSharedFaceCardinalityFixed.lean`.

The unique-third-vertex result is an **isolated theorem** over distinct tetrahedral supports, **not yet integrated** with the particular fan's closed-core distinct-support certificate.

## Exact remaining obligations (OPEN)

1. **G2_FAN_DISTINCT_SUPPORT_BRIDGE** — connect the unique shared-face lemma to the actual `AmbientEdgeCyclicFan` tetrahedra using `ClosedTriangulationCore` pairwise distinct-support hypotheses.
2. **G2_FACE_TO_CYCLIC_INDEX_BIJECTION** — prove every and only actual dual faces correspond to the two flags incident to each cycle edge, with unique face support and closing adjacency.
3. **G2_FINITE_CYCLIC_DISK_GLUING** — construct the finite triangle-gluing object and a continuous bijective parameterization from a closed disk or an explicitly equivalent finite cone.
4. **G2_EMBEDDED_GEOMETRIC_DUAL_DISK** — prove that the parameterization identifies no unintended geometric points, using all four exact intersection configurations, and construct the homeomorphism.
5. **G2_BOUNDARY_EQ_FAN** — identify the embedded disk boundary precisely with the cyclic fan boundary and connect it to the verified G1 mod-two chain statement.
6. **G2_GLOBAL_HOMOLOGY_BRIDGE** and **GLOBAL_DESCENT_OR_ALTERNATIVE_CLOSURE** — close the genuinely global obligations of the independent derivation; no conclusion follows merely from local dual-disk topology.

**GLOBAL_POINCARE := OPEN.** Classical Poincaré's theorem is established externally; this project seeks a separate Lean-verified derivation.

## Promotion and reproducibility policy

- Preserve the uncommitted/local-only source evidence on the Mac; do not delete or prune worktrees or temporary directories on the strength of this index.
- The original G2 Mac sources must be transferred **without editing their proofs**, installed in an appropriate repository module, compiled against the pinned toolchain, and audited at the integration commit before claiming repository-level `LEAN_VERIFIED`.
- The new GitHub documentation commit records status only; it **does not** establish that source transplantation or GitHub CI succeeded.
- No merge or publication of a global Poincaré theorem is authorized by this checkpoint.
