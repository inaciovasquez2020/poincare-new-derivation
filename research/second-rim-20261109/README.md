# Second-rim conditional rigidity — research checkpoint (2026-11-09)

**Status:** preserved research artifact; not an integrated or global Poincaré proof.

**Remote baseline:** `03172442ae2d83ed0630c92b6aeb795269168e7a`.
The authoritative Mac checkout was last reported at that HEAD with its existing working state preserved. These files are kept under `research/`, outside the Lean build/import tree; none modifies existing theorems, `lakefile`, `lean-toolchain`, or the acceptance test.

## Compiled and axiom-audited on the user's Mac

Pinned `leanprover/lean4:v4.30.0-rc1`. Status reports below are from user-supplied Mac compiler outputs, **not independently recompiled in this GitHub branch**. All observed axioms are within the permitted `propext`, `Classical.choice`, `Quot.sound` set.

| Stored source | Load-bearing declarations | Mac result |
| --- | --- | --- |
| `verified/FanTriangleRepaired.lean` | `triangle_component_closed`, `no_fourth_vertex_in_triangle_fan` | PASS, no axioms |
| `verified/SecondRimOrderInvariantCore_20261109.lean` | `secondSourceTripleAvoidsOldB`, `secondTransverseOutsideOriginalFive` | PASS, `[propext]` |
| `verified/SecondRimActualTetTransport_20261109.lean` | `sourceFaceAbsentAfterConcretePrefix` | PASS, `[propext]` |
| `verified/SecondRimComposedAllInOne_20261109.lean` | `secondSourceFaceAbsent_of_realizedTargets_and_prefix` (contains earlier two base proof modules inline) | PASS, `[propext]` in Mac receipt `secondrim-composed.4jgdUWO5` |
| `verified/SecondRimCornerTraceback_20261109.lean` | `retained_witness_one_step`, `retained_witness_two_steps`, `first_corner_original`, `second_corner_original` | four stages PASS, `[propext]` |
| `verified/SecondRimFourthIncidentTet_20261109.lean` | `fourth_incident_of_incidence_four` | PASS, `[propext, Classical.choice, Quot.sound]`; corrected version only |

Additional Mac-verified temporary sources **not yet copied into this branch**:
- `Poincare.SecondRimHighSpokeActualTet.edgeAdj_symm`, `corner_edgeTriangle`, `no_fourth_reachable_corner`, `transverses_ne_of_represented_fourth`, Mac receipt `secondrim-high-spoke.nrj7Gfdq`, PASS (none or `[propext]`).
- `Poincare.SecondRimHighSpokeActualTet.transverses_ne_of_incidence_four`, Mac receipt `fourth-edge-bridge.4E2Yh2rt`, PASS `[propext, Classical.choice, Quot.sound]`. Verified source SHA-256: `1065ccc9a87c93a4aaedcd0810dec072d84ca90f51c3a93612a0875ee6a14c98`; underlying high-spoke source SHA-256: `e39c7696fc85855a36cb83f41811462f96c5686b69cbbca0a81d1ba9a976fed3`.

The archive versions of source files can contain original candidate/NOT_RUN comments predating the later successful Mac test; use this manifest and the actual Mac receipts for verified status. Conversely, a successful isolated build does **not** establish actual Move32Site integration.

## Explicitly uncompiled candidates

`open-integration/ThreeCornerActualLinkStarWitness_20261109.lean` is a **source-local insertion candidate** for `GlobalEdgeCyclicFanChordClassification.lean`; its dependency `AmbientEdgeCyclicFan.star_length_eq_three_of_triangle` is private. It is NOT_RUN.

`open-integration/SecondRimSiteFreshnessBridge_20261109.lean` is an actual-`Move32Site` integration candidate, NOT_RUN. Do not treat either candidate as established.

## Exact open proof boundary

1. Extract the three ordered/unordered corner-tetrahedron and retained-prefix witnesses from the concrete first/second `Move32Site` realizations **without assuming the second move is legal**.
2. Transport the verified abstract `Tet` edge adjacency to `vertexLinkStarGraph`. Existing `vertexLinkStarConnected_of_topologicalThreeManifold` and `ClosedTriangulationCore.vertexLinkStarDegreeTwo` exist but the required application is not compiled in this checkpoint.
3. Combine actual manifold edge-fan connectedness and degree two, incidence four, transverse separation, and the source-face absence certificate to establish `Move32Site.LegalIn`.
4. Independently compile and audit the integrated theorem and its full dependency and assumption chain. The research checkout previously reported missing compiled `.olean` modules; no full rebuild or acceptance test is claimed.

**GLOBAL_JIID := OPEN. UNIVERSAL_STABILIZED_DESCENT := OPEN. INDEPENDENT_POINCARE_DERIVATION := OPEN.** Classical Poincaré is known true; this independent derivation is not yet proved.

## Safety and promotion

This is a research-only archival branch. GitHub persistence does not establish that every local-only Mac artifact was included; the Mac is authoritative. No tracked proof file has been changed, and this checkpoint has not been merged or promoted to the formal acceptance path. Prior to any promotion, run the repository's actual toolchain/build, `#print axioms`, hypothesis/vacuity audit, diff audit, and relevant CI on the exact candidate branch.
