# U(16) finite unlocking certificate

## Scope

This directory contains a **finite, deterministic Python computation** on the
104-facet cyclic Dougherty–Faber–Murphy U(16) simplicial 3-sphere construction.
It **does not** claim a general theorem, a Lean-verified certificate, or an
unrestricted descent strategy.

- `urf_u16_unlock_audit.py`: dependency-free exact combinatorial search.
- `urf_u16_unlock_receipt.json`: saved audit result and two explicit example
  move sequences.
- `u16_all_witness_manifest.py`: replays and independently checks the selected
  legal move sequence for **each of the 104** stabilization choices; `--all`
  emits the complete 104-witness JSON archive to standard output.
- `.github/workflows/u16-unlock-certificates.yml`: validates the reproduced
  receipt **and** all 104 witness digest on pull requests.

## Reproduced values

- Original complex: 16 vertices, 104 tetrahedra, complete 120-edge graph;
  no legal 2→3, 3→2, or 4→1 sites under the audited combinatorial rules.
- After each single 1→4 insertion: 107 tetrahedra; exactly 4 2→3 sites,
  0 3→2 sites, 1 inverse 4→1 site.
- After further 2↔3 moves: 96 cases expose an original-to-original
  edge 3→2 site at BFS depth 2; 8 cases first expose one at depth 3.
- Search visited 1,199 BFS nodes in total; 320 witness-move checks.
- Original facet digest (sorted normalized tetrahedra separated by newlines):
  `4e4e4e280195ff124ceb19c5ca0934a3f5829b94ed9a45ca25537d89bf907ccb`.
- Complete 104-witness digest (canonical compact sorted-key JSON):
  `2dfa073cacd7b673bb2daadc8cc1b52254ce643b205904d7dc8dc306945545d1`.

## Validation and limitations

The code verifies closed face incidences, connected vertex links and Euler
characteristic 2 in the tested intermediates. These are finite checks
on this explicit simplicial-complex model, not a formal bridge to every
`ClosedTriangulationCore` Lean hypothesis or a mechanically checked theorem
about homeomorphism to `S³`. The identification of U(16) as a combinatorial
3-sphere is taken from the published construction.

The computation **does not** produce strict `PhiSupport` descent. In a
representative depth-2 case the final complex has 108 tetrahedra and 17
vertices, giving `PhiSupport = 4(108 - 17) = 364`, versus 352 initially.
The `PhiSupport` values use the closed-core counting formula, subject to
the intended combinatorial interpretation.

No `sorry`, `axiom`, or `native_decide` is introduced; no Lean code is
modified in this PR. The Python proof status is **COMPUTATION_PASS**, while
`LEAN_VERIFIED := NOT_RUN` and `GLOBAL_POINCARE := OPEN`.

## Literature

Dougherty, Faber and Murphy, *Unflippable triangulations of the 3-sphere*,
Discrete & Computational Geometry 32 (2004), 309–315; also the description
of seven cyclic generators in Bagchi–Datta, arXiv:1208.1389, Example 3.1(b).
