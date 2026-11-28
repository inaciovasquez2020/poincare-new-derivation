# G2 parity bridge research checkpoint — 2026-11-27

**Status:** PROVED_ON_PAPER under explicit hypotheses; five finite verifiers COMPUTATION_PASS; Lean NOT_RUN; actual incidence integration OPEN; GLOBAL_POINCARE OPEN. No novelty or independent-review claim.

Intended repository destination: `docs/certificates/g2_parity_bridge_20261127/` on the draft PR #200 branch `research/g2-radial-chain-decomposition-20261117` at head `36df38d563014164bf288d17448255de4817abb8`. Last user-reported Mac HEAD `ffbd449d21530c1bef49c7b8cfac1cd89b3a2bd5`, branch `work/first-nonzero-reentry-20261027`, with two untracked entries; do not overwrite or discard them. These files are research records, not integrated Lean library modules. The two append-only candidates require the imports and context specified in their headers; the standalone candidate imports Mathlib. None has been compiled here. No dependency pins or build roots should change.

## Contents and dependency order

1. `G2SegmentPartitionBridge.lean`: initial conditional bridge, preserved for provenance; superseded at the paper level.
2. `G2ClosedPrimalWalkCandidate.lean` and `verify_g2_partition.py`: candidate recursive partition reconstruction; exact rational regression (128 walks, 20,800 point checks). The Mac stopped at a missing compiled dependency before checking proofs.
3. `G2_local_potential_gluing.md` and `G2LocalPotentialGluingCandidate.lean`: conditional local-to-global construction; candidate not compiled. Fixture verifier supplies inputs for later scripts.
4. `G2_unified_cocycle_cancellation.md` and `verify_g2_vertex_grid.py`: dimension-independent paper route; finite grid regression only. Compactness and geometric transport are not kernel verified.
5. `G2_obstruction_isomorphism.md` and `verify_g2_obstruction_isomorphism.py`: explicit forward and inverse quotient maps on paper. The original receipt is preserved; the staged script and fresh receipt correct the misleading `local_obstruction_quotient_dimension` field to `residual_local_obstruction_dimension` and separately report `locally_solvable_quotient_dimension`. Numerical results unchanged.
6. `G2_localization_exact_sequence.md` and `verify_g2_localization_rank.py`: exact sequence (no final surjectivity claim) and independently calculated localization rank; 824 basis/generator checks on eight fixtures.

## Reproduction

Python 3 standard library only. Run each `verify_g2_*.py` from this directory; each emits a receipt to stdout. Scripts were rerun in this staged directory with 30-second per-process time limits and all exited successfully. Receipt comparisons ignore elapsed time only. No Lean executable was available. `SHA256SUMS` records the staged byte hashes. Finite evidence does not prove general topology or global descent.

## Remaining gates

- Formalize generic cocycle exactness and transport to the actual carrier and vertex-link incidence types.
- Verify conditional gluing and the concrete incidence transport under the pinned Lean toolchain, followed by allowed-axiom audits.
- Integrate dual parity into the actual reentry witness and prove any remaining descent/termination obligations. PR #199 and #200 remain research drafts; do not promote, merge, or claim global closure.

No repository write, commit, push, or merge has occurred during preparation. CODEX_USED := NO; CLAUDE_USED := NO.
