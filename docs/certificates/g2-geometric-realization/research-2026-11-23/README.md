# G2 disk/chain research checkpoint — 2026-11-23

Research-only material. Do not import the Lean candidates into the production
Lean entrypoint: they are **NOT_RUN** and have no successful axiom audit. The
existing geometric witness-free archive has its own **historical** compiler
receipt, which must not be relabeled as fresh verification. Mathematical
proofs in the markdown files are independent paper-level results.

## Included materials

* `G2_Geometric_Disk_Integration_Audit_2026-11-23.md` — inspection of the
  geometric realization, correct incidence subdivision and OPEN Lean bridge.
* `G2_Canonical_Cycle_Filling_2026-11-23.md` — proof of unique integral 1-cycle
  filling in the subdivided cyclic cone.
* `G2_General_Graph_Cone_Cycle_Filling_2026-11-23.md` — stronger proof for the
  cone on **any finite simple graph** over any abelian coefficient group.
* `g2_canonical_filling_verify.py` — original finite integral tests.
* `g2_general_cone_filling_verify.py` — all small graphs and all F2 1-chains;
  independent randomized seeded exact-integer adversarial tests.
* `G2SubdividedConeCandidate.lean` — tagged incidence-cone combinatorial
  candidate, compilation **NOT_RUN**.
* `G2_FlagFaceProjection_Candidate_2026-11-23.lean` — separate face-projection
  lemma snippet to append to a temporary *copy* of the existing 3,950-line
  geometric certificate; the proposed `rfl` is **NOT_RUN**.

## Boundaries

- No G2 disk homeomorphism was compiled in this checkpoint.
- The graph-cone filling theorem is **not** a manifold disk theorem for
  arbitrary graphs.
- The global Poincare derivation remains OPEN.
- No changes to production imports, package pins, build caches or existing
  Git files are part of this research bundle.

## Source identifiers

Published source branch: `work/first-nonzero-reentry-20261027`.

* `lean/Poincare/PR199G2VerifiedConeComplex.lean` blob
  `ef91ca5df95415f4d617bd64a7aa31afed626aad`
* `docs/certificates/g2-geometric-realization/G2WitnessFreeAffineVerified.lean`
  blob `b198a04ea9b11733064e82ef16fcb9861f99a8ff`
* The archived receipt reports prior Lean 4.30.0-rc1 PASS and axioms PASS
  for the standalone geometric witness-free certificate, but explicitly
  leaves the geometric disk-homeomorphism theorem OPEN.
* Last reported Mac HEAD `570f125477cbd89e25055cbbd917bed5a2aa9ef1`,
  branch `proof/tksv-local-descent`, with two untracked `.DS_Store` files.
  That local-only state has not been re-inspected or modified by this work.

## Verification receipt

Executed in the independent assistant container on 2026-11-23:

```
python3 -B g2_canonical_filling_verify.py
RESULT := COMPUTATION_PASS
EXACT_INTEGER_CHECKS := 7304

python3 -B g2_general_cone_filling_verify.py
RESULT := COMPUTATION_PASS
GRAPH_CASES := 76
F2_CHAIN_EXHAUSTIVE_CHECKS := 11895
Z_INTEGER_PAIRS := 8400
TOTAL_CHAIN_CHECKS := 28695
CYCLE_INVERSE_CHECKS := 9161
```

All verification results are finite; the universal filling theorem follows
from the independent algebraic proof. Lean := NOT_RUN for new candidates.

## SHA-256 (bundle files, excludes this README)

`e17eeff0d34736cc329ed1b7cf6f479ebf4af6679d044aa74486b35c199dbb0b`  `G2SubdividedConeCandidate.lean`
`7db46ba90948bddd7f928b040ce963f30eb99b5ac0c84d859a2c9be552490545`  `G2_Canonical_Cycle_Filling_2026-11-23.md`
`ac77942bf502ba97babf6d3e711e3fd630ce911ab75e4dba1a9f50a408f2bc27`  `G2_FlagFaceProjection_Candidate_2026-11-23.lean`
`4d93a25589b29b0dfa1c03a5544a0db721bf4d8dd70026f1e8e9039d73224c3f`  `G2_General_Graph_Cone_Cycle_Filling_2026-11-23.md`
`91794b310ef47bb9b471ab2a0df3d1f3f2ffc5f5dd943e20cb8ea89befb17e4f`  `G2_Geometric_Disk_Integration_Audit_2026-11-23.md`
`ebcd11b3e6ee278054b60d3cb8fc090c21582d7c456c55cbea6f636a0776d0e7`  `g2_canonical_filling_verify.py`
`232204ec4acd865c63668f16f73a04a5fa73157ebd2c6b509b31b778ca4c4906`  `g2_general_cone_filling_verify.py`
