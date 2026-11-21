# Fan-only fail-closed recurrence checkpoint

Status: LEAN_VERIFIED

Repository base: 02637eb1ac9ace4ea525a21b25f4591ade694839

Toolchain: repository-pinned Lean toolchain.

Verified declarations:
- exists_highFanStep_of_noMove23_noDescent
- exists_perpetual_highFanStep_of_noMove23_noDescent
- exists_recurrent_highFanStep_of_noMove23_noDescent

Allowed axioms:
- propext
- Classical.choice
- Quot.sound

Validation: module build, independent import, strict axiom audit.

Mathematical boundary:
Finite high-fan recurrence does not exclude cycles.

GLOBAL_CYCLIC_RIGIDITY := OPEN
GLOBAL_POINCARE := OPEN
