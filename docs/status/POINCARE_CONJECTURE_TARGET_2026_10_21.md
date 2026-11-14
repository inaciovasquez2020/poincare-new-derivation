# Unconditional Poincare target statement

**Status:** target formalized; unconditional proof remains open.
**Date:** 2026-10-21

lean/Poincare/PoincareConjectureTarget.lean now states the unconditional repository-level target as PoincareConjectureTarget. Unlike the existing conditional theorem, the target has no global-descent argument in its assumptions.

The file also proves the straightforward reduction from SimplyConnectedGlobalPhiSupportDescent to this target using the existing conditional theorem. It does not assert that the descent proposition has been proved.

This is intentionally not an axiom and contains no admitted proof. It makes the desired theorem explicit and type-checkable as a proposition while keeping the proof obligation visible. A named target proposition is not itself evidence that the conjecture is true.

The actual missing mathematical result remains a proof of PoincareConjectureTarget, or an independently proved theorem implying it. The equivalence in GlobalDescentEquivalence.lean shows that the current global-descent route still requires universal normalized-representative existence; this file does not disguise that dependency.