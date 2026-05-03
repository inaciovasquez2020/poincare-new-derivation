# PND-D3EL Coupled Discharge Frontier

## Status

OPEN_FRONTIER.

## Terminal Invariant

PND-D3EL is equivalent to the coupled discharge of the following five primitives:

1. `PLManifoldLike`
2. `ExposedFeatures`
3. `LocalDegree`
4. `MoveAdmissible`
5. `BarrierHeight`

These primitives are jointly blocking. They cannot be discharged independently.

## Closed Components

The following components are already structurally closed or harmless:

- `local_classification` as previously written is vacuous, because `LocalCase` is inhabited by construction.
- `inadmissible_case` is closeable if `Admissible` excludes the forbidden constructor by definition.
- `PND-CDT-1` is usable once `beta` is Nat-valued or otherwise well-founded.
- The architecture is coherent as a conditional proof skeleton.

## Open Components

The following components remain open:

- `exposure_case`, blocked on `ExposedFeatures` and `LocalDegree`.
- `descent_case`, blocked on `MoveAdmissible` and `BarrierHeight`.
- `local_classification_nontrivial`, which is exactly PND-D3EL.
- `PND-D3EL`.
- The independent terminal-exposure bridge.

## Coupled Discharge Lemma

The remaining required theorem is:

```lean
lemma pnd_d3el_coupled_discharge
    (S : State)
    (hA : Admissible S)
    (hN : Nonterminal S) :
    HasDegreeThreeExposure S ∨
    ∃ S' : State, Step S S' ∧ beta S' < beta S
Boundary
This document does not prove PND-D3EL.
This document does not define the five missing primitives.
This document does not prove the Poincare conjecture.
This document does not assert unconditional theorem-level closure.
This document does not promote repository build success to mathematical proof.
Build success verifies artifact integrity only.
Fixed Point
No further progress is possible without new input defining the five primitives and proving their joint discharge.
