import Poincare.FacePairingPillow
import Mathlib.Logic.Equiv.Basic

namespace Poincare

/-!
A first local combinatorial template for the `2→3` step used in
Pachner factorization.

The source uses the single shared face ABC of tetrahedra ABCD/ABCE.
The target uses internal faces ADE, BDE, CDE of ABDE/ACDE/BCDE.
Outer-face pairing, compatibility with an enclosing triangulation,
the paper's arrow-selected site, and local move legality remain OPEN.
-/

/-- The source and target *interior* face identifications of the
standard local `2→3` replacement.

Tetrahedron occurrences are numbered 0,1 (source) and 0,1,2 (target).
The target's second gluing exchanges local positions 0 and 1.
This is a local template, not a move operation on arbitrary face pairings. -/
def standardLocal23InteriorPairings : FacePairingData 2 × FacePairingData 3 :=
  (
    { identifications := [
        {
          source := { occurrence := 0, opposite := 3 }
          target := { occurrence := 1, opposite := 3 }
          localVertexMap := Equiv.refl (Fin 4)
          opposite_compatible := rfl
        }
      ]
    },
    { identifications := [
        {
          source := { occurrence := 0, opposite := 1 }
          target := { occurrence := 1, opposite := 1 }
          localVertexMap := Equiv.refl (Fin 4)
          opposite_compatible := rfl
        },
        {
          source := { occurrence := 0, opposite := 0 }
          target := { occurrence := 2, opposite := 1 }
          localVertexMap := Equiv.swap (0 : Fin 4) 1
          opposite_compatible := by decide
        },
        {
          source := { occurrence := 1, opposite := 0 }
          target := { occurrence := 2, opposite := 0 }
          localVertexMap := Equiv.refl (Fin 4)
          opposite_compatible := rfl
        }
      ]
    }
  )


/-- Both local interiors use each occurrence-face at most once. This is a
combinatorial necessary condition, not a proof of `2→3` legality in a
surrounding face-paired triangulation. -/
theorem standardLocal23InteriorPairings_noRepeatedFace :
    standardLocal23InteriorPairings.1.NoRepeatedFace ∧
    standardLocal23InteriorPairings.2.NoRepeatedFace := by
  constructor
  · change
      ([(⟨0, 3⟩ : PairedFace 2), ⟨1, 3⟩] : List (PairedFace 2)).Nodup
    decide
  · change
      ([
        (⟨0, 1⟩ : PairedFace 3),
        ⟨1, 1⟩,
        ⟨0, 0⟩,
        ⟨2, 1⟩,
        ⟨1, 0⟩,
        ⟨2, 0⟩
      ] : List (PairedFace 3)).Nodup
    decide

end Poincare
