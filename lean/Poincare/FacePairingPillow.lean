import Mathlib.Logic.Equiv.Defs
import Poincare.Triangulation

namespace Poincare

/-!
A bounded data model for face-paired tetrahedron *occurrences*.

This does not assert manifoldness, a 2-to-0 move, or the four-move
factorization. In particular, unlike a vertex-set simplicial complex,
two distinct tetrahedron occurrences may be paired on two different faces.
-/

/-- A face is identified by an occurrence and the opposite local vertex. -/
structure PairedFace (n : Nat) where
  occurrence : Fin n
  opposite : Fin 4
  deriving DecidableEq, Repr

/-- A directed description of a face identification, with a bijection of
local vertex positions which carries the opposite vertex to the opposite
vertex. This record is used once per *unoriented* pairing. -/
structure FaceIdentification (n : Nat) where
  source : PairedFace n
  target : PairedFace n
  localVertexMap : Equiv.Perm (Fin 4)
  opposite_compatible :
    localVertexMap source.opposite = target.opposite

/-- Partial face pairings; faces omitted from the list are boundary faces.
The occurrence index is independent of vertex labels. -/
structure FacePairingData (n : Nat) where
  identifications : List (FaceIdentification n)

/-- No face occurrence is listed in two identifications. -/
def FacePairingData.NoRepeatedFace {n : Nat} (K : FacePairingData n) : Prop :=
  (K.identifications.flatMap (fun g => [g.source, g.target])).Nodup

/-- The two distinct face-pairings of a two-tetrahedron pillow, with
identity maps of local vertex positions on both paired faces. -/
def pillowPairingZero : FaceIdentification 2 where
  source := { occurrence := 0, opposite := 0 }
  target := { occurrence := 1, opposite := 0 }
  localVertexMap := Equiv.refl (Fin 4)
  opposite_compatible := rfl

def pillowPairingOne : FaceIdentification 2 where
  source := { occurrence := 0, opposite := 1 }
  target := { occurrence := 1, opposite := 1 }
  localVertexMap := Equiv.refl (Fin 4)
  opposite_compatible := rfl

def twoFacePillow : FacePairingData 2 where
  identifications := [pillowPairingZero, pillowPairingOne]

theorem twoFacePillow_has_two_identifications :
    twoFacePillow.identifications.length = 2 := by
  decide

theorem twoFacePillow_distinct_occurrences_and_faces :
    pillowPairingZero.source.occurrence ≠ pillowPairingZero.target.occurrence ∧
    pillowPairingZero.source.occurrence = pillowPairingOne.source.occurrence ∧
    pillowPairingZero.target.occurrence = pillowPairingOne.target.occurrence ∧
    pillowPairingZero.source.opposite ≠ pillowPairingOne.source.opposite ∧
    pillowPairingZero.target.opposite ≠ pillowPairingOne.target.opposite := by
  decide

theorem twoFacePillow_no_repeated_face :
    twoFacePillow.NoRepeatedFace := by
  decide

end Poincare
