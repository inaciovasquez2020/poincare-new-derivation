import Poincare.FacePairingEdgeEquivalence

namespace Poincare

/-!
A complete two-tetrahedron face-pairing fixture extending the recorded
two-face pillow. Each of the four local faces of tetrahedron occurrence 0
is identified with the corresponding local face of occurrence 1 by the
identity permutation.

The explicit arrow frame below has axis edge 0-1 and equator edge 2-3.
This fixture is NOT claimed to realize SnapPy's legal first 2→3 move.
-/

def doublePillowPairingTwo : FaceIdentification 2 where
  source := { occurrence := 0, opposite := 2 }
  target := { occurrence := 1, opposite := 2 }
  localVertexMap := Equiv.refl (Fin 4)
  opposite_compatible := rfl

def doublePillowPairingThree : FaceIdentification 2 where
  source := { occurrence := 0, opposite := 3 }
  target := { occurrence := 1, opposite := 3 }
  localVertexMap := Equiv.refl (Fin 4)
  opposite_compatible := rfl

/-- All eight faces are paired, with the two old pillow face gluings
unchanged. -/
def completeDoublePillow : FacePairingData 2 where
  identifications :=
    [pillowPairingZero, pillowPairingOne,
     doublePillowPairingTwo, doublePillowPairingThree]

theorem completeDoublePillow_extends_pillow :
    completeDoublePillow.identifications.take 2 =
      twoFacePillow.identifications := by
  rfl

theorem completeDoublePillow_no_repeated_face :
    completeDoublePillow.NoRepeatedFace := by
  change
    ([
      (⟨0, 0⟩ : PairedFace 2), ⟨1, 0⟩,
      ⟨0, 1⟩, ⟨1, 1⟩,
      ⟨0, 2⟩, ⟨1, 2⟩,
      ⟨0, 3⟩, ⟨1, 3⟩
    ] : List (PairedFace 2)).Nodup
  decide

theorem completeDoublePillow_all_faces_paired :
    ∀ f : PairedFace 2,
      f ∈ (completeDoublePillow.identifications.flatMap
        (fun g => [g.source, g.target])) := by
  decide

/-- An arrow frame: its axis is the local edge first-second; the face
is specified by its opposite vertex and must contain that axis. -/
structure FacePairingArrow (n : Nat) where
  occurrence : Fin n
  first : Fin 4
  second : Fin 4
  faceOpposite : Fin 4
  endpoints_ne : first ≠ second
  first_in_face : first ≠ faceOpposite
  second_in_face : second ≠ faceOpposite

/-- A selected frame with axis (0,1), equator (2,3), face opposite 2. -/
def doublePillowSelectedArrow : FacePairingArrow 2 where
  occurrence := 0
  first := 0
  second := 1
  faceOpposite := 2
  endpoints_ne := by decide
  first_in_face := by decide
  second_in_face := by decide

end Poincare
