import Poincare.Triangulation

namespace Poincare

/--
Formalization audit: the current `S3` predicate does not characterize a
(nonempty) tetrahedral 3-manifold.

The one-tetrahedron object below has all four tetrahedron slots equal to the
same vertex. Hence that vertex occurs exactly four times, so the current
defect functional is zero and the repository's current `S3` predicate is
true. This object is not a valid simplicial tetrahedron.

Therefore the present `Triangulation` structure and `S3` predicate are
strictly weaker than the intended topological sphere-recognition statement.
-/
def degenerateOneTet : Triangulation :=
  { tets := [{ v0 := 0, v1 := 0, v2 := 0, v3 := 0 }] }

theorem degenerateOneTet_is_S3 :
    S3 degenerateOneTet := by
  rfl

theorem S3_does_not_imply_nonempty_valid_tetrahedral_model :
    ∃ K : Triangulation, S3 K ∧ K.tets.length = 1 := by
  exact ⟨degenerateOneTet, degenerateOneTet_is_S3, rfl⟩

end Poincare
