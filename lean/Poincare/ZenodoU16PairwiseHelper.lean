import Poincare.ZenodoU16FirstHighFan

namespace Poincare

/-- Isolated two-tetrahedron distinction using a concrete separating vertex. -/
theorem zenodoU16_firstPair_ne :
    ¬ SameTetVertices (⟨1, 2, 3, 6⟩ : Tet) (⟨1, 2, 3, 9⟩ : Tet) := by
  intro h
  have h6 : 6 ∈ (⟨1, 2, 3, 9⟩ : Tet).verts :=
    (h 6).mp (by decide)
  exact (by decide : 6 ∉ (⟨1, 2, 3, 9⟩ : Tet).verts) h6

/-- A bounded comparison of two tetrahedra by their four vertex slots.
A separating vertex certifies nonidentity of the represented vertex sets. -/
theorem tet_not_same_of_separating_vertex
    (tau sigma : Tet) (v : Nat)
    (hmem : v ∈ tau.verts) (hnot : v ∉ sigma.verts) :
    ¬ SameTetVertices tau sigma := by
  intro h
  exact hnot ((h v).mp hmem)

/-- The first three U(16) tetrahedra have pairwise distinct vertex sets,
checked by three explicit bounded separating vertices. -/
theorem zenodoU16_firstThree_pairwise :
    ([⟨1, 2, 3, 6⟩, ⟨1, 2, 3, 9⟩, ⟨1, 2, 5, 10⟩] : List Tet).Pairwise
      (fun tau sigma => ¬ SameTetVertices tau sigma) := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq, List.pairwise_singleton]
  constructor
  · exact tet_not_same_of_separating_vertex
      ⟨1, 2, 3, 6⟩ ⟨1, 2, 3, 9⟩ 6 (by decide) (by decide)
  constructor
  · exact tet_not_same_of_separating_vertex
      ⟨1, 2, 3, 6⟩ ⟨1, 2, 5, 10⟩ 6 (by decide) (by decide)
  · exact tet_not_same_of_separating_vertex
      ⟨1, 2, 3, 9⟩ ⟨1, 2, 5, 10⟩ 9 (by decide) (by decide)

end Poincare
