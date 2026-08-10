import Poincare.CrossPolytopeBoundary

namespace Poincare

/-- A canonical low-label `2-3` site in the four-dimensional cross-polytope boundary. -/
def crossPolytopeEscapeMove23 : Move23Site where
  a := 0
  b := 2
  c := 4
  d := 6
  e := 7
  distinct := by decide

/-- The first, non-inverse, `3-2` site in the escape block. -/
def crossPolytopeEscapeMove32₁ : Move32Site where
  a := 1
  b := 6
  c := 7
  d := 2
  e := 4

/-- The second `3-2` site in the escape block. -/
def crossPolytopeEscapeMove32₂ : Move32Site where
  a := 3
  b := 6
  c := 7
  d := 0
  e := 4

def crossPolytopeEscapeAfter23 : Triangulation :=
  crossPolytopeEscapeMove23.replace crossPolytopeBoundary4

def crossPolytopeEscapeAfter32₁ : Triangulation :=
  crossPolytopeEscapeMove32₁.replace crossPolytopeEscapeAfter23

def crossPolytopeEscapeFinal : Triangulation :=
  crossPolytopeEscapeMove32₂.replace crossPolytopeEscapeAfter32₁

theorem crossPolytopeEscapeAfter23_tets :
    crossPolytopeEscapeAfter23.tets =
      [⟨0, 2, 6, 7⟩, ⟨0, 4, 6, 7⟩, ⟨2, 4, 6, 7⟩,
       ⟨0, 2, 5, 6⟩, ⟨0, 2, 5, 7⟩, ⟨0, 3, 4, 6⟩,
       ⟨0, 3, 4, 7⟩, ⟨0, 3, 5, 6⟩, ⟨0, 3, 5, 7⟩,
       ⟨1, 2, 4, 6⟩, ⟨1, 2, 4, 7⟩, ⟨1, 2, 5, 6⟩,
       ⟨1, 2, 5, 7⟩, ⟨1, 3, 4, 6⟩, ⟨1, 3, 4, 7⟩,
       ⟨1, 3, 5, 6⟩, ⟨1, 3, 5, 7⟩] := by
  rfl

theorem crossPolytopeEscapeAfter32₁_tets :
    crossPolytopeEscapeAfter32₁.tets =
      [⟨1, 6, 7, 2⟩, ⟨1, 6, 7, 4⟩, ⟨0, 2, 6, 7⟩,
       ⟨0, 4, 6, 7⟩, ⟨0, 2, 5, 6⟩, ⟨0, 2, 5, 7⟩,
       ⟨0, 3, 4, 6⟩, ⟨0, 3, 4, 7⟩, ⟨0, 3, 5, 6⟩,
       ⟨0, 3, 5, 7⟩, ⟨1, 2, 5, 6⟩, ⟨1, 2, 5, 7⟩,
       ⟨1, 3, 4, 6⟩, ⟨1, 3, 4, 7⟩, ⟨1, 3, 5, 6⟩,
       ⟨1, 3, 5, 7⟩] := by
  rfl

theorem crossPolytopeEscapeMove23_legal :
    crossPolytopeEscapeMove23.LegalIn crossPolytopeBoundary4 := by
  norm_num [Move23Site.LegalIn, Move23Site.RealizedIn,
    Move23Site.SharedFaceExactlyTwo, Move23Site.NewEdgeAbsent,
    crossPolytopeEscapeMove23, crossPolytopeBoundary4, SameTetVertices,
    Move23Site.leftTet, Move23Site.rightTet, Tet.verts]

theorem crossPolytopeEscapeMove32₁_legal :
    crossPolytopeEscapeMove32₁.LegalIn crossPolytopeEscapeAfter23 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨⟨1, 2, 4, 6⟩,
      by rw [crossPolytopeEscapeAfter23_tets]; simp,
      by intro v; simp [crossPolytopeEscapeMove32₁,
        Move32Site.targetTet₀, Tet.verts]; aesop⟩,
      ⟨⟨1, 2, 4, 7⟩,
        by rw [crossPolytopeEscapeAfter23_tets]; simp,
        by intro v; simp [crossPolytopeEscapeMove32₁,
          Move32Site.targetTet₁, Tet.verts]; aesop⟩,
      ⟨⟨2, 4, 6, 7⟩,
        by rw [crossPolytopeEscapeAfter23_tets]; simp,
        by intro v; simp [crossPolytopeEscapeMove32₁,
          Move32Site.targetTet₂, Tet.verts]; aesop⟩⟩
  · norm_num [Move32Site.SharedEdgeExactlyThree,
      crossPolytopeEscapeAfter23_tets, crossPolytopeEscapeMove32₁, Tet.verts]
  · norm_num [Move32Site.SourceFaceAbsent,
      crossPolytopeEscapeAfter23_tets, crossPolytopeEscapeMove32₁, Tet.verts]

theorem crossPolytopeEscapeMove32₂_legal :
    crossPolytopeEscapeMove32₂.LegalIn crossPolytopeEscapeAfter32₁ := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨⟨0, 3, 4, 6⟩,
      by rw [crossPolytopeEscapeAfter32₁_tets]; simp,
      by intro v; simp [crossPolytopeEscapeMove32₂,
        Move32Site.targetTet₀, Tet.verts]; aesop⟩,
      ⟨⟨0, 3, 4, 7⟩,
        by rw [crossPolytopeEscapeAfter32₁_tets]; simp,
        by intro v; simp [crossPolytopeEscapeMove32₂,
          Move32Site.targetTet₁, Tet.verts]; aesop⟩,
      ⟨⟨0, 4, 6, 7⟩,
        by rw [crossPolytopeEscapeAfter32₁_tets]; simp,
        by intro v; simp [crossPolytopeEscapeMove32₂,
          Move32Site.targetTet₂, Tet.verts]; aesop⟩⟩
  · norm_num [Move32Site.SharedEdgeExactlyThree,
      crossPolytopeEscapeAfter32₁_tets, crossPolytopeEscapeMove32₂, Tet.verts]
  · norm_num [Move32Site.SourceFaceAbsent,
      crossPolytopeEscapeAfter32₁_tets, crossPolytopeEscapeMove32₂, Tet.verts]

theorem crossPolytopeEscapeMove32₁_ne_canonicalReverse :
    crossPolytopeEscapeMove32₁ ≠
      Move32Site.ofMove23Site crossPolytopeEscapeMove23 := by
  intro h
  have ha := congrArg Move32Site.a h
  norm_num [crossPolytopeEscapeMove32₁, Move32Site.ofMove23Site,
    crossPolytopeEscapeMove23] at ha

theorem crossPolytopeEscapeAfter23_PhiSupport :
    PhiSupport crossPolytopeEscapeAfter23 = 36 := by
  decide

theorem crossPolytopeEscapeAfter32₁_PhiSupport :
    PhiSupport crossPolytopeEscapeAfter32₁ = 32 := by
  decide

theorem crossPolytopeEscapeFinal_PhiSupport :
    PhiSupport crossPolytopeEscapeFinal = 28 := by
  decide

theorem crossPolytopeEscapeInitial_PhiSupport :
    PhiSupport crossPolytopeBoundary4 = 32 := by
  decide

theorem crossPolytopeBoundary4_exists_move2332_block_strict_descent :
    ∃ K' : Triangulation,
      K' = crossPolytopeEscapeMove32₂.replace
        (crossPolytopeEscapeMove32₁.replace
          (crossPolytopeEscapeMove23.replace crossPolytopeBoundary4)) ∧
      PhiSupport K' < PhiSupport crossPolytopeBoundary4 := by
  refine ⟨crossPolytopeEscapeFinal, rfl, ?_⟩
  rw [crossPolytopeEscapeFinal_PhiSupport, crossPolytopeEscapeInitial_PhiSupport]
  decide

end Poincare
