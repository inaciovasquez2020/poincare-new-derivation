import Poincare.FacePairingLocalMove23

namespace Poincare

/-!
Six exterior boundary-face correspondences for the *local* two-to-three
bipyramid replacement. The five vertex labels are a=0, b=1, c=2, d=3, e=4.
The old tetrahedra are abcd and abce; the new ones are abde, acde, bcde.

This module makes no claim about a surrounding face-paired 3-manifold,
the four-move 2→0 factorization, or a SnapPy arrow frame.
-/

private def local23SourceTet (i : Fin 2) : Tet :=
  if i = 0 then ⟨0, 1, 2, 3⟩ else ⟨0, 1, 2, 4⟩

private def local23TargetTet (i : Fin 3) : Tet :=
  if i = 0 then ⟨0, 1, 3, 4⟩
  else if i = 1 then ⟨0, 2, 3, 4⟩
  else ⟨1, 2, 3, 4⟩

/-- The three vertices of a tetrahedron face, listed in increasing
local-position order, where the opposite position is omitted. -/
private def local23FaceVertices (t : Tet) (opp : Fin 4) : List Nat :=
  if opp = 0 then [t.v1, t.v2, t.v3]
  else if opp = 1 then [t.v0, t.v2, t.v3]
  else if opp = 2 then [t.v0, t.v1, t.v3]
  else [t.v0, t.v1, t.v2]

/-- Complete six-face boundary interface from the two old occurrences to
the three new ones; each pair has the same three global vertex labels.

Old face -> new face:
  (0,0)->(2,3) BCD; (0,1)->(1,3) ACD; (0,2)->(0,3) ABD;
  (1,0)->(2,2) BCE; (1,1)->(1,2) ACE; (1,2)->(0,2) ABE.
-/
def standardLocal23BoundaryFaces : List (PairedFace 2 × PairedFace 3) :=
  [
    (⟨0, 0⟩, ⟨2, 3⟩),
    (⟨0, 1⟩, ⟨1, 3⟩),
    (⟨0, 2⟩, ⟨0, 3⟩),
    (⟨1, 0⟩, ⟨2, 2⟩),
    (⟨1, 1⟩, ⟨1, 2⟩),
    (⟨1, 2⟩, ⟨0, 2⟩)
  ]

theorem standardLocal23BoundaryFaces_card :
    standardLocal23BoundaryFaces.length = 6 := by
  decide

/-- No source exterior face or target exterior face appears twice. -/
theorem standardLocal23BoundaryFaces_nodup :
    (standardLocal23BoundaryFaces.map Prod.fst).Nodup ∧
    (standardLocal23BoundaryFaces.map Prod.snd).Nodup := by
  decide

/-- Each boundary-face pair literally carries the same three global labels,
not just the same number of vertices. -/
theorem standardLocal23BoundaryFaces_vertices_agree :
    ∀ p ∈ standardLocal23BoundaryFaces,
      local23FaceVertices (local23SourceTet p.1.occurrence) p.1.opposite =
      local23FaceVertices (local23TargetTet p.2.occurrence) p.2.opposite := by
  decide

end Poincare
