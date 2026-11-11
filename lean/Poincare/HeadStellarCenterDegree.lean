import Poincare.HeadStellarSimpleCore

namespace Poincare

/-- With a center fresh in the exterior, a literal head 1→4 subdivision
gives that center degree exactly four without assuming a closed core. -/
theorem Move41Site.headStellar_center_vertexDegree
    (s : Move41Site) (rest : List Tet)
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    vertexDegree (s.headStellar rest) s.e = 4 := by
  have hrest : (rest.flatMap Tet.verts).count s.e = 0 := by
    induction rest with
    | nil => simp
    | cons τ tail ih =>
      have hτ : s.e ∉ τ.verts := hfresh τ (by simp)
      have htail : ∀ ρ ∈ tail, s.e ∉ ρ.verts := by
        intro ρ hρ
        exact hfresh ρ (by simp [hρ])
      have hzero := ih htail
      have hτzero : τ.verts.count s.e = 0 := (List.count_eq_zero).2 hτ
      simpa [List.flatMap_cons, List.count_append, hτzero] using hzero
  have hd := s.distinct
  simp [List.nodup_cons] at hd
  simp [vertexDegree, allVerts, Move41Site.headStellar,
    Move41Site.sourceTet₀, Move41Site.sourceTet₁,
    Move41Site.sourceTet₂, Move41Site.sourceTet₃,
    Tet.verts, List.count_append, hrest]
  aesop

/-- The newly inserted stellar center contributes zero to the
degree-four defect functional. -/
theorem Move41Site.headStellar_center_vertexDefect
    (s : Move41Site) (rest : List Tet)
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    vertexDefect (s.headStellar rest) s.e = 0 := by
  simp [vertexDefect, targetDegree,
    s.headStellar_center_vertexDegree rest hfresh]

end Poincare
