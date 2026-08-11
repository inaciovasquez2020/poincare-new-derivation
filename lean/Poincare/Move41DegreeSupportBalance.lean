import Poincare.Move41GeometricCarrierHomeomorph
import Poincare.VertexIncidenceCounting

namespace Poincare

/-- The center of a genuine legal `4 → 1` site is incident to exactly the
four source tetrahedra. -/
theorem ClosedTriangulationCore.move41Site_center_vertexDegree_eq_four
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    vertexDegree K s.e = 4 := by
  classical
  let p₀ : Tet → Bool := fun τ ↦ sameTetVerticesBool τ s.sourceTet₀
  let p₁ : Tet → Bool := fun τ ↦ sameTetVerticesBool τ s.sourceTet₁
  let p₂ : Tet → Bool := fun τ ↦ sameTetVerticesBool τ s.sourceTet₂
  let p₃ : Tet → Bool := fun τ ↦ sameTetVerticesBool τ s.sourceTet₃
  have hpartition :
      (K.tets.filter (fun τ ↦ s.e ∈ τ.verts)).length =
        (K.tets.filter p₀).length + (K.tets.filter p₁).length +
          (K.tets.filter p₂).length + (K.tets.filter p₃).length := by
    have hpair := hlegal.sourcePairwiseDistinct
    simp [Move41Site.sourceTets] at hpair
    have hnotOther {u v : Tet} (huv : ¬ SameTetVertices u v)
        {tau : Tet} (htu : SameTetVertices tau u) :
        ¬ SameTetVertices tau v := by
      intro htv
      exact huv (sameTetVertices_trans (sameTetVertices_symm htu) htv)
    have aux (L : List Tet) (hLK : ∀ ρ ∈ L, ρ ∈ K.tets) :
        (L.filter (fun τ ↦ s.e ∈ τ.verts)).length =
          (L.filter p₀).length + (L.filter p₁).length +
            (L.filter p₂).length + (L.filter p₃).length := by
      induction L with
      | nil => simp
      | cons τ L ih =>
        have hτK : τ ∈ K.tets := hLK τ (by simp)
        have htail : ∀ ρ ∈ L, ρ ∈ K.tets := by
          intro ρ hρ
          exact hLK ρ (by simp [hρ])
        have ih' := ih htail
        simp only [p₀, p₁, p₂, p₃] at ih'
        by_cases he : s.e ∈ τ.verts
        · rcases (hlegal.centerSaturated τ hτK he) with ⟨source, hs, hsame⟩
          simp [Move41Site.sourceTets] at hs
          rcases hs with rfl | rfl | rfl | rfl
          · have h1 := hnotOther hpair.1.1 hsame
            have h2 := hnotOther hpair.1.2.1 hsame
            have h3 := hnotOther hpair.1.2.2 hsame
            simp only [List.filter_cons]
            simp [he, p₀, p₁, p₂, p₃, sameTetVerticesBool_eq_true_iff,
              hsame, h1, h2, h3]
            omega
          · have h0 := hnotOther (fun h ↦ hpair.1.1 (sameTetVertices_symm h)) hsame
            have h2 := hnotOther hpair.2.1.1 hsame
            have h3 := hnotOther hpair.2.1.2 hsame
            simp only [List.filter_cons]
            simp [he, p₀, p₁, p₂, p₃, sameTetVerticesBool_eq_true_iff,
              hsame, h0, h2, h3]
            omega
          · have h0 := hnotOther (fun h ↦ hpair.1.2.1 (sameTetVertices_symm h)) hsame
            have h1 := hnotOther (fun h ↦ hpair.2.1.1 (sameTetVertices_symm h)) hsame
            have h3 := hnotOther hpair.2.2 hsame
            simp only [List.filter_cons]
            simp [he, p₀, p₁, p₂, p₃, sameTetVerticesBool_eq_true_iff,
              hsame, h0, h1, h3]
            omega
          · have h0 := hnotOther (fun h ↦ hpair.1.2.2 (sameTetVertices_symm h)) hsame
            have h1 := hnotOther (fun h ↦ hpair.2.1.2 (sameTetVertices_symm h)) hsame
            have h2 := hnotOther (fun h ↦ hpair.2.2 (sameTetVertices_symm h)) hsame
            simp only [List.filter_cons]
            simp [he, p₀, p₁, p₂, p₃, sameTetVerticesBool_eq_true_iff,
              hsame, h0, h1, h2]
            omega
        · have hn (source : Tet) (hs : source ∈ s.sourceTets) :
              ¬ SameTetVertices τ source := by
            intro hsame
            apply he
            exact (hsame s.e).2 (by
              simp [Move41Site.sourceTets] at hs
              rcases hs with rfl | rfl | rfl | rfl <;>
                simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
                  Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts])
          simp only [List.filter_cons]
          simp [he, p₀, p₁, p₂, p₃, sameTetVerticesBool_eq_true_iff,
            hn s.sourceTet₀ (by simp [Move41Site.sourceTets]),
            hn s.sourceTet₁ (by simp [Move41Site.sourceTets]),
            hn s.sourceTet₂ (by simp [Move41Site.sourceTets]),
            hn s.sourceTet₃ (by simp [Move41Site.sourceTets])]
          exact ih'
    exact aux K.tets (fun _ h ↦ h)
  rw [hcore.vertexDegree_eq_incidentTetCount, hpartition]
  have h₀ : (K.tets.filter p₀).length = 1 := by
    simpa [p₀] using
      hlegal.sourceOccursExactlyOnce s.sourceTet₀ (by simp [Move41Site.sourceTets])
  have h₁ : (K.tets.filter p₁).length = 1 := by
    simpa [p₁] using
      hlegal.sourceOccursExactlyOnce s.sourceTet₁ (by simp [Move41Site.sourceTets])
  have h₂ : (K.tets.filter p₂).length = 1 := by
    simpa [p₂] using
      hlegal.sourceOccursExactlyOnce s.sourceTet₂ (by simp [Move41Site.sourceTets])
  have h₃ : (K.tets.filter p₃).length = 1 := by
    simpa [p₃] using
      hlegal.sourceOccursExactlyOnce s.sourceTet₃ (by simp [Move41Site.sourceTets])
  omega

end Poincare
