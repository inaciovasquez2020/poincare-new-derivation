import Poincare.Move41DegreeSupportBalance

namespace Poincare

/--
A saturated four-source Move41 star has center degree exactly four.

Unlike `move41Site_center_vertexDegree_eq_four`, this statement does not
require the opposite target tetrahedron to be absent.  Only the three pieces
of local star data actually used by the degree count are assumed.
-/
theorem ClosedTriangulationCore.move41Site_center_vertexDegree_eq_four_of_local_star
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move41Site)
    (hsourcesExact :
      ∀ source ∈ s.sourceTets,
        (K.tets.filter
          (fun tau => sameTetVerticesBool tau source)).length = 1)
    (hpairwise :
      s.sourceTets.Pairwise
        (fun tau sigma => ¬ SameTetVertices tau sigma))
    (hsaturated :
      ∀ tau ∈ K.tets, s.e ∈ tau.verts →
        ∃ source ∈ s.sourceTets,
          SameTetVertices tau source) :
    vertexDegree K s.e = 4 := by
  classical
  let p₀ : Tet → Bool := fun tau => sameTetVerticesBool tau s.sourceTet₀
  let p₁ : Tet → Bool := fun tau => sameTetVerticesBool tau s.sourceTet₁
  let p₂ : Tet → Bool := fun tau => sameTetVerticesBool tau s.sourceTet₂
  let p₃ : Tet → Bool := fun tau => sameTetVerticesBool tau s.sourceTet₃

  have hpartition :
      (K.tets.filter (fun tau => s.e ∈ tau.verts)).length =
        (K.tets.filter p₀).length +
        (K.tets.filter p₁).length +
        (K.tets.filter p₂).length +
        (K.tets.filter p₃).length := by
    have hpair := hpairwise
    simp [Move41Site.sourceTets] at hpair

    have hnotOther {u v : Tet}
        (huv : ¬ SameTetVertices u v)
        {tau : Tet}
        (htu : SameTetVertices tau u) :
        ¬ SameTetVertices tau v := by
      intro htv
      exact huv
        (sameTetVertices_trans
          (sameTetVertices_symm htu) htv)

    have aux
        (L : List Tet)
        (hLK : ∀ rho ∈ L, rho ∈ K.tets) :
        (L.filter (fun tau => s.e ∈ tau.verts)).length =
          (L.filter p₀).length +
          (L.filter p₁).length +
          (L.filter p₂).length +
          (L.filter p₃).length := by
      induction L with
      | nil =>
          simp
      | cons tau L ih =>
          have htauK : tau ∈ K.tets :=
            hLK tau (by simp)

          have htail : ∀ rho ∈ L, rho ∈ K.tets := by
            intro rho hrho
            exact hLK rho (by simp [hrho])

          have ih' := ih htail
          simp only [p₀, p₁, p₂, p₃] at ih'

          by_cases he : s.e ∈ tau.verts

          · rcases hsaturated tau htauK he with
              ⟨source, hs, hsame⟩

            simp [Move41Site.sourceTets] at hs
            rcases hs with rfl | rfl | rfl | rfl

            · have h1 := hnotOther hpair.1.1 hsame
              have h2 := hnotOther hpair.1.2.1 hsame
              have h3 := hnotOther hpair.1.2.2 hsame
              simp only [List.filter_cons]
              simp [
                he, p₀, p₁, p₂, p₃,
                sameTetVerticesBool_eq_true_iff,
                hsame, h1, h2, h3
              ]
              omega

            · have h0 :=
                hnotOther
                  (fun h =>
                    hpair.1.1
                      (sameTetVertices_symm h))
                  hsame
              have h2 := hnotOther hpair.2.1.1 hsame
              have h3 := hnotOther hpair.2.1.2 hsame
              simp only [List.filter_cons]
              simp [
                he, p₀, p₁, p₂, p₃,
                sameTetVerticesBool_eq_true_iff,
                hsame, h0, h2, h3
              ]
              omega

            · have h0 :=
                hnotOther
                  (fun h =>
                    hpair.1.2.1
                      (sameTetVertices_symm h))
                  hsame
              have h1 :=
                hnotOther
                  (fun h =>
                    hpair.2.1.1
                      (sameTetVertices_symm h))
                  hsame
              have h3 := hnotOther hpair.2.2 hsame
              simp only [List.filter_cons]
              simp [
                he, p₀, p₁, p₂, p₃,
                sameTetVerticesBool_eq_true_iff,
                hsame, h0, h1, h3
              ]
              omega

            · have h0 :=
                hnotOther
                  (fun h =>
                    hpair.1.2.2
                      (sameTetVertices_symm h))
                  hsame
              have h1 :=
                hnotOther
                  (fun h =>
                    hpair.2.1.2
                      (sameTetVertices_symm h))
                  hsame
              have h2 :=
                hnotOther
                  (fun h =>
                    hpair.2.2
                      (sameTetVertices_symm h))
                  hsame
              simp only [List.filter_cons]
              simp [
                he, p₀, p₁, p₂, p₃,
                sameTetVerticesBool_eq_true_iff,
                hsame, h0, h1, h2
              ]
              omega

          · have hn
                (source : Tet)
                (hs : source ∈ s.sourceTets) :
                ¬ SameTetVertices tau source := by
              intro hsame
              apply he
              exact (hsame s.e).2 (by
                simp [Move41Site.sourceTets] at hs
                rcases hs with rfl | rfl | rfl | rfl <;>
                  simp [
                    Move41Site.sourceTet₀,
                    Move41Site.sourceTet₁,
                    Move41Site.sourceTet₂,
                    Move41Site.sourceTet₃,
                    Tet.verts
                  ])

            simp only [List.filter_cons]
            simp [
              he, p₀, p₁, p₂, p₃,
              sameTetVerticesBool_eq_true_iff,
              hn s.sourceTet₀
                (by simp [Move41Site.sourceTets]),
              hn s.sourceTet₁
                (by simp [Move41Site.sourceTets]),
              hn s.sourceTet₂
                (by simp [Move41Site.sourceTets]),
              hn s.sourceTet₃
                (by simp [Move41Site.sourceTets])
            ]
            exact ih'

    exact aux K.tets (fun _ h => h)

  rw [
    hcore.vertexDegree_eq_incidentTetCount,
    hpartition
  ]

  have h₀ : (K.tets.filter p₀).length = 1 := by
    simpa [p₀] using
      hsourcesExact s.sourceTet₀
        (by simp [Move41Site.sourceTets])

  have h₁ : (K.tets.filter p₁).length = 1 := by
    simpa [p₁] using
      hsourcesExact s.sourceTet₁
        (by simp [Move41Site.sourceTets])

  have h₂ : (K.tets.filter p₂).length = 1 := by
    simpa [p₂] using
      hsourcesExact s.sourceTet₂
        (by simp [Move41Site.sourceTets])

  have h₃ : (K.tets.filter p₃).length = 1 := by
    simpa [p₃] using
      hsourcesExact s.sourceTet₃
        (by simp [Move41Site.sourceTets])

  omega

end Poincare
