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

/-- Exact degree bookkeeping for a genuine `4 → 1` replacement: insertion of
the target balances erasure of the four source tetrahedra vertex by vertex. -/
theorem ClosedTriangulationCore.move41Site_replace_vertexDegree_balance
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) (v : Nat) :
    vertexDegree K v + s.targetTet.verts.count v =
      vertexDegree (s.replace K) v + s.sourceTet₀.verts.count v +
        s.sourceTet₁.verts.count v + s.sourceTet₂.verts.count v +
        s.sourceTet₃.verts.count v := by
  classical
  have sourceExists (source : Tet) (hsource : source ∈ s.sourceTets) :
      ∃ τ ∈ K.tets, SameTetVertices τ source := by
    have hlength := hlegal.sourceOccursExactlyOnce source hsource
    have hne : K.tets.filter (fun τ ↦ sameTetVerticesBool τ source) ≠ [] := by
      intro hempty
      simp [hempty] at hlength
    rcases List.exists_mem_of_ne_nil _ hne with ⟨τ, hτ⟩
    exact ⟨τ, by simpa [sameTetVerticesBool_eq_true_iff] using hτ⟩
  have hp := hlegal.sourcePairwiseDistinct
  simp [Move41Site.sourceTets] at hp
  have hu0 := hcore.existsUnique_sameTetVertices
    (sourceExists s.sourceTet₀ (by simp [Move41Site.sourceTets]))
  have hu1 := hcore.existsUnique_sameTetVertices
    (sourceExists s.sourceTet₁ (by simp [Move41Site.sourceTets]))
  have hu2 := hcore.existsUnique_sameTetVertices
    (sourceExists s.sourceTet₂ (by simp [Move41Site.sourceTets]))
  have hu3 := hcore.existsUnique_sameTetVertices
    (sourceExists s.sourceTet₃ (by simp [Move41Site.sourceTets]))
  have hu1' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu1
    (fun h ↦ hp.1.1 (sameTetVertices_symm h))
  have hu2' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2
    (fun h ↦ hp.1.2.1 (sameTetVertices_symm h))
  have hu2'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2'
    (fun h ↦ hp.2.1.1 (sameTetVertices_symm h))
  have hu3' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu3
    (fun h ↦ hp.1.2.2 (sameTetVertices_symm h))
  have hu3'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu3'
    (fun h ↦ hp.2.1.2 (sameTetVertices_symm h))
  have hu3''' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu3''
    (fun h ↦ hp.2.2 (sameTetVertices_symm h))
  have guard (source : Tet) (hsource : source ∈ s.sourceTets) :
      ∀ τ ∈ K.tets, SameTetVertices τ source →
        τ.verts.count v = source.verts.count v := by
    intro τ hτ hsame
    have hτn := hcore.1 τ hτ
    have hsn : source.verts.Nodup := by
      simp [Move41Site.sourceTets] at hsource
      have hd := s.distinct
      simp at hd
      rcases hsource with rfl | rfl | rfl | rfl <;>
        simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
          Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts] <;>
        aesop
    by_cases hv : v ∈ source.verts
    · rw [List.count_eq_one_of_mem hτn ((hsame v).2 hv),
        List.count_eq_one_of_mem hsn hv]
    · have hvτ : v ∉ τ.verts := fun h ↦ hv ((hsame v).1 h)
      simp [List.Nodup.count hτn, List.Nodup.count hsn, hv, hvτ]
  have e0 := eraseFirstSameTet_count_flatMap s.sourceTet₀ K.tets v
    ⟨hu0.choose, hu0.choose_spec.1⟩
    (guard s.sourceTet₀ (by simp [Move41Site.sourceTets]))
  have e1 := eraseFirstSameTet_count_flatMap s.sourceTet₁
    (eraseFirstSameTet s.sourceTet₀ K.tets) v
    ⟨hu1'.choose, hu1'.choose_spec.1⟩
    (fun τ hτ hs ↦ guard s.sourceTet₁ (by simp [Move41Site.sourceTets]) τ
      (mem_of_mem_eraseFirstSameTet hτ) hs)
  have e2 := eraseFirstSameTet_count_flatMap s.sourceTet₂
    (eraseFirstSameTet s.sourceTet₁
      (eraseFirstSameTet s.sourceTet₀ K.tets)) v
    ⟨hu2''.choose, hu2''.choose_spec.1⟩
    (fun τ hτ hs ↦ guard s.sourceTet₂ (by simp [Move41Site.sourceTets]) τ
      (mem_of_mem_eraseFirstSameTet (mem_of_mem_eraseFirstSameTet hτ)) hs)
  have e3 := eraseFirstSameTet_count_flatMap s.sourceTet₃
    (eraseFirstSameTet s.sourceTet₂
      (eraseFirstSameTet s.sourceTet₁
        (eraseFirstSameTet s.sourceTet₀ K.tets))) v
    ⟨hu3'''.choose, hu3'''.choose_spec.1⟩
    (fun τ hτ hs ↦ guard s.sourceTet₃ (by simp [Move41Site.sourceTets]) τ
      (mem_of_mem_eraseFirstSameTet
        (mem_of_mem_eraseFirstSameTet
          (mem_of_mem_eraseFirstSameTet hτ))) hs)
  change (K.tets.flatMap Tet.verts).count v + _ =
    ((s.replace K).tets.flatMap Tet.verts).count v + _ + _ + _ + _
  simp [Move41Site.replace, Move41Site.unchangedTets,
    List.count_append] at ⊢
  omega

/-- Each outer vertex of a genuine legal `4 → 1` site loses exactly two
incident tetrahedra: three source tetrahedra are removed and the target
tetrahedron is inserted. -/
theorem ClosedTriangulationCore.move41Site_replace_outer_vertexDegree
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    vertexDegree K s.a = vertexDegree (s.replace K) s.a + 2 ∧
    vertexDegree K s.b = vertexDegree (s.replace K) s.b + 2 ∧
    vertexDegree K s.c = vertexDegree (s.replace K) s.c + 2 ∧
    vertexDegree K s.d = vertexDegree (s.replace K) s.d + 2 := by
  classical
  have sourceExists (source : Tet) (hsource : source ∈ s.sourceTets) :
      ∃ τ ∈ K.tets, SameTetVertices τ source := by
    have hlength := hlegal.sourceOccursExactlyOnce source hsource
    have hne : K.tets.filter
        (fun τ => sameTetVerticesBool τ source) ≠ [] := by
      intro hempty
      simp [hempty] at hlength
    rcases List.exists_mem_of_ne_nil _ hne with ⟨τ, hτ⟩
    exact ⟨τ, by simpa [sameTetVerticesBool_eq_true_iff] using hτ⟩
  have hp := hlegal.sourcePairwiseDistinct
  simp [Move41Site.sourceTets] at hp
  have hu0 := hcore.existsUnique_sameTetVertices
    (sourceExists s.sourceTet₀ (by simp [Move41Site.sourceTets]))
  have hu1 := hcore.existsUnique_sameTetVertices
    (sourceExists s.sourceTet₁ (by simp [Move41Site.sourceTets]))
  have hu2 := hcore.existsUnique_sameTetVertices
    (sourceExists s.sourceTet₂ (by simp [Move41Site.sourceTets]))
  have hu3 := hcore.existsUnique_sameTetVertices
    (sourceExists s.sourceTet₃ (by simp [Move41Site.sourceTets]))
  have hu1' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu1
    (fun h => hp.1.1 (sameTetVertices_symm h))
  have hu2' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2
    (fun h => hp.1.2.1 (sameTetVertices_symm h))
  have hu2'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2'
    (fun h => hp.2.1.1 (sameTetVertices_symm h))
  have hu3' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu3
    (fun h => hp.1.2.2 (sameTetVertices_symm h))
  have hu3'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu3'
    (fun h => hp.2.1.2 (sameTetVertices_symm h))
  have hu3''' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu3''
    (fun h => hp.2.2 (sameTetVertices_symm h))
  have balance (v : Nat) :
      vertexDegree K v + s.targetTet.verts.count v =
        vertexDegree (s.replace K) v + s.sourceTet₀.verts.count v +
          s.sourceTet₁.verts.count v + s.sourceTet₂.verts.count v +
          s.sourceTet₃.verts.count v := by
    have guard (source : Tet) (hsource : source ∈ s.sourceTets) :
        ∀ τ ∈ K.tets, SameTetVertices τ source →
          τ.verts.count v = source.verts.count v := by
      intro τ hτ hsame
      have hτn := hcore.1 τ hτ
      have hsn : source.verts.Nodup := by
        simp [Move41Site.sourceTets] at hsource
        have hd := s.distinct
        simp at hd
        rcases hsource with rfl | rfl | rfl | rfl <;>
          simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
            Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts] <;>
          aesop
      by_cases hv : v ∈ source.verts
      · rw [List.count_eq_one_of_mem hτn ((hsame v).2 hv),
            List.count_eq_one_of_mem hsn hv]
      · have hvτ : v ∉ τ.verts := fun h => hv ((hsame v).1 h)
        simp [List.Nodup.count hτn, List.Nodup.count hsn, hv, hvτ]
    have e0 := eraseFirstSameTet_count_flatMap s.sourceTet₀ K.tets v
      ⟨hu0.choose, hu0.choose_spec.1⟩
      (guard s.sourceTet₀ (by simp [Move41Site.sourceTets]))
    have e1 := eraseFirstSameTet_count_flatMap s.sourceTet₁
      (eraseFirstSameTet s.sourceTet₀ K.tets) v
      ⟨hu1'.choose, hu1'.choose_spec.1⟩
      (fun τ hτ hs => guard s.sourceTet₁ (by simp [Move41Site.sourceTets]) τ
        (mem_of_mem_eraseFirstSameTet hτ) hs)
    have e2 := eraseFirstSameTet_count_flatMap s.sourceTet₂
      (eraseFirstSameTet s.sourceTet₁
        (eraseFirstSameTet s.sourceTet₀ K.tets)) v
      ⟨hu2''.choose, hu2''.choose_spec.1⟩
      (fun τ hτ hs => guard s.sourceTet₂ (by simp [Move41Site.sourceTets]) τ
        (mem_of_mem_eraseFirstSameTet (mem_of_mem_eraseFirstSameTet hτ)) hs)
    have e3 := eraseFirstSameTet_count_flatMap s.sourceTet₃
      (eraseFirstSameTet s.sourceTet₂
        (eraseFirstSameTet s.sourceTet₁
          (eraseFirstSameTet s.sourceTet₀ K.tets))) v
      ⟨hu3'''.choose, hu3'''.choose_spec.1⟩
      (fun τ hτ hs => guard s.sourceTet₃ (by simp [Move41Site.sourceTets]) τ
        (mem_of_mem_eraseFirstSameTet
          (mem_of_mem_eraseFirstSameTet
            (mem_of_mem_eraseFirstSameTet hτ))) hs)
    change (K.tets.flatMap Tet.verts).count v + _ =
      ((s.replace K).tets.flatMap Tet.verts).count v + _ + _ + _ + _
    simp [Move41Site.replace, Move41Site.unchangedTets,
      List.count_append] at ⊢
    omega
  have ha := balance s.a
  have hb := balance s.b
  have hc := balance s.c
  have hd := balance s.d
  have hdistinct := s.distinct
  simp at hdistinct
  rcases hdistinct with
    ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩
  have hba : s.b ≠ s.a := Ne.symm hab
  have hca : s.c ≠ s.a := Ne.symm hac
  have hda : s.d ≠ s.a := Ne.symm had
  have hea : s.e ≠ s.a := Ne.symm hae
  have hcb : s.c ≠ s.b := Ne.symm hbc
  have hdb : s.d ≠ s.b := Ne.symm hbd
  have heb : s.e ≠ s.b := Ne.symm hbe
  have hdc : s.d ≠ s.c := Ne.symm hcd
  have hec : s.e ≠ s.c := Ne.symm hce
  have hed : s.e ≠ s.d := Ne.symm hde
  simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
    Move41Site.sourceTet₂, Move41Site.sourceTet₃,
    Move41Site.targetTet, Tet.verts,
    hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde,
    hba, hca, hda, hea, hcb, hdb, heb, hdc, hec, hed] at ha hb hc hd
  omega

/-- A genuine `4 → 1` replacement leaves the degree of every vertex outside
the five move labels unchanged. -/
theorem ClosedTriangulationCore.move41Site_replace_vertexDegree_offSite
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) {v : Nat}
    (hva : v ≠ s.a) (hvb : v ≠ s.b) (hvc : v ≠ s.c)
    (hvd : v ≠ s.d) (hve : v ≠ s.e) :
    vertexDegree (s.replace K) v = vertexDegree K v := by
  have hav : s.a ≠ v := Ne.symm hva
  have hbv : s.b ≠ v := Ne.symm hvb
  have hcv : s.c ≠ v := Ne.symm hvc
  have hdv : s.d ≠ v := Ne.symm hvd
  have hev : s.e ≠ v := Ne.symm hve
  have h := hcore.move41Site_replace_vertexDegree_balance s hlegal v
  simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
    Move41Site.sourceTet₂, Move41Site.sourceTet₃,
    Move41Site.targetTet, Tet.verts,
    hav, hbv, hcv, hdv, hev] at h
  omega

end Poincare
