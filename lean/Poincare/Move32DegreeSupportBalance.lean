import Poincare.Move32SurvivorClassification
import Poincare.VertexIncidenceCounting

namespace Poincare

theorem ClosedTriangulationCore.move32Site_threeTargetErasure_count
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) (v : Nat) :
    (K.tets.flatMap Tet.verts).count v =
      ((s.unchangedTets K).flatMap Tet.verts).count v
        + s.targetTet₀.verts.count v
        + s.targetTet₁.verts.count v
        + s.targetTet₂.verts.count v := by
  have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hlegal.1
  rcases hlegal.1 with ⟨h0, h1, h2⟩
  have hu0 := hcore.existsUnique_sameTetVertices h0
  have hu1 := hcore.existsUnique_sameTetVertices h1
  have hu2 := hcore.existsUnique_sameTetVertices h2
  have h1' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu1
    (fun h => s.targetTet₀_not_same_targetTet₁ hfive (sameTetVertices_symm h))
  have h2' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2
    (fun h => s.targetTet₀_not_same_targetTet₂ hfive (sameTetVertices_symm h))
  have h2'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same h2'
    (fun h => s.targetTet₁_not_same_targetTet₂ hfive (sameTetVertices_symm h))
  have targetNodup (target : Tet)
      (ht : target = s.targetTet₀ ∨ target = s.targetTet₁ ∨ target = s.targetTet₂) :
      target.verts.Nodup := by
    rcases ht with rfl | rfl | rfl <;>
      simp [Move32Site.targetTet₀, Move32Site.targetTet₁,
        Move32Site.targetTet₂, Tet.verts] at hfive ⊢ <;> aesop
  have guard (target : Tet)
      (ht : target = s.targetTet₀ ∨ target = s.targetTet₁ ∨ target = s.targetTet₂) :
      ∀ tau ∈ K.tets, SameTetVertices tau target →
        tau.verts.count v = target.verts.count v := by
    intro tau htau hm
    have hTau := hcore.1 tau htau
    have hTarget := targetNodup target ht
    by_cases hv : v ∈ target.verts
    · rw [List.count_eq_one_of_mem hTarget hv,
        List.count_eq_one_of_mem hTau ((hm v).2 hv)]
    · have hvTau : v ∉ tau.verts := fun h => hv ((hm v).1 h)
      simpa [List.Nodup.count hTarget, List.Nodup.count hTau, hv, hvTau]
  have e0 := eraseFirstSameTet_count_flatMap s.targetTet₀ K.tets v h0
    (fun tau ht hm => guard s.targetTet₀ (Or.inl rfl) tau ht hm)
  have e1 := eraseFirstSameTet_count_flatMap s.targetTet₁
    (eraseFirstSameTet s.targetTet₀ K.tets) v ⟨h1'.choose, h1'.choose_spec.1⟩
    (fun tau ht hm => guard s.targetTet₁ (Or.inr (Or.inl rfl)) tau
      (mem_of_mem_eraseFirstSameTet ht) hm)
  have e2 := eraseFirstSameTet_count_flatMap s.targetTet₂
    (eraseFirstSameTet s.targetTet₁ (eraseFirstSameTet s.targetTet₀ K.tets)) v
    ⟨h2''.choose, h2''.choose_spec.1⟩
    (fun tau ht hm => guard s.targetTet₂ (Or.inr (Or.inr rfl)) tau
      (mem_of_mem_eraseFirstSameTet (mem_of_mem_eraseFirstSameTet ht)) hm)
  change _ = ((eraseFirstSameTet s.targetTet₂
    (eraseFirstSameTet s.targetTet₁ (eraseFirstSameTet s.targetTet₀ K.tets))).flatMap
      Tet.verts).count v + _ + _ + _
  omega

theorem ClosedTriangulationCore.move32Site_replace_vertexDegree_balance
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) (v : Nat) :
    vertexDegree K v + s.sourceTet₀.verts.count v + s.sourceTet₁.verts.count v =
    vertexDegree (s.replace K) v + s.targetTet₀.verts.count v +
      s.targetTet₁.verts.count v + s.targetTet₂.verts.count v := by
  have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hlegal.1
  have he := hcore.move32Site_threeTargetErasure_count s hlegal v
  change (K.tets.flatMap Tet.verts).count v + _ + _ =
    ((s.replace K).tets.flatMap Tet.verts).count v + _ + _ + _
  rw [he]
  simp [Move32Site.replace, Move32Site.unchangedTets, List.count_append]
  ac_rfl

theorem ClosedTriangulationCore.move32Site_replace_vertexDegree_site
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    vertexDegree (s.replace K) s.a = vertexDegree K s.a ∧
    vertexDegree (s.replace K) s.b = vertexDegree K s.b ∧
    vertexDegree (s.replace K) s.c = vertexDegree K s.c ∧
    vertexDegree K s.d = vertexDegree (s.replace K) s.d + 2 ∧
    vertexDegree K s.e = vertexDegree (s.replace K) s.e + 2 := by
  have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hlegal.1
  have ha := hcore.move32Site_replace_vertexDegree_balance s hlegal s.a
  have hb := hcore.move32Site_replace_vertexDegree_balance s hlegal s.b
  have hc := hcore.move32Site_replace_vertexDegree_balance s hlegal s.c
  have hd := hcore.move32Site_replace_vertexDegree_balance s hlegal s.d
  have he := hcore.move32Site_replace_vertexDegree_balance s hlegal s.e
  simp at hfive
  rcases hfive with
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
  simp [Move32Site.sourceTet₀, Move32Site.sourceTet₁, Move32Site.targetTet₀,
    Move32Site.targetTet₁, Move32Site.targetTet₂, Tet.verts,
    hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde,
    hba, hca, hda, hea, hcb, hdb, heb, hdc, hec, hed] at ha hb hc hd he
  omega

theorem ClosedTriangulationCore.move32Site_replace_vertexDegree_offSite
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) {v : Nat}
    (hva : v ≠ s.a) (hvb : v ≠ s.b) (hvc : v ≠ s.c)
    (hvd : v ≠ s.d) (hve : v ≠ s.e) :
    vertexDegree (s.replace K) v = vertexDegree K v := by
  have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hlegal.1
  have hav : s.a ≠ v := fun h => hva h.symm
  have hbv : s.b ≠ v := fun h => hvb h.symm
  have hcv : s.c ≠ v := fun h => hvc h.symm
  have hdv : s.d ≠ v := fun h => hvd h.symm
  have hev : s.e ≠ v := fun h => hve h.symm
  have h := hcore.move32Site_replace_vertexDegree_balance s hlegal v
  simp [Move32Site.sourceTet₀, Move32Site.sourceTet₁, Move32Site.targetTet₀,
    Move32Site.targetTet₁, Move32Site.targetTet₂, Tet.verts,
    hva, hvb, hvc, hvd, hve, hav, hbv, hcv, hdv, hev] at h
  omega

theorem ClosedTriangulationCore.move32Site_sharedEdge_vertexDegree_lower_bound
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    3 ≤ vertexDegree K s.d ∧ 3 ≤ vertexDegree K s.e := by
  have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hlegal.1
  have filter_le (p q : Tet → Prop) [DecidablePred p] [DecidablePred q]
      (hpq : ∀ tau, p tau → q tau) (xs : List Tet) :
      (xs.filter p).length ≤ (xs.filter q).length := by
    induction xs with
    | nil => simp
    | cons tau xs ih =>
      by_cases hp : p tau <;> by_cases hq : q tau <;> simp_all <;> omega
  constructor <;> rw [hcore.vertexDegree_eq_incidentTetCount]
  · rw [← hlegal.2.1]
    exact filter_le _ _ (fun _ h => h.1) K.tets
  · rw [← hlegal.2.1]
    exact filter_le _ _ (fun _ h => h.2) K.tets

theorem ClosedTriangulationCore.move32Site_replace_sharedEdge_vertexDegree_pos
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    0 < vertexDegree (s.replace K) s.d ∧ 0 < vertexDegree (s.replace K) s.e := by
  have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hlegal.1
  have hs := hcore.move32Site_replace_vertexDegree_site s hlegal
  have hl := hcore.move32Site_sharedEdge_vertexDegree_lower_bound s hlegal
  omega

theorem ClosedTriangulationCore.move32Site_replace_vertexSupport_mem_iff
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) (v : Nat) :
    v ∈ vertexSupport (s.replace K) ↔ v ∈ vertexSupport K := by
  have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hlegal.1
  have memDegree (J : Triangulation) (x : Nat) :
      x ∈ vertexSupport J ↔ 0 < vertexDegree J x := by
    rw [mem_vertexSupport_iff]
    change x ∈ allVerts J ↔ 0 < (allVerts J).count x
    simpa using ((Multiset.count_pos (a := x)
      (s := (↑(allVerts J) : Multiset Nat))).symm)
  rw [memDegree, memDegree]
  rcases hcore.move32Site_replace_vertexDegree_site s hlegal with ⟨ha, hb, hc, hd, he⟩
  have hp := hcore.move32Site_replace_sharedEdge_vertexDegree_pos s hlegal
  by_cases hva : v = s.a; · subst v; rw [ha]
  by_cases hvb : v = s.b; · subst v; rw [hb]
  by_cases hvc : v = s.c; · subst v; rw [hc]
  by_cases hvd : v = s.d; · subst v; omega
  by_cases hve : v = s.e; · subst v; omega
  rw [hcore.move32Site_replace_vertexDegree_offSite s hlegal hva hvb hvc hvd hve]

theorem ClosedTriangulationCore.move32Site_replace_PhiSupport_balance
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    PhiSupport (s.replace K) + vertexDefect K s.d + vertexDefect K s.e =
    PhiSupport K + vertexDefect (s.replace K) s.d +
      vertexDefect (s.replace K) s.e := by
  have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hlegal.1
  let S : Finset Nat := (vertexSupport K).toFinset
  have hsupport : (vertexSupport (s.replace K)).toFinset = S := by
    ext x
    simpa [S] using hcore.move32Site_replace_vertexSupport_mem_iff s hlegal x
  rcases hlegal.1 with ⟨⟨tau, htau, hmatch⟩, _, _⟩
  have hdSupport : s.d ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htau, (hmatch s.d).2 (by
      simp [Move32Site.targetTet₀, Tet.verts])⟩
  have heSupport : s.e ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htau, (hmatch s.e).2 (by
      simp [Move32Site.targetTet₀, Tet.verts])⟩
  have hdS : s.d ∈ S := by simpa [S] using hdSupport
  have heS : s.e ∈ S := by simpa [S] using heSupport
  have hde : s.d ≠ s.e := by simp at hfive; omega
  have heErase : s.e ∈ S.erase s.d := by simp [heS, Ne.symm hde]
  rcases hcore.move32Site_replace_vertexDegree_site s hlegal with ⟨ha, hb, hc, _, _⟩
  have hDegreeExcept (v : Nat) (hvd : v ≠ s.d) (hve : v ≠ s.e) :
      vertexDegree (s.replace K) v = vertexDegree K v := by
    by_cases hva : v = s.a; · subst v; exact ha
    by_cases hvb : v = s.b; · subst v; exact hb
    by_cases hvc : v = s.c; · subst v; exact hc
    exact hcore.move32Site_replace_vertexDegree_offSite s hlegal hva hvb hvc hvd hve
  have hRest :
      (∑ v ∈ (S.erase s.d).erase s.e, vertexDefect (s.replace K) v) =
        ∑ v ∈ (S.erase s.d).erase s.e, vertexDefect K v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hve := (Finset.mem_erase.mp hv).1
    have hvd := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
    unfold vertexDefect
    rw [hDegreeExcept v hvd hve]
  have split (J : Triangulation) :
      (∑ v ∈ S, vertexDefect J v) =
        (∑ v ∈ (S.erase s.d).erase s.e, vertexDefect J v) +
          vertexDefect J s.e + vertexDefect J s.d := by
    rw [(Finset.sum_erase_add S (vertexDefect J) hdS).symm,
      (Finset.sum_erase_add (S.erase s.d) (vertexDefect J) heErase).symm]
  rw [phiSupport_eq_finset_sum K, phiSupport_eq_finset_sum (s.replace K), hsupport]
  change (∑ v ∈ S, vertexDefect (s.replace K) v) + _ + _ =
    (∑ v ∈ S, vertexDefect K v) + _ + _
  rw [split (s.replace K), split K, hRest]
  ac_rfl

end Poincare
