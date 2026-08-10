import Poincare.Move23ActualRegions
import Poincare.TriangulationTopologicalGeometricIntersections

open Set

namespace Poincare

def Move23Site.unchangedTets (s : Move23Site) (K : Triangulation) : List Tet :=
  eraseFirstSameTet s.rightTet (eraseFirstSameTet s.leftTet K.tets)

@[simp] theorem Move23Site.replace_tets_eq (s : Move23Site) (K : Triangulation) :
    (s.replace K).tets =
      s.newTet₀ :: s.newTet₁ :: s.newTet₂ :: s.unchangedTets K := by
  rfl

theorem mem_of_mem_eraseFirstSameTet {tau target : Tet} {tets : List Tet}
    (h : tau ∈ eraseFirstSameTet target tets) : tau ∈ tets := by
  induction tets generalizing tau with
  | nil => simp [eraseFirstSameTet] at h
  | cons rho rest ih =>
      by_cases hb : sameTetVerticesBool rho target = true
      · have hr : tau ∈ rest := by simpa [eraseFirstSameTet, hb] using h
        exact by simp [hr]
      · have hb' : sameTetVerticesBool rho target = false := by
          cases heq : sameTetVerticesBool rho target <;> simp_all
        have hr : tau = rho ∨ tau ∈ eraseFirstSameTet target rest := by
          simpa [eraseFirstSameTet, hb'] using h
        exact hr.elim (fun e => by simp [e]) (fun e => by simp [ih e])

theorem mem_eraseFirstSameTet_of_mem_of_not_same
    {tau target : Tet} {tets : List Tet} (h : tau ∈ tets)
    (hn : ¬ SameTetVertices tau target) :
    tau ∈ eraseFirstSameTet target tets := by
  induction tets generalizing tau with
  | nil => simp at h
  | cons sigma rest ih =>
      rcases (by simpa using h : tau = sigma ∨ tau ∈ rest) with heq | ht
      · subst sigma
        have hb : sameTetVerticesBool tau target = false := by
          cases heqb : sameTetVerticesBool tau target with
          | false => rfl
          | true => exact (hn ((sameTetVerticesBool_eq_true_iff tau target).1 heqb)).elim
        simp [eraseFirstSameTet, hb]
      · by_cases hb : sameTetVerticesBool sigma target = true
        · rw [eraseFirstSameTet]
          simp [hb]
          exact ht
        · have hb' : sameTetVerticesBool sigma target = false := by
            cases heq : sameTetVerticesBool sigma target <;> simp_all
          simp [eraseFirstSameTet, hb', ih ht hn]

theorem eraseFirstSameTet_sublist (target : Tet) (tets : List Tet) :
    List.Sublist (eraseFirstSameTet target tets) tets := by
  induction tets with
  | nil => simp [eraseFirstSameTet]
  | cons x xs ih =>
      by_cases hb : sameTetVerticesBool x target = true
      · simp [eraseFirstSameTet, hb]
      · have hb' : sameTetVerticesBool x target = false := by
          cases he : sameTetVerticesBool x target <;> simp_all
        simpa [eraseFirstSameTet, hb'] using ih.cons_cons x

/-- Erasing the first representative of a tetrahedron vertex set does not
change the number of entries satisfying a vertex-set invariant predicate
which is false on that vertex set.  No uniqueness hypothesis is needed. -/
theorem eraseFirstSameTet_filter_length_eq_of_not
    (p : Tet → Prop) [DecidablePred p]
    (target : Tet) (tets : List Tet)
    (hinvariant : ∀ τ σ, SameTetVertices τ σ → (p τ ↔ p σ))
    (hnot : ¬ p target) :
    ((eraseFirstSameTet target tets).filter p).length =
      (tets.filter p).length := by
  induction tets with
  | nil => simp [eraseFirstSameTet]
  | cons τ rest ih =>
      by_cases hb : sameTetVerticesBool τ target = true
      · have hsame : SameTetVertices τ target :=
          (sameTetVerticesBool_eq_true_iff τ target).1 hb
        have hτ : ¬ p τ := by
          intro hp
          exact hnot ((hinvariant τ target hsame).1 hp)
        simp [eraseFirstSameTet, hb, hτ]
      · have hbfalse : sameTetVerticesBool τ target = false := by
          cases h : sameTetVerticesBool τ target <;> simp_all
        rw [eraseFirstSameTet]
        simp only [hbfalse]
        by_cases hp : p τ <;> simp [hp, ih]

/-- Erasing the first representative of a tetrahedron vertex set removes
exactly one entry from a vertex-set invariant filtered count, provided that
the vertex set is represented and satisfies the predicate.  As with the
negative-erasure lemma, uniqueness is unnecessary. -/
theorem eraseFirstSameTet_filter_length_add_one_eq
    (p : Tet → Prop) [DecidablePred p]
    (target : Tet) (tets : List Tet)
    (hinvariant : ∀ τ σ, SameTetVertices τ σ → (p τ ↔ p σ))
    (hrepresented : ∃ τ ∈ tets, SameTetVertices τ target)
    (hpos : p target) :
    ((eraseFirstSameTet target tets).filter p).length + 1 =
      (tets.filter p).length := by
  induction tets with
  | nil => simp at hrepresented
  | cons τ rest ih =>
      by_cases hb : sameTetVerticesBool τ target = true
      · have hsame : SameTetVertices τ target :=
          (sameTetVerticesBool_eq_true_iff τ target).1 hb
        have hτ : p τ := (hinvariant τ target hsame).2 hpos
        simp [eraseFirstSameTet, hb, hτ]
      · have hbfalse : sameTetVerticesBool τ target = false := by
          cases h : sameTetVerticesBool τ target <;> simp_all
        have hrest : ∃ σ ∈ rest, SameTetVertices σ target := by
          rcases hrepresented with ⟨σ, hσ, hs⟩
          rcases (by simpa using hσ : σ = τ ∨ σ ∈ rest) with heq | hσrest
          · have hsame : SameTetVertices τ target := by simpa [heq] using hs
            exact (hb ((sameTetVerticesBool_eq_true_iff τ target).2 hsame)).elim
          · exact ⟨σ, hσrest, hs⟩
        rw [eraseFirstSameTet]
        simp only [hbfalse]
        by_cases hτ : p τ <;> simp [hτ, ih hrest]

/-- At a legal `2-3` site, removing the two uniquely represented source
tetrahedra splits any vertex-set invariant filtered count into the unchanged
count and the explicit two-tetrahedron local count. -/
theorem ClosedTriangulationCore.move23Site_unchanged_filter_length_add_local_eq
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K)
    (p : Tet → Prop) [DecidablePred p]
    (hinvariant : ∀ τ σ, SameTetVertices τ σ → (p τ ↔ p σ)) :
    ((s.unchangedTets K).filter p).length +
        ([s.leftTet, s.rightTet].filter p).length =
      (K.tets.filter p).length := by
  have hdata := hcore.move23Site_simpleBistellarData s hlegal
  have hrightAfter :
      ∃ τ ∈ eraseFirstSameTet s.leftTet K.tets,
        SameTetVertices τ s.rightTet :=
    s.rightMatch_survives_eraseLeft K.tets ⟨hdata.2.2.1.choose,
      hdata.2.2.1.choose_spec.1.1, hdata.2.2.1.choose_spec.1.2⟩
  by_cases hleft : p s.leftTet
  · have eleft := eraseFirstSameTet_filter_length_add_one_eq
      p s.leftTet K.tets hinvariant
      ⟨hdata.2.1.choose, hdata.2.1.choose_spec.1.1,
        hdata.2.1.choose_spec.1.2⟩ hleft
    by_cases hright : p s.rightTet
    · have eright := eraseFirstSameTet_filter_length_add_one_eq
        p s.rightTet (eraseFirstSameTet s.leftTet K.tets)
        hinvariant hrightAfter hright
      simp only [Move23Site.unchangedTets]
      simp [hleft, hright] at ⊢
      omega
    · have eright := eraseFirstSameTet_filter_length_eq_of_not
        p s.rightTet (eraseFirstSameTet s.leftTet K.tets)
        hinvariant hright
      simp only [Move23Site.unchangedTets]
      simp [hleft, hright] at ⊢
      omega
  · have eleft := eraseFirstSameTet_filter_length_eq_of_not
      p s.leftTet K.tets hinvariant hleft
    by_cases hright : p s.rightTet
    · have eright := eraseFirstSameTet_filter_length_add_one_eq
        p s.rightTet (eraseFirstSameTet s.leftTet K.tets)
        hinvariant hrightAfter hright
      simp only [Move23Site.unchangedTets]
      simp [hleft, hright] at ⊢
      omega
    · have eright := eraseFirstSameTet_filter_length_eq_of_not
        p s.rightTet (eraseFirstSameTet s.leftTet K.tets)
        hinvariant hright
      simp only [Move23Site.unchangedTets]
      simp [hleft, hright] at ⊢
      omega

theorem not_same_of_mem_eraseFirstSameTet_of_unique
    {tau target : Tet} {tets : List Tet}
    (hn : tets.Nodup)
    (hu : ∃! rho : Tet, rho ∈ tets ∧ SameTetVertices rho target)
    (h : tau ∈ eraseFirstSameTet target tets) :
    ¬ SameTetVertices tau target := by
  induction tets generalizing tau with
  | nil => simp [eraseFirstSameTet] at h
  | cons sigma rest ih =>
      by_cases hb : sameTetVerticesBool sigma target = true
      · intro htau
        have heq : tau = sigma := hu.unique ⟨mem_of_mem_eraseFirstSameTet h, htau⟩
          ⟨by simp, (sameTetVerticesBool_eq_true_iff sigma target).1 hb⟩
        subst tau
        have hs : sigma ∈ rest := by simpa [eraseFirstSameTet, hb] using h
        exact (List.nodup_cons.mp hn).1 hs
      · have hb' : sameTetVerticesBool sigma target = false := by
          cases he : sameTetVerticesBool sigma target <;> simp_all
        rcases hu with ⟨rho, hrho, huniq⟩
        have hrrest : rho ∈ rest := by
          rcases (by simpa using hrho.1 : rho = sigma ∨ rho ∈ rest) with hrs | hrs
          · subst rho
            exact (hb ((sameTetVerticesBool_eq_true_iff sigma target).2 hrho.2)).elim
          · exact hrs
        have hurest : ∃! x : Tet, x ∈ rest ∧ SameTetVertices x target :=
          ⟨rho, ⟨hrrest, hrho.2⟩, fun x hx => huniq x ⟨by simp [hx.1], hx.2⟩⟩
        by_cases heq : tau = sigma
        · subst tau
          exact fun hs => hb ((sameTetVerticesBool_eq_true_iff sigma target).2 hs)
        · exact ih (List.nodup_cons.mp hn).2 hurest
            (by simpa [eraseFirstSameTet, hb', heq] using h)

theorem ClosedTriangulationCore.move23Site_mem_unchangedTets
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K) :
    tau ∈ K.tets ∧ tau ∈ (s.replace K).tets ∧
      ¬ SameTetVertices tau s.leftTet ∧ ¬ SameTetVertices tau s.rightTet := by
  have hdata := hcore.move23Site_simpleBistellarData s hlegal
  have hnK : K.tets.Nodup := hcore.2.1.imp (by
    intro x y hxy heq
    subst y
    exact hxy (fun _ => Iff.rfl))
  have hnAfter : (eraseFirstSameTet s.leftTet K.tets).Nodup :=
    hnK.sublist (eraseFirstSameTet_sublist _ _)
  have hright : ¬ SameTetVertices tau s.rightTet :=
    not_same_of_mem_eraseFirstSameTet_of_unique hnAfter
      (by
        rcases hdata.2.2.1 with ⟨rho, hrho, hu⟩
        have hnl : ¬ SameTetVertices rho s.leftTet := by
          intro hl
          exact s.leftTet_not_same_rightTet (fun v => (hl v).symm.trans (hrho.2 v))
        exact ⟨rho, ⟨mem_eraseFirstSameTet_of_mem_of_not_same hrho.1 hnl, hrho.2⟩,
          fun x hx => hu x ⟨mem_of_mem_eraseFirstSameTet hx.1, hx.2⟩⟩)
      (by simpa [Move23Site.unchangedTets] using htau)
  have hafter : tau ∈ eraseFirstSameTet s.leftTet K.tets :=
    mem_of_mem_eraseFirstSameTet htau
  have hleft : ¬ SameTetVertices tau s.leftTet :=
    not_same_of_mem_eraseFirstSameTet_of_unique hnK hdata.2.1 hafter
  exact ⟨mem_of_mem_eraseFirstSameTet hafter, by
      rw [s.replace_tets_eq K]
      simp [htau],
    hleft, hright⟩

theorem ClosedTriangulationCore.move23Site_same_source_of_contains_sharedFace
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htauK : tau ∈ K.tets) (ha : s.a ∈ tau.verts)
    (hb : s.b ∈ tau.verts) (hc : s.c ∈ tau.verts) :
    SameTetVertices tau s.leftTet ∨ SameTetVertices tau s.rightTet := by
  obtain ⟨tauL, tauR, hL, hR, hsL, hsR, _⟩ := s.exists_actual_source_region hlegal.1
  let f := fun t : Tet => s.a ∈ t.verts ∧ s.b ∈ t.verts ∧ s.c ∈ t.verts
  have hmem (t : Tet) (ht : t ∈ K.tets) (hf : f t) : t ∈ K.tets.filter f := by simp [ht, hf]
  have hLf : f tauL := by
    constructor
    · exact (hsL s.a).2 (by simp [Move23Site.leftTet, Tet.verts])
    constructor
    · exact (hsL s.b).2 (by simp [Move23Site.leftTet, Tet.verts])
    · exact (hsL s.c).2 (by simp [Move23Site.leftTet, Tet.verts])
  have hRf : f tauR := by
    constructor
    · exact (hsR s.a).2 (by simp [Move23Site.rightTet, Tet.verts])
    constructor
    · exact (hsR s.b).2 (by simp [Move23Site.rightTet, Tet.verts])
    · exact (hsR s.c).2 (by simp [Move23Site.rightTet, Tet.verts])
  have hne : tauL ≠ tauR := hcore.move23Site_source_tets_ne s hL hsL hR hsR
  have hnK : K.tets.Nodup := hcore.2.1.imp (by
    intro x y hxy heq
    subst y
    exact hxy (fun _ => Iff.rfl))
  have hn : (K.tets.filter f).Nodup := hnK.filter _
  have hlen : (K.tets.filter f).length = 2 := hlegal.2.1
  have hall : ∀ x ∈ K.tets.filter f, x = tauL ∨ x = tauR := by
    intro x hx
    rcases heq : K.tets.filter f with _ | ⟨u, us⟩
    · simp [heq] at hx
    · rcases us with _ | ⟨v, vs⟩
      · simp [heq] at hlen
      · have : vs = [] := by simpa [heq] using hlen
        subst vs
        have huv : u ≠ v := by simpa [heq] using hn
        have hLm := hmem tauL hL hLf
        have hRm := hmem tauR hR hRf
        simp [heq] at hx hLm hRm
        rcases hx with rfl | rfl <;> aesop
  rcases hall tau (hmem tau htauK ⟨ha, hb, hc⟩) with rfl | rfl
  · exact Or.inl hsL
  · exact Or.inr hsR

theorem ClosedTriangulationCore.move23Site_unchangedTet_not_contains_sharedFace
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K) :
    ¬ (s.a ∈ tau.verts ∧ s.b ∈ tau.verts ∧ s.c ∈ tau.verts) := by
  intro h
  have hm := hcore.move23Site_mem_unchangedTets s hlegal htau
  exact (hcore.move23Site_same_source_of_contains_sharedFace s hlegal hm.1 h.1 h.2.1 h.2.2).elim
    hm.2.2.1 hm.2.2.2

theorem ClosedTriangulationCore.move23Site_unchangedTet_not_contains_newEdge
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K) :
    ¬ (s.d ∈ tau.verts ∧ s.e ∈ tau.verts) :=
  hlegal.2.2 tau (hcore.move23Site_mem_unchangedTets s hlegal htau).1

theorem tetBody_inter_subset_of_common_support
    (K : Triangulation) (tau rho sigma : Tet)
    (htau : tau ∈ K.tets) (hrho : rho ∈ K.tets)
    (hsub : tau.verts.toFinset ∩ rho.verts.toFinset ⊆ sigma.verts.toFinset) :
    triangulationTopologicalTetBody tau ∩ triangulationTopologicalTetBody rho ⊆
      triangulationTopologicalTetBody sigma := by
  rw [triangulationTopologicalTetBody, triangulationTopologicalTetBody,
    triangulationTopologicalTetrahedron_inter_eq_commonFace K tau rho htau hrho]
  exact convexHull_mono (Set.image_mono (by
    intro v hv
    exact hsub hv))

theorem common_support_subset_of_missing
    (tau rho sigma : Tet) (z : Nat) (hz : z ∉ tau.verts)
    (hface : ∀ v ∈ rho.verts, v = z ∨ v ∈ sigma.verts) :
    tau.verts.toFinset ∩ rho.verts.toFinset ⊆ sigma.verts.toFinset := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hvt, hvr⟩
  rcases hface v (by simpa using hvr) with rfl | hs
  · exact (hz (by simpa using hvt)).elim
  · simpa using hs

theorem ClosedTriangulationCore.move23Site_unchangedTet_inter_source_subset_target
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K) :
    triangulationTopologicalTetBody tau ∩
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ⊆
      move23PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
  obtain ⟨tauL, tauR, hL, hR, hsL, hsR, hregion⟩ :=
    s.exists_actual_source_region hlegal.1
  have hm := hcore.move23Site_mem_unchangedTets s hlegal htau
  have hmiss := hcore.move23Site_unchangedTet_not_contains_sharedFace s hlegal htau
  intro p hp
  rw [← hregion] at hp
  rcases hp with ⟨hpTau, hpL | hpR⟩
  · have branch (sigma : Tet)
        (hsub : tau.verts.toFinset ∩ tauL.verts.toFinset ⊆ sigma.verts.toFinset) :
        p ∈ triangulationTopologicalTetBody sigma :=
      tetBody_inter_subset_of_common_support K tau tauL sigma hm.1 hL hsub ⟨hpTau, hpL⟩
    by_cases ha : s.a ∈ tau.verts
    · by_cases hb : s.b ∈ tau.verts
      · have hc : s.c ∉ tau.verts := fun hc => hmiss ⟨ha, hb, hc⟩
        rw [← s.newTets_tetBody_union]
        exact Or.inl (Or.inl (branch s.newTet₀ (by
          intro v hv
          rcases Finset.mem_inter.mp hv with ⟨hvT, hvS⟩
          have hvL : v ∈ s.leftTet.verts := (hsL v).1 (by simpa using hvS)
          simp [Move23Site.leftTet, Move23Site.newTet₀, Tet.verts] at hvL ⊢
          aesop)))
      · rw [← s.newTets_tetBody_union]
        exact Or.inl (Or.inr (branch s.newTet₁ (by
          intro v hv
          rcases Finset.mem_inter.mp hv with ⟨hvT, hvS⟩
          have hvL : v ∈ s.leftTet.verts := (hsL v).1 (by simpa using hvS)
          simp [Move23Site.leftTet, Move23Site.newTet₁, Tet.verts] at hvL ⊢
          aesop)))
    · rw [← s.newTets_tetBody_union]
      exact Or.inr (branch s.newTet₂ (by
        intro v hv
        rcases Finset.mem_inter.mp hv with ⟨hvT, hvS⟩
        have hvL : v ∈ s.leftTet.verts := (hsL v).1 (by simpa using hvS)
        simp [Move23Site.leftTet, Move23Site.newTet₂, Tet.verts] at hvL ⊢
        aesop))
  · have branch (sigma : Tet)
        (hsub : tau.verts.toFinset ∩ tauR.verts.toFinset ⊆ sigma.verts.toFinset) :
        p ∈ triangulationTopologicalTetBody sigma :=
      tetBody_inter_subset_of_common_support K tau tauR sigma hm.1 hR hsub ⟨hpTau, hpR⟩
    by_cases ha : s.a ∈ tau.verts
    · by_cases hb : s.b ∈ tau.verts
      · have hc : s.c ∉ tau.verts := fun hc => hmiss ⟨ha, hb, hc⟩
        rw [← s.newTets_tetBody_union]
        exact Or.inl (Or.inl (branch s.newTet₀ (by
          intro v hv
          rcases Finset.mem_inter.mp hv with ⟨hvT, hvS⟩
          have hvR : v ∈ s.rightTet.verts := (hsR v).1 (by simpa using hvS)
          simp [Move23Site.rightTet, Move23Site.newTet₀, Tet.verts] at hvR ⊢
          aesop)))
      · rw [← s.newTets_tetBody_union]
        exact Or.inl (Or.inr (branch s.newTet₁ (by
          intro v hv
          rcases Finset.mem_inter.mp hv with ⟨hvT, hvS⟩
          have hvR : v ∈ s.rightTet.verts := (hsR v).1 (by simpa using hvS)
          simp [Move23Site.rightTet, Move23Site.newTet₁, Tet.verts] at hvR ⊢
          aesop)))
    · rw [← s.newTets_tetBody_union]
      exact Or.inr (branch s.newTet₂ (by
        intro v hv
        rcases Finset.mem_inter.mp hv with ⟨hvT, hvS⟩
        have hvR : v ∈ s.rightTet.verts := (hsR v).1 (by simpa using hvS)
        simp [Move23Site.rightTet, Move23Site.newTet₂, Tet.verts] at hvR ⊢
        aesop))

theorem ClosedTriangulationCore.move23Site_unchangedTet_inter_target_subset_source
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K) :
    triangulationTopologicalTetBody tau ∩
        move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ⊆
      move23PiSourceLocalCarrier s.a s.b s.c s.d s.e := by
  have hm := hcore.move23Site_mem_unchangedTets s hlegal htau
  have hedge := hcore.move23Site_unchangedTet_not_contains_newEdge s hlegal htau
  rcases s.newTets_mem_replace K with ⟨h0, h1, h2⟩
  intro p hp
  rw [← s.newTets_tetBody_union] at hp
  rcases hp with ⟨hpTau, (hp0 | hp1) | hp2⟩
  all_goals
    have hmissing : s.d ∉ tau.verts ∨ s.e ∉ tau.verts := by
      by_cases hd : s.d ∈ tau.verts
      · exact Or.inr (fun he => hedge ⟨hd, he⟩)
      · exact Or.inl hd
  · rcases hmissing with hd | he
    · apply Or.inr
      simpa using tetBody_inter_subset_of_common_support (s.replace K) tau s.newTet₀ s.rightTet
        hm.2.1 h0 (common_support_subset_of_missing tau s.newTet₀ s.rightTet s.d hd
          (by intro v hv; simp [Move23Site.newTet₀, Move23Site.rightTet, Tet.verts] at hv ⊢; aesop))
        ⟨hpTau, by simpa using hp0⟩
    · apply Or.inl
      simpa using tetBody_inter_subset_of_common_support (s.replace K) tau s.newTet₀ s.leftTet
        hm.2.1 h0 (common_support_subset_of_missing tau s.newTet₀ s.leftTet s.e he
          (by intro v hv; simp [Move23Site.newTet₀, Move23Site.leftTet, Tet.verts] at hv ⊢; aesop))
        ⟨hpTau, by simpa using hp0⟩
  · rcases hmissing with hd | he
    · apply Or.inr
      simpa using tetBody_inter_subset_of_common_support (s.replace K) tau s.newTet₁ s.rightTet
        hm.2.1 h1 (common_support_subset_of_missing tau s.newTet₁ s.rightTet s.d hd
          (by intro v hv; simp [Move23Site.newTet₁, Move23Site.rightTet, Tet.verts] at hv ⊢; aesop))
        ⟨hpTau, by simpa using hp1⟩
    · apply Or.inl
      simpa using tetBody_inter_subset_of_common_support (s.replace K) tau s.newTet₁ s.leftTet
        hm.2.1 h1 (common_support_subset_of_missing tau s.newTet₁ s.leftTet s.e he
          (by intro v hv; simp [Move23Site.newTet₁, Move23Site.leftTet, Tet.verts] at hv ⊢; aesop))
        ⟨hpTau, by simpa using hp1⟩
  · rcases hmissing with hd | he
    · apply Or.inr
      simpa using tetBody_inter_subset_of_common_support (s.replace K) tau s.newTet₂ s.rightTet
        hm.2.1 h2 (common_support_subset_of_missing tau s.newTet₂ s.rightTet s.d hd
          (by intro v hv; simp [Move23Site.newTet₂, Move23Site.rightTet, Tet.verts] at hv ⊢; aesop))
        ⟨hpTau, by simpa using hp2⟩
    · apply Or.inl
      simpa using tetBody_inter_subset_of_common_support (s.replace K) tau s.newTet₂ s.leftTet
        hm.2.1 h2 (common_support_subset_of_missing tau s.newTet₂ s.leftTet s.e he
          (by intro v hv; simp [Move23Site.newTet₂, Move23Site.leftTet, Tet.verts] at hv ⊢; aesop))
        ⟨hpTau, by simpa using hp2⟩

theorem ClosedTriangulationCore.move23PiLocalHomeomorph_fixes_unchanged_source_overlap
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K)
    (p : ↥(move23PiSourceLocalCarrier s.a s.b s.c s.d s.e))
    (hpTau : p.1 ∈ triangulationTopologicalTetBody tau) :
    (move23PiLocalHomeomorph
      (hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2) p).1 = p.1 := by
  have hfive := hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2
  apply move23PiLocalHomeomorph_apply_eq_of_mem_target hfive p
  exact hcore.move23Site_unchangedTet_inter_source_subset_target s hlegal htau
    ⟨hpTau, p.2⟩

theorem ClosedTriangulationCore.move23PiLocalHomeomorph_symm_fixes_unchanged_target_overlap
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K)
    (q : ↥(move23PiTargetLocalCarrier s.a s.b s.c s.d s.e))
    (hqTau : q.1 ∈ triangulationTopologicalTetBody tau) :
    ((move23PiLocalHomeomorph
      (hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2)).symm q).1 = q.1 := by
  have hfive := hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2
  apply move23PiLocalHomeomorph_symm_apply_eq_of_mem_source hfive q
  exact hcore.move23Site_unchangedTet_inter_target_subset_source s hlegal htau
    ⟨hqTau, q.2⟩

noncomputable def Move23Site.unchangedGeometricCarrier
    (s : Move23Site) (K : Triangulation) : Set (Nat → ℝ) :=
  ⋃ (tau : Tet) (_ : tau ∈ s.unchangedTets K),
    triangulationTopologicalTetBody tau

theorem ClosedTriangulationCore.move23Site_unchangedCarrier_inter_source_subset_target
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    s.unchangedGeometricCarrier K ∩
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ⊆
      move23PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
  rintro p ⟨hp, hs⟩
  simp only [Move23Site.unchangedGeometricCarrier, mem_iUnion] at hp
  obtain ⟨tau, htau, hpTau⟩ := hp
  exact hcore.move23Site_unchangedTet_inter_source_subset_target s hlegal htau
    ⟨hpTau, hs⟩

theorem ClosedTriangulationCore.move23Site_unchangedCarrier_inter_target_subset_source
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    s.unchangedGeometricCarrier K ∩
        move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ⊆
      move23PiSourceLocalCarrier s.a s.b s.c s.d s.e := by
  rintro p ⟨hp, ht⟩
  simp only [Move23Site.unchangedGeometricCarrier, mem_iUnion] at hp
  obtain ⟨tau, htau, hpTau⟩ := hp
  exact hcore.move23Site_unchangedTet_inter_target_subset_source s hlegal htau
    ⟨hpTau, ht⟩

end Poincare
