import Poincare.Validity

namespace Poincare

/-- In a closed triangulation, a represented tetrahedron is determined by its
vertex set. -/
theorem ClosedTriangulationCore.eq_of_mem_of_sameTetVertices
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {τ ρ : Tet}
    (hτK : τ ∈ K.tets)
    (hρK : ρ ∈ K.tets)
    (hsame : SameTetVertices τ ρ) :
    τ = ρ := by
  have aux : ∀ {l : List Tet},
      l.Pairwise (fun α β => ¬ SameTetVertices α β) →
      ∀ {α β : Tet}, α ∈ l → β ∈ l → SameTetVertices α β → α = β := by
    intro l hp
    induction l with
    | nil => simp
    | cons σ t ih =>
        rw [List.pairwise_cons] at hp
        rcases hp with ⟨hσ, ht⟩
        intro α β hα hβ hab
        simp only [List.mem_cons] at hα hβ
        rcases hα with rfl | hαt <;> rcases hβ with rfl | hβt
        · rfl
        · exact False.elim (hσ β hβt hab)
        · exact False.elim (hσ α hαt (fun v => (hab v).symm))
        · exact ih ht hαt hβt hab
  exact aux hcore.2.1 hτK hρK hsame

/-- A tetrahedron with the same finite vertex support as a nondegenerate
tetrahedron is itself nondegenerate. -/
theorem Tet.verts_nodup_of_sameTetVertices
    {tau rho : Tet}
    (htau : tau.verts.Nodup)
    (hsame : SameTetVertices tau rho) :
    rho.verts.Nodup := by
  have hfin : tau.verts.toFinset = rho.verts.toFinset := by
    ext v
    simpa using hsame v
  have hcard : rho.verts.toFinset.card = rho.verts.length := by
    rw [← hfin, List.toFinset_card_of_nodup htau]
    simp [Tet.verts]
  have hmulti : (↑rho.verts : Multiset Nat).Nodup := by
    apply (Multiset.toFinset_card_eq_card_iff_nodup).1
    simpa using hcard
  simpa using hmulti

/-- In a closed triangulation, represented `2-3` source tetrahedra and absence
of the proposed new edge force all five raw vertices to be distinct. -/
theorem ClosedTriangulationCore.fiveVertexNodup_of_move23_rawData
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (a b c d e : Nat)
    (hleft :
      ∃ tauL : Tet,
        tauL ∈ K.tets ∧
        SameTetVertices tauL ⟨a, b, c, d⟩)
    (hright :
      ∃ tauR : Tet,
        tauR ∈ K.tets ∧
        SameTetVertices tauR ⟨a, b, c, e⟩)
    (hnewEdge :
      ∀ tau ∈ K.tets,
        ¬ (d ∈ tau.verts ∧ e ∈ tau.verts)) :
    [a, b, c, d, e].Nodup := by
  rcases hleft with ⟨tauL, htauLK, hsameL⟩
  rcases hright with ⟨tauR, htauRK, hsameR⟩
  have hleftNodup : (⟨a, b, c, d⟩ : Tet).verts.Nodup :=
    Tet.verts_nodup_of_sameTetVertices (hcore.1 tauL htauLK) hsameL
  have hrightNodup : (⟨a, b, c, e⟩ : Tet).verts.Nodup :=
    Tet.verts_nodup_of_sameTetVertices (hcore.1 tauR htauRK) hsameR
  have hde : d ≠ e := by
    intro h
    subst e
    have hdRaw : d ∈ (⟨a, b, c, d⟩ : Tet).verts := by
      simp [Tet.verts]
    have hdTau : d ∈ tauL.verts := (hsameL d).2 hdRaw
    exact hnewEdge tauL htauLK ⟨hdTau, hdTau⟩
  simp [Tet.verts] at hleftNodup hrightNodup ⊢
  aesop

/-- At a realized closed-core `2-3` site with absent new edge, the site's
five-way distinctness follows without using its stored distinctness field. -/
theorem ClosedTriangulationCore.move23Site_distinct_independent
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move23Site)
    (hrealized : s.RealizedIn K)
    (hnewEdge : s.NewEdgeAbsent K) :
    [s.a, s.b, s.c, s.d, s.e].Nodup := by
  exact hcore.fiveVertexNodup_of_move23_rawData
    s.a s.b s.c s.d s.e
    (by simpa [Move23Site.leftTet] using hrealized.1)
    (by simpa [Move23Site.rightTet] using hrealized.2)
    hnewEdge

/-- The two source tetrahedra at a legal `2-3` site have different represented
occurrences. -/
theorem ClosedTriangulationCore.move23Site_source_tets_ne
    {K : Triangulation}
    (_hcore : ClosedTriangulationCore K)
    (s : Move23Site)
    {τL τR : Tet}
    (_hτLK : τL ∈ K.tets)
    (hτL : SameTetVertices τL s.leftTet)
    (_hτRK : τR ∈ K.tets)
    (hτR : SameTetVertices τR s.rightTet) :
    τL ≠ τR := by
  intro heq
  subst τR
  apply s.leftTet_not_same_rightTet
  intro v
  exact (hτL v).symm.trans (hτR v)

/-- A legal `2-3` site in the current simple-complex representation supplies
the nondegenerate, uniquely represented local bistellar data. -/
theorem ClosedTriangulationCore.move23Site_simpleBistellarData
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move23Site)
    (hlegal : s.LegalIn K) :
    [s.a, s.b, s.c, s.d, s.e].Nodup ∧
    (∃! τL : Tet,
      τL ∈ K.tets ∧ SameTetVertices τL s.leftTet) ∧
    (∃! τR : Tet,
      τR ∈ K.tets ∧ SameTetVertices τR s.rightTet) ∧
    s.leftTet.verts.Nodup ∧
    s.rightTet.verts.Nodup ∧
    s.newTet₀.verts.Nodup ∧
    s.newTet₁.verts.Nodup ∧
    s.newTet₂.verts.Nodup := by
  have hfive :=
    hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2
  rcases hlegal.1 with ⟨⟨τL, hτLK, hτL⟩, ⟨τR, hτRK, hτR⟩⟩
  have hleftUnique :
      ∃! σ : Tet, σ ∈ K.tets ∧ SameTetVertices σ s.leftTet := by
    refine ⟨τL, ⟨hτLK, hτL⟩, ?_⟩
    intro σ hσ
    exact hcore.eq_of_mem_of_sameTetVertices hσ.1 hτLK
      (fun v => (hσ.2 v).trans (hτL v).symm)
  have hrightUnique :
      ∃! σ : Tet, σ ∈ K.tets ∧ SameTetVertices σ s.rightTet := by
    refine ⟨τR, ⟨hτRK, hτR⟩, ?_⟩
    intro σ hσ
    exact hcore.eq_of_mem_of_sameTetVertices hσ.1 hτRK
      (fun v => (hσ.2 v).trans (hτR v).symm)
  have hleft : s.leftTet.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.leftTet, Tet.verts] at hf ⊢
    aesop
  have hright : s.rightTet.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.rightTet, Tet.verts] at hf ⊢
    aesop
  have hnew0 : s.newTet₀.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.newTet₀, Tet.verts] at hf ⊢
    aesop
  have hnew1 : s.newTet₁.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.newTet₁, Tet.verts] at hf ⊢
    aesop
  have hnew2 : s.newTet₂.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.newTet₂, Tet.verts] at hf ⊢
    aesop
  exact ⟨hfive, hleftUnique, hrightUnique, hleft, hright,
    hnew0, hnew1, hnew2⟩

end Poincare
