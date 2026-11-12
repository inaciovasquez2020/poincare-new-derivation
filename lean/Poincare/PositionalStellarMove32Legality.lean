import Poincare.PositionalStellarOldEdgeIncidence
import Poincare.PositionalStellarOldFacePersistence
import Poincare.GlobalRepresentedEdgeIncidenceLowerBound
import Poincare.PositionStellarClosedCoreTransport

namespace Poincare

private theorem child_old_vertex (s : Move41Site) {τ : Tet} (hτ : τ ∈ s.sourceTets)
    {v : Nat} (hv : v ∈ τ.verts) (hne : v ≠ s.e) : v ∈ s.targetTet.verts := by
  simp only [Move41Site.sourceTets, List.mem_cons, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;>
    simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
      Move41Site.sourceTet₂, Move41Site.sourceTet₃, Move41Site.targetTet, Tet.verts] <;>
    aesop

/-- Immediately after a fresh positional 1→4 move, the legal 3→2 sites
are exactly the original sites whose shared edge is outside the six
edges of the selected tetrahedron. -/
theorem Move41Site.insertFreshAt_legal32_iff
    (s : Move41Site) (K : Triangulation) (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hcore : ClosedTriangulationCore K) (hfresh : s.e ∉ vertexSupport K)
    (m : Move32Site) :
    m.LegalIn (s.insertFreshAt K before after hsource hfresh) ↔
      m.LegalIn K ∧ ¬ (m.d ∈ s.targetTet.verts ∧ m.e ∈ s.targetTet.verts) := by
  let L := s.insertFreshAt K before after hsource hfresh
  change m.LegalIn L ↔ _
  have htets : L.tets = before ++ s.sourceTets ++ after := rfl
  have hnewCore : ClosedTriangulationCore L :=
    s.insertFreshAt_closedCore K before after hsource hcore hfresh
  have htarget : s.targetTet ∈ K.tets := by
    rw [hsource]
    simp
  have hold (τ : Tet) (hτ : τ ∈ K.tets) (v : Nat) (hv : v ∈ τ.verts) :
      v ≠ s.e := by
    intro he
    subst v
    apply hfresh
    exact (mem_vertexSupport_iff K s.e).2
      (List.mem_flatMap.mpr ⟨τ, hτ, hv⟩)
  have hchild (τ : Tet) (hτ : τ ∈ L.tets) (hc : s.e ∈ τ.verts) :
      τ ∈ s.sourceTets := by
    rw [htets, List.mem_append, List.mem_append] at hτ
    rcases hτ with (hb | hs) | ha
    · exact (hold τ (by rw [hsource]; exact List.mem_append.mpr (Or.inl hb))
        s.e hc rfl).elim
    · exact hs
    · exact (hold τ (by rw [hsource]; simp [ha]) s.e hc rfl).elim
  have hregion (σ : Tet) (hd : m.d ∈ σ.verts) (he : m.e ∈ σ.verts)
      (hdf : m.d ≠ s.e) (hef : m.e ≠ s.e)
      (hout : ¬ (m.d ∈ s.targetTet.verts ∧ m.e ∈ s.targetTet.verts)) :
      (∃ τ ∈ L.tets, SameTetVertices τ σ) ↔
        (∃ τ ∈ K.tets, SameTetVertices τ σ) := by
    constructor
    · rintro ⟨τ, hτ, hs⟩
      rw [htets, List.mem_append, List.mem_append] at hτ
      rcases hτ with (hb | hc) | ha
      · exact ⟨τ, by rw [hsource]; exact List.mem_append.mpr (Or.inl hb), hs⟩
      · exact (hout ⟨child_old_vertex s hc ((hs m.d).2 hd) hdf,
          child_old_vertex s hc ((hs m.e).2 he) hef⟩).elim
      · exact ⟨τ, by rw [hsource]; simp [ha], hs⟩
    · rintro ⟨τ, hτ, hs⟩
      rw [hsource, List.mem_append, List.mem_cons] at hτ
      rcases hτ with hb | rfl | ha
      · exact ⟨τ, by rw [htets]; simp [hb], hs⟩
      · exact (hout ⟨(hs m.d).2 hd, (hs m.e).2 he⟩).elim
      · exact ⟨τ, by rw [htets]; simp [ha], hs⟩
  have hrealized (hdf : m.d ≠ s.e) (hef : m.e ≠ s.e)
      (hout : ¬ (m.d ∈ s.targetTet.verts ∧ m.e ∈ s.targetTet.verts)) :
      m.RealizedIn L ↔ m.RealizedIn K := by
    unfold Move32Site.RealizedIn
    rw [hregion m.targetTet₀ (by simp [Move32Site.targetTet₀, Tet.verts])
          (by simp [Move32Site.targetTet₀, Tet.verts]) hdf hef hout,
        hregion m.targetTet₁ (by simp [Move32Site.targetTet₁, Tet.verts])
          (by simp [Move32Site.targetTet₁, Tet.verts]) hdf hef hout,
        hregion m.targetTet₂ (by simp [Move32Site.targetTet₂, Tet.verts])
          (by simp [Move32Site.targetTet₂, Tet.verts]) hdf hef hout]
  have hcount (hdf : m.d ≠ s.e) (hef : m.e ≠ s.e) (hde : m.d ≠ m.e) :
      (L.tets.filter (fun τ => m.d ∈ τ.verts ∧ m.e ∈ τ.verts)).length =
        (K.tets.filter (fun τ => m.d ∈ τ.verts ∧ m.e ∈ τ.verts)).length +
          (if m.d ∈ s.targetTet.verts ∧ m.e ∈ s.targetTet.verts then 1 else 0) :=
    s.insertFreshAt_old_edge_count K before after hsource hfresh m.d m.e hdf hef hde
  constructor
  · intro hl
    have habs : m.SourceFaceAbsent K :=
      s.insertFreshAt_sourceFaceAbsent_implies_original m K before after hsource hfresh hl.2.2
    have hn := hnewCore.move32Site_distinct m hl.1
    have hdistinct : m.a ≠ m.d ∧ m.b ≠ m.d ∧ m.c ≠ m.d ∧
        m.a ≠ m.e ∧ m.b ≠ m.e ∧ m.c ≠ m.e ∧ m.d ≠ m.e := by
      simp at hn
      aesop
    obtain ⟨⟨τ₀, ht₀, hs₀⟩, ⟨τ₁, ht₁, hs₁⟩, _⟩ := hl.1
    have hspoke (hd : m.d = s.e ∨ m.e = s.e) : False := by
      have hcenter₀ : s.e ∈ τ₀.verts := (hs₀ s.e).2 (by
        rcases hd with hd | he
        · rw [← hd]; simp [Move32Site.targetTet₀, Tet.verts]
        · rw [← he]; simp [Move32Site.targetTet₀, Tet.verts])
      have hcenter₁ : s.e ∈ τ₁.verts := (hs₁ s.e).2 (by
        rcases hd with hd | he
        · rw [← hd]; simp [Move32Site.targetTet₁, Tet.verts]
        · rw [← he]; simp [Move32Site.targetTet₁, Tet.verts])
      have ha : m.a ≠ s.e := by rcases hd with hd | he <;> aesop
      have hb : m.b ≠ s.e := by rcases hd with hd | he <;> aesop
      have hc : m.c ≠ s.e := by rcases hd with hd | he <;> aesop
      exact habs s.targetTet htarget
        ⟨child_old_vertex s (hchild τ₀ ht₀ hcenter₀)
            ((hs₀ m.a).2 (by simp [Move32Site.targetTet₀, Tet.verts])) ha,
         child_old_vertex s (hchild τ₀ ht₀ hcenter₀)
            ((hs₀ m.b).2 (by simp [Move32Site.targetTet₀, Tet.verts])) hb,
         child_old_vertex s (hchild τ₁ ht₁ hcenter₁)
            ((hs₁ m.c).2 (by simp [Move32Site.targetTet₁, Tet.verts])) hc⟩
    have hdf : m.d ≠ s.e := fun hd => hspoke (Or.inl hd)
    have hef : m.e ≠ s.e := fun he => hspoke (Or.inr he)
    have hde := hdistinct.2.2.2.2.2.2
    have heq := hcount hdf hef hde
    have hthree := hl.2.1
    change (L.tets.filter (fun τ => m.d ∈ τ.verts ∧ m.e ∈ τ.verts)).length = 3 at hthree
    have hout : ¬ (m.d ∈ s.targetTet.verts ∧ m.e ∈ s.targetTet.verts) := by
      intro hin
      have hpos : 0 < (K.tets.filter
          (fun τ => m.d ∈ τ.verts ∧ m.e ∈ τ.verts)).length :=
        List.length_pos_iff_exists_mem.mpr ⟨s.targetTet, by simp [htarget, hin]⟩
      have hmin := hcore.edgeIncidence_three_le_of_pos m.d m.e hde hpos
      rw [if_pos hin, hthree] at heq
      omega
    exact ⟨⟨(hrealized hdf hef hout).1 hl.1, by
      simpa [Move32Site.SharedEdgeExactlyThree, hout, hthree] using heq.symm, habs⟩, hout⟩
  · rintro ⟨hk, hout⟩
    obtain ⟨⟨τ₀, ht₀, hs₀⟩, ⟨τ₁, ht₁, hs₁⟩, _⟩ := hk.1
    have hdf := hold τ₀ ht₀ m.d ((hs₀ m.d).2 (by simp [Move32Site.targetTet₀, Tet.verts]))
    have hef := hold τ₀ ht₀ m.e ((hs₀ m.e).2 (by simp [Move32Site.targetTet₀, Tet.verts]))
    have hn := hcore.move32Site_distinct m hk.1
    have hde : m.d ≠ m.e := by
      simp at hn
      aesop
    have heq := hcount hdf hef hde
    have hthree := hk.2.1
    change (K.tets.filter (fun τ => m.d ∈ τ.verts ∧ m.e ∈ τ.verts)).length = 3 at hthree
    refine ⟨(hrealized hdf hef hout).2 hk.1, ?_, ?_⟩
    · simpa [Move32Site.SharedEdgeExactlyThree, hout, hthree] using heq
    · intro τ hτ hface
      rw [htets, List.mem_append, List.mem_append] at hτ
      rcases hτ with (hb | hc) | ha
      · exact hk.2.2 τ (by rw [hsource]; exact List.mem_append.mpr (Or.inl hb)) hface
      · have haf := hold τ₀ ht₀ m.a ((hs₀ m.a).2 (by simp [Move32Site.targetTet₀, Tet.verts]))
        have hbf := hold τ₀ ht₀ m.b ((hs₀ m.b).2 (by simp [Move32Site.targetTet₀, Tet.verts]))
        have hcf := hold τ₁ ht₁ m.c ((hs₁ m.c).2 (by simp [Move32Site.targetTet₁, Tet.verts]))
        exact hk.2.2 s.targetTet htarget
          ⟨child_old_vertex s hc hface.1 haf, child_old_vertex s hc hface.2.1 hbf,
            child_old_vertex s hc hface.2.2 hcf⟩
      · exact hk.2.2 τ (by rw [hsource]; simp [ha]) hface

end Poincare