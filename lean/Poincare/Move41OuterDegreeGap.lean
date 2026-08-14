import Poincare.DegreeFourConnectedLinkClassification
import Poincare.GlobalPhiSupportDegreeGap

namespace Poincare

set_option maxHeartbeats 2000000

private theorem vertexLinkVertex_of_represented_tet
    {K : Triangulation} {v x : Nat} {tau : Tet}
    (htauK : tau ∈ K.tets) (hv : v ∈ tau.verts)
    (hx : x ∈ tau.verts) (hxv : x ≠ v) :
    x ∈ vertexLinkVertices K v := by
  obtain ⟨sigma, hsigma, hlink⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem K v tau htauK hv
  rw [mem_vertexLinkVertices_iff]
  exact ⟨sigma, hsigma,
    (tau.mem_linkTriangleAt?_iff v x sigma hlink hxv).2 hx⟩

/-- If an outer vertex of a legal `4 → 1` site had degree four, its
tetrahedral-boundary link would supply the forbidden opposite target
tetrahedron. -/
theorem ClosedTriangulationCore.move41Site_outer_vertexDegree_ne_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    vertexDegree K s.a ≠ 4 ∧
    vertexDegree K s.b ≠ 4 ∧
    vertexDegree K s.c ≠ 4 ∧
    vertexDegree K s.d ≠ 4 := by
  classical
  have represented (source : Tet) (hsource : source ∈ s.sourceTets) :
      ∃ tau ∈ K.tets, SameTetVertices tau source :=
    (s.sources_represented_of_exactlyOnce hlegal.sourceOccursExactlyOnce)
      source hsource
  have forceTarget (x p q r t : Nat)
      (hdist : [x, p, q, r, t].Nodup)
      (hdeg : vertexDegree K x = 4)
      (tauP tauT : Tet)
      (htauPK : tauP ∈ K.tets)
      (htauP : SameTetVertices tauP ⟨x, p, q, t⟩)
      (htauTK : tauT ∈ K.tets)
      (htauT : SameTetVertices tauT ⟨x, p, r, t⟩) :
      ∃ tau ∈ K.tets, SameTetVertices tau ⟨x, p, q, r⟩ := by
    have hd := hdist
    simp [Tet.verts] at hd
    have hxp : x ∈ tauP.verts := (htauP x).2 (by simp [Tet.verts])
    have hpP : p ∈ tauP.verts := (htauP p).2 (by simp [Tet.verts])
    have hqP : q ∈ tauP.verts := (htauP q).2 (by simp [Tet.verts])
    have htP : t ∈ tauP.verts := (htauP t).2 (by simp [Tet.verts])
    have hxT : x ∈ tauT.verts := (htauT x).2 (by simp [Tet.verts])
    have hrT : r ∈ tauT.verts := (htauT r).2 (by simp [Tet.verts])
    have hpLink := vertexLinkVertex_of_represented_tet htauPK hxp hpP (by aesop)
    have hqLink := vertexLinkVertex_of_represented_tet htauPK hxp hqP (by aesop)
    have htLink := vertexLinkVertex_of_represented_tet htauPK hxp htP (by aesop)
    have hrLink := vertexLinkVertex_of_represented_tet htauTK hxT hrT (by aesop)
    have hcert :=
      hcore.vertexLinkTetrahedralBoundaryCertificate_of_vertexDegree_eq_four
        x hdeg
    obtain ⟨sigma, hsigma, hverts⟩ :=
      (hcert.2.2.2.2.2 t htLink).exists
    obtain ⟨tau, htauK, hlink⟩ :=
      (mem_vertexLinkTriangles_iff K x sigma).1 hsigma
    refine ⟨tau, htauK, ?_⟩
    intro y
    have hxTau : x ∈ tau.verts :=
      (tau.linkTriangleAt?_isSome_iff x).1 (by rw [hlink]; rfl)
    by_cases hyx : y = x
    · subst y
      simpa [Tet.verts] using hxTau
    have hyiff := tau.mem_linkTriangleAt?_iff x y sigma hlink hyx
    rw [← hyiff, hverts]
    constructor
    · rintro ⟨hyLink, hyt⟩
      have hlen := hcert.1
      have hsubset : {p, q, r, t} ⊆ (vertexLinkVertices K x).toFinset := by
        simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
          List.mem_toFinset] using ⟨hpLink, hqLink, hrLink, htLink⟩
      have hall : (vertexLinkVertices K x).toFinset = {p, q, r, t} := by
        apply (Finset.eq_of_subset_of_card_le hsubset ?_).symm
        calc
          (vertexLinkVertices K x).toFinset.card ≤
              (vertexLinkVertices K x).length :=
            List.toFinset_card_le (vertexLinkVertices K x)
          _ = 4 := hlen
          _ = ({p, q, r, t} : Finset Nat).card := by simp [hd]
      have : y = p ∨ y = q ∨ y = r ∨ y = t := by
        have : y ∈ ({p, q, r, t} : Finset Nat) := by
          rw [← hall]
          exact List.mem_toFinset.mpr hyLink
        simpa using this
      rcases this with rfl | rfl | rfl | rfl
      · simp [Tet.verts]
      · simp [Tet.verts]
      · simp [Tet.verts]
      · exact (hyt rfl).elim
    · intro hy
      simp [Tet.verts, hyx] at hy
      rcases hy with (rfl | rfl | rfl)
      · exact ⟨hpLink, by aesop⟩
      · exact ⟨hqLink, by aesop⟩
      · exact ⟨hrLink, by aesop⟩
  have targetAbsent : ∀ tau ∈ K.tets, ¬ SameTetVertices tau s.targetTet :=
    hlegal.targetAbsent
  constructor
  · intro ha
    obtain ⟨t0, ht0K, ht0⟩ := represented s.sourceTet₀ (by simp [Move41Site.sourceTets])
    obtain ⟨t1, ht1K, ht1⟩ := represented s.sourceTet₁ (by simp [Move41Site.sourceTets])
    obtain ⟨tau, htauK, htau⟩ := forceTarget s.a s.b s.c s.d s.e
      s.distinct ha t0 t1 ht0K ht0 ht1K ht1
    exact targetAbsent tau htauK (by simpa [Move41Site.targetTet] using htau)
  · constructor
    · intro hb
      obtain ⟨t0, ht0K, ht0⟩ := represented s.sourceTet₀ (by simp [Move41Site.sourceTets])
      obtain ⟨t1, ht1K, ht1⟩ := represented s.sourceTet₁ (by simp [Move41Site.sourceTets])
      obtain ⟨tau, htauK, htau⟩ := forceTarget s.b s.a s.c s.d s.e
        (by have h := s.distinct; simp at h ⊢; omega) hb t0 t1
        ht0K (by intro z; have h := ht0 z; simp [Move41Site.sourceTet₀, Tet.verts] at h ⊢; aesop)
        ht1K (by intro z; have h := ht1 z; simp [Move41Site.sourceTet₁, Tet.verts] at h ⊢; aesop)
      exact targetAbsent tau htauK (by
        intro z
        have h := htau z
        simp [Move41Site.targetTet, Tet.verts] at h ⊢
        aesop)
    · constructor
      · intro hc
        obtain ⟨t0, ht0K, ht0⟩ := represented s.sourceTet₀ (by simp [Move41Site.sourceTets])
        obtain ⟨t2, ht2K, ht2⟩ := represented s.sourceTet₂ (by simp [Move41Site.sourceTets])
        obtain ⟨tau, htauK, htau⟩ := forceTarget s.c s.a s.b s.d s.e
          (by have h := s.distinct; simp at h ⊢; omega) hc t0 t2
          ht0K (by intro z; have h := ht0 z; simp [Move41Site.sourceTet₀, Tet.verts] at h ⊢; aesop)
          ht2K (by intro z; have h := ht2 z; simp [Move41Site.sourceTet₂, Tet.verts] at h ⊢; aesop)
        exact targetAbsent tau htauK (by
          intro z
          have h := htau z
          simp [Move41Site.targetTet, Tet.verts] at h ⊢
          aesop)
      · intro hdg
        obtain ⟨t1, ht1K, ht1⟩ := represented s.sourceTet₁ (by simp [Move41Site.sourceTets])
        obtain ⟨t2, ht2K, ht2⟩ := represented s.sourceTet₂ (by simp [Move41Site.sourceTets])
        obtain ⟨tau, htauK, htau⟩ := forceTarget s.d s.a s.b s.c s.e
          (by have h := s.distinct; simp at h ⊢; omega) hdg t1 t2
          ht1K (by intro z; have h := ht1 z; simp [Move41Site.sourceTet₁, Tet.verts] at h ⊢; aesop)
          ht2K (by intro z; have h := ht2 z; simp [Move41Site.sourceTet₂, Tet.verts] at h ⊢; aesop)
        exact targetAbsent tau htauK (by
          intro z
          have h := htau z
          simp [Move41Site.targetTet, Tet.verts] at h ⊢
          aesop)

/-- The closed-core degree gap therefore puts every outer vertex of a legal
`4 → 1` site in the high-degree branch required by strict descent. -/
theorem ClosedTriangulationCore.move41Site_outer_vertexDegree_ge_six
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    6 ≤ vertexDegree K s.a ∧ 6 ≤ vertexDegree K s.b ∧
    6 ≤ vertexDegree K s.c ∧ 6 ≤ vertexDegree K s.d := by
  have hne := hcore.move41Site_outer_vertexDegree_ne_four s hlegal
  have hsupp :
      s.a ∈ vertexSupport K ∧ s.b ∈ vertexSupport K ∧
      s.c ∈ vertexSupport K ∧ s.d ∈ vertexSupport K := by
    obtain ⟨t0, ht0K, ht0⟩ :=
      (s.sources_represented_of_exactlyOnce hlegal.sourceOccursExactlyOnce)
        s.sourceTet₀ (by simp [Move41Site.sourceTets])
    obtain ⟨t1, ht1K, ht1⟩ :=
      (s.sources_represented_of_exactlyOnce hlegal.sourceOccursExactlyOnce)
        s.sourceTet₁ (by simp [Move41Site.sourceTets])
    have mem (v : Nat) (tau : Tet) (htauK : tau ∈ K.tets)
        (hv : v ∈ tau.verts) : v ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      exact List.mem_flatMap.mpr ⟨tau, htauK, hv⟩
    exact ⟨mem s.a t0 ht0K ((ht0 s.a).2 (by simp [Move41Site.sourceTet₀, Tet.verts])),
      mem s.b t0 ht0K ((ht0 s.b).2 (by simp [Move41Site.sourceTet₀, Tet.verts])),
      mem s.c t0 ht0K ((ht0 s.c).2 (by simp [Move41Site.sourceTet₀, Tet.verts])),
      mem s.d t1 ht1K ((ht1 s.d).2 (by simp [Move41Site.sourceTet₁, Tet.verts]))⟩
  rcases hcore.vertexDegree_eq_four_or_ge_six_of_mem_vertexSupport hsupp.1 with h | h
  · exact (hne.1 h).elim
  · refine ⟨h, ?_⟩
    rcases hcore.vertexDegree_eq_four_or_ge_six_of_mem_vertexSupport hsupp.2.1 with h | h
    · exact (hne.2.1 h).elim
    · refine ⟨h, ?_⟩
      rcases hcore.vertexDegree_eq_four_or_ge_six_of_mem_vertexSupport hsupp.2.2.1 with h | h
      · exact (hne.2.2.1 h).elim
      · refine ⟨h, ?_⟩
        rcases hcore.vertexDegree_eq_four_or_ge_six_of_mem_vertexSupport hsupp.2.2.2 with h | h
        · exact (hne.2.2.2 h).elim
        · exact h

end Poincare
