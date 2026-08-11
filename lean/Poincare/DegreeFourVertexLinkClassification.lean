import Poincare.Move41TopologyPreservingDescent
import Poincare.VertexLink

namespace Poincare

/-- A degree-four vertex in a closed triangulation core has the complete
tetrahedral-boundary link certificate. -/
theorem ClosedTriangulationCore.vertexLinkTetrahedralBoundaryCertificate_of_vertexDegree_eq_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hdegree : vertexDegree K v = 4) :
    VertexLinkTetrahedralBoundaryCertificate K hcore v := by
  apply vertexLinkTetrahedralBoundaryCertificate_of_vertexDefect_zero
  · simp [vertexDefect, targetDegree, hdegree]
  · intro x hrepresented
    exact hcore.vertexLinkStarDegreeTwo hrepresented

/-- A degree-four supported star has four concrete, pairwise distinct outer
labels, all distinct from its center.  They are packaged in the label shape
used by a genuine `Move41Site`; legality is deliberately not asserted here. -/
theorem ClosedTriangulationCore.exists_move41Site_labels_of_vertexDegree_eq_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hdegree : vertexDegree K v = 4) :
    ∃ s : Move41Site,
      s.e = v ∧
      ∀ x : Nat,
        x ∈ vertexLinkVertices K v ↔
          x = s.a ∨ x = s.b ∨ x = s.c ∨ x = s.d := by
  classical
  let hcert :=
    hcore.vertexLinkTetrahedralBoundaryCertificate_of_vertexDegree_eq_four
      v hdegree
  let equiv := vertexLinkVertexEquivFin4 K hcore v hcert
  let a := (equiv.symm 0).1
  let b := (equiv.symm 1).1
  let c := (equiv.symm 2).1
  let d := (equiv.symm 3).1
  have houter (i : Fin 4) : (equiv.symm i).1 ∈ vertexLinkVertices K v := by
    exact List.mem_toFinset.mp (equiv.symm i).2
  have hcenter (i : Fin 4) : (equiv.symm i).1 ≠ v := by
    intro heq
    obtain ⟨σ, hσ, hiσ⟩ :=
      (mem_vertexLinkVertices_iff K v _).1 (houter i)
    obtain ⟨τ, hτK, hlink⟩ :=
      (mem_vertexLinkTriangles_iff K v σ).1 hσ
    have hτnodup := hcore.1 τ hτK
    unfold Tet.linkTriangleAt? at hlink
    split at hlink <;> rename_i h0
    · subst v
      cases hlink
      simp [LinkTriangle.verts, Tet.verts] at hτnodup hiσ heq
      aesop
    · split at hlink <;> rename_i h1
      · subst v
        cases hlink
        simp [LinkTriangle.verts, Tet.verts] at hτnodup hiσ heq
        aesop
      · split at hlink <;> rename_i h2
        · subst v
          cases hlink
          simp [LinkTriangle.verts, Tet.verts] at hτnodup hiσ heq
          aesop
        · split at hlink <;> rename_i h3
          · subst v
            cases hlink
            simp [LinkTriangle.verts, Tet.verts] at hτnodup hiσ heq
            aesop
          · simp at hlink
  have hdistinct (i j : Fin 4) (hij : i ≠ j) :
      (equiv.symm i).1 ≠ (equiv.symm j).1 := by
    intro heq
    apply hij
    apply equiv.symm.injective
    exact Subtype.ext heq
  have hnodup : [a, b, c, d, v].Nodup := by
    simp [a, b, c, d,
      hdistinct 0 1 (by decide), hdistinct 0 2 (by decide),
      hdistinct 0 3 (by decide), hdistinct 1 2 (by decide),
      hdistinct 1 3 (by decide), hdistinct 2 3 (by decide),
      hcenter 0, hcenter 1, hcenter 2, hcenter 3]
  let s : Move41Site := ⟨a, b, c, d, v, hnodup⟩
  refine ⟨s, rfl, ?_⟩
  intro x
  constructor
  · intro hx
    let y : ↥((vertexLinkVertices K v).toFinset) :=
      ⟨x, List.mem_toFinset.mpr hx⟩
    have hy : equiv y = 0 ∨ equiv y = 1 ∨ equiv y = 2 ∨ equiv y = 3 := by
      omega
    rcases hy with hy | hy | hy | hy
    · left
      change x = a
      have := congrArg equiv.symm hy
      simpa [a, y] using congrArg Subtype.val this
    · right; left
      change x = b
      have := congrArg equiv.symm hy
      simpa [b, y] using congrArg Subtype.val this
    · right; right; left
      change x = c
      have := congrArg equiv.symm hy
      simpa [c, y] using congrArg Subtype.val this
    · right; right; right
      change x = d
      have := congrArg equiv.symm hy
      simpa [d, y] using congrArg Subtype.val this
  · rintro (rfl | rfl | rfl | rfl) <;>
      exact houter _

private theorem exists_move41_source_of_center_mem_of_outer_cover
    (s : Move41Site) (tau : Tet)
    (htau : tau.verts.Nodup)
    (he : s.e ∈ tau.verts)
    (hcover : ∀ x ∈ tau.verts, x ≠ s.e →
      x = s.a ∨ x = s.b ∨ x = s.c ∨ x = s.d) :
    ∃ source ∈ s.sourceTets, SameTetVertices tau source := by
  classical
  let T : Finset Nat := tau.verts.toFinset
  let U : Finset Nat := [s.a, s.b, s.c, s.d, s.e].toFinset
  have hs := s.distinct
  simp at hs
  have hTcard : T.card = 4 := by
    simpa [T, Tet.verts] using List.toFinset_card_of_nodup htau
  have hUcard : U.card = 5 := by
    simpa [U] using List.toFinset_card_of_nodup s.distinct
  have hTU : T ⊆ U := by
    intro x hx
    have hxtau : x ∈ tau.verts := by simpa [T] using hx
    by_cases hxe : x = s.e
    · simp [U, hxe]
    · rcases hcover x hxtau hxe with rfl | rfl | rfl | rfl <;> simp [U]
  have hdiffcard : (U \ T).card = 1 := by
    rw [Finset.card_sdiff_of_subset hTU, hUcard, hTcard]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiffcard
  have hxmem : x ∈ U \ T := by simp [hx]
  have hxU : x ∈ U := by
    exact (Finset.mem_sdiff.mp hxmem).1
  have hxT : x ∉ T := by
    exact (Finset.mem_sdiff.mp hxmem).2
  have heT : s.e ∈ T := by simpa [T] using he
  have hxe : x ≠ s.e := by
    intro h
    subst x
    exact hxT heT
  have hUT : U.erase x = T := by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      by_contra hyT
      have : y ∈ U \ T :=
        Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hy).2, hyT⟩
      have hyx : y = x := by simpa [hx] using this
      exact (Finset.mem_erase.mp hy).1 hyx
    · intro hyT
      exact Finset.mem_erase.mpr ⟨fun hyx ↦ hxT (hyx ▸ hyT), hTU hyT⟩
  have hxlabels : x = s.a ∨ x = s.b ∨ x = s.c ∨ x = s.d := by
    simpa [U, hxe] using hxU
  rcases hxlabels with rfl | rfl | rfl | rfl
  · refine ⟨s.sourceTet₃, by simp [Move41Site.sourceTets], ?_⟩
    intro y
    have hy := Finset.ext_iff.mp hUT.symm y
    simp [T, U, Move41Site.sourceTet₃, Tet.verts] at hy ⊢
    aesop
  · refine ⟨s.sourceTet₂, by simp [Move41Site.sourceTets], ?_⟩
    intro y
    have hy := Finset.ext_iff.mp hUT.symm y
    simp [T, U, Move41Site.sourceTet₂, Tet.verts] at hy ⊢
    aesop
  · refine ⟨s.sourceTet₁, by simp [Move41Site.sourceTets], ?_⟩
    intro y
    have hy := Finset.ext_iff.mp hUT.symm y
    simp [T, U, Move41Site.sourceTet₁, Tet.verts] at hy ⊢
    aesop
  · refine ⟨s.sourceTet₀, by simp [Move41Site.sourceTets], ?_⟩
    intro y
    have hy := Finset.ext_iff.mp hUT.symm y
    simp [T, U, Move41Site.sourceTet₀, Tet.verts] at hy ⊢
    aesop

/-- The four labels extracted from a degree-four vertex saturate its entire
tetrahedron star. -/
theorem ClosedTriangulationCore.exists_move41Site_centerSaturated_of_vertexDegree_eq_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hdegree : vertexDegree K v = 4) :
    ∃ s : Move41Site,
      s.e = v ∧
      ∀ tau ∈ K.tets, s.e ∈ tau.verts →
        ∃ source ∈ s.sourceTets, SameTetVertices tau source := by
  classical
  obtain ⟨s, hse, hlabels⟩ :=
    hcore.exists_move41Site_labels_of_vertexDegree_eq_four v hdegree
  refine ⟨s, hse, ?_⟩
  intro tau htauK he
  apply exists_move41_source_of_center_mem_of_outer_cover s tau
    (hcore.1 tau htauK) he
  intro x hxtau hxe
  obtain ⟨sigma, hsigma, hlink⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem K v tau htauK (hse ▸ he)
  have hxsigma : x ∈ sigma.verts :=
    (tau.mem_linkTriangleAt?_iff v x sigma hlink (by simpa [hse] using hxe)).2 hxtau
  have hxvertices : x ∈ vertexLinkVertices K v :=
    (mem_vertexLinkVertices_iff K v x).2 ⟨sigma, hsigma, hxsigma⟩
  exact (hlabels x).1 hxvertices

/-- The saturated degree-four star has the four pairwise distinct source
tetrahedron vertex sets required by genuine `Move41` legality. -/
theorem ClosedTriangulationCore.exists_move41Site_centerSaturated_pairwise_of_vertexDegree_eq_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hdegree : vertexDegree K v = 4) :
    ∃ s : Move41Site,
      s.e = v ∧
      s.sourceTets.Pairwise (fun tau sigma => ¬ SameTetVertices tau sigma) ∧
      ∀ tau ∈ K.tets, s.e ∈ tau.verts →
        ∃ source ∈ s.sourceTets, SameTetVertices tau source := by
  obtain ⟨s, hse, hsaturated⟩ :=
    hcore.exists_move41Site_centerSaturated_of_vertexDegree_eq_four v hdegree
  refine ⟨s, hse, ?_, hsaturated⟩
  have hd := s.distinct
  simp [Move41Site.sourceTets, Move41Site.sourceTet₀, Move41Site.sourceTet₁,
    Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts] at hd ⊢
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro h
    have := (h s.c).1 (by simp [Move41Site.sourceTet₀, Tet.verts])
    simp [Move41Site.sourceTet₁, Tet.verts] at this
    aesop
  · intro h
    have := (h s.b).1 (by simp [Move41Site.sourceTet₀, Tet.verts])
    simp [Move41Site.sourceTet₂, Tet.verts] at this
    aesop
  · intro h
    have := (h s.a).1 (by simp [Move41Site.sourceTet₀, Tet.verts])
    simp [Move41Site.sourceTet₃, Tet.verts] at this
    aesop
  · intro h
    have := (h s.b).1 (by simp [Move41Site.sourceTet₁, Tet.verts])
    simp [Move41Site.sourceTet₂, Tet.verts] at this
    aesop
  · intro h
    have := (h s.a).1 (by simp [Move41Site.sourceTet₁, Tet.verts])
    simp [Move41Site.sourceTet₃, Tet.verts] at this
    aesop
  · intro h
    have := (h s.a).1 (by simp [Move41Site.sourceTet₂, Tet.verts])
    simp [Move41Site.sourceTet₃, Tet.verts] at this
    aesop

/-- Every one of the four source vertex sets extracted from a degree-four
vertex is represented by a tetrahedron of the triangulation. -/
theorem ClosedTriangulationCore.exists_move41Site_sources_of_vertexDegree_eq_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hdegree : vertexDegree K v = 4) :
    ∃ s : Move41Site,
      s.e = v ∧
      ∀ source ∈ s.sourceTets,
        ∃ tau ∈ K.tets, SameTetVertices tau source := by
  classical
  obtain ⟨s, hse, hlabels⟩ :=
    hcore.exists_move41Site_labels_of_vertexDegree_eq_four v hdegree
  have hcert :=
    hcore.vertexLinkTetrahedralBoundaryCertificate_of_vertexDegree_eq_four
      v hdegree
  refine ⟨s, hse, ?_⟩
  intro source hsource
  simp [Move41Site.sourceTets] at hsource
  rcases hsource with rfl | rfl | rfl | rfl
  · have hdlink : s.d ∈ vertexLinkVertices K v :=
      (hlabels s.d).2 (by aesop)
    obtain ⟨sigma, hsigma, hverts⟩ := (hcert.2.2.2.2.2 s.d hdlink).exists
    obtain ⟨tau, htau, hlink⟩ :=
      (mem_vertexLinkTriangles_iff K v sigma).1 hsigma
    refine ⟨tau, htau, ?_⟩
    intro x
    have he : v ∈ tau.verts :=
      (tau.linkTriangleAt?_isSome_iff v).1 (by rw [hlink]; rfl)
    by_cases hxv : x = v
    · subst x
      simpa [Move41Site.sourceTet₀, Tet.verts, hse] using he
    · have hxiff := tau.mem_linkTriangleAt?_iff v x sigma hlink hxv
      rw [← hxiff, hverts x, hlabels x]
      have hd := s.distinct
      simp [Move41Site.sourceTet₀, Tet.verts] at hd ⊢
      omega
  · have hclink : s.c ∈ vertexLinkVertices K v :=
      (hlabels s.c).2 (by aesop)
    obtain ⟨sigma, hsigma, hverts⟩ := (hcert.2.2.2.2.2 s.c hclink).exists
    obtain ⟨tau, htau, hlink⟩ :=
      (mem_vertexLinkTriangles_iff K v sigma).1 hsigma
    refine ⟨tau, htau, ?_⟩
    intro x
    have he : v ∈ tau.verts :=
      (tau.linkTriangleAt?_isSome_iff v).1 (by rw [hlink]; rfl)
    by_cases hxv : x = v
    · subst x
      simpa [Move41Site.sourceTet₁, Tet.verts, hse] using he
    · have hxiff := tau.mem_linkTriangleAt?_iff v x sigma hlink hxv
      rw [← hxiff, hverts x, hlabels x]
      have hd := s.distinct
      simp [Move41Site.sourceTet₁, Tet.verts] at hd ⊢
      omega
  · have hblink : s.b ∈ vertexLinkVertices K v :=
      (hlabels s.b).2 (by aesop)
    obtain ⟨sigma, hsigma, hverts⟩ := (hcert.2.2.2.2.2 s.b hblink).exists
    obtain ⟨tau, htau, hlink⟩ :=
      (mem_vertexLinkTriangles_iff K v sigma).1 hsigma
    refine ⟨tau, htau, ?_⟩
    intro x
    have he : v ∈ tau.verts :=
      (tau.linkTriangleAt?_isSome_iff v).1 (by rw [hlink]; rfl)
    by_cases hxv : x = v
    · subst x
      simpa [Move41Site.sourceTet₂, Tet.verts, hse] using he
    · have hxiff := tau.mem_linkTriangleAt?_iff v x sigma hlink hxv
      rw [← hxiff, hverts x, hlabels x]
      have hd := s.distinct
      simp [Move41Site.sourceTet₂, Tet.verts] at hd ⊢
      omega
  · have halink : s.a ∈ vertexLinkVertices K v :=
      (hlabels s.a).2 (by aesop)
    obtain ⟨sigma, hsigma, hverts⟩ := (hcert.2.2.2.2.2 s.a halink).exists
    obtain ⟨tau, htau, hlink⟩ :=
      (mem_vertexLinkTriangles_iff K v sigma).1 hsigma
    refine ⟨tau, htau, ?_⟩
    intro x
    have he : v ∈ tau.verts :=
      (tau.linkTriangleAt?_isSome_iff v).1 (by rw [hlink]; rfl)
    by_cases hxv : x = v
    · subst x
      simpa [Move41Site.sourceTet₃, Tet.verts, hse] using he
    · have hxiff := tau.mem_linkTriangleAt?_iff v x sigma hlink hxv
      rw [← hxiff, hverts x, hlabels x]
      have hd := s.distinct
      simp [Move41Site.sourceTet₃, Tet.verts] at hd ⊢
      omega

/-- The four source vertex sets extracted at a degree-four vertex each occur
exactly once in the triangulation. -/
theorem ClosedTriangulationCore.exists_move41Site_sourcesExactlyOnce_of_vertexDegree_eq_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hdegree : vertexDegree K v = 4) :
    ∃ s : Move41Site,
      s.e = v ∧
      ∀ source ∈ s.sourceTets,
        (K.tets.filter (fun tau => sameTetVerticesBool tau source)).length = 1 := by
  classical
  obtain ⟨s, hse, hsources⟩ :=
    hcore.exists_move41Site_sources_of_vertexDegree_eq_four v hdegree
  refine ⟨s, hse, ?_⟩
  intro source hsource
  obtain ⟨tau, htauK, hsame⟩ := hsources source hsource
  have hunique := hcore.existsUnique_sameTetVertices
    ⟨tau, htauK, hsame⟩
  let L := K.tets.filter (fun rho => sameTetVerticesBool rho source)
  have htauL : tau ∈ L := by
    simp [L, htauK, sameTetVerticesBool_eq_true_iff, hsame]
  have hmem : ∀ rho, rho ∈ L ↔ rho = tau := by
    intro rho
    constructor
    · intro hrho
      have hrho' : rho ∈ K.tets ∧ SameTetVertices rho source := by
        simpa [L, sameTetVerticesBool_eq_true_iff] using hrho
      exact hunique.unique hrho' ⟨htauK, hsame⟩
    · rintro rfl
      exact htauL
  have hfinset : L.toFinset = {tau} := by
    ext rho
    simp [hmem]
  have hnodupK : K.tets.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hcore.2.1.imp (fun {x y} hxy hEq => by
      subst y
      exact hxy (sameTetVertices_refl x))
  have hnodupL : L.Nodup := by
    exact hnodupK.filter _
  change L.length = 1
  rw [← List.toFinset_card_of_nodup hnodupL, hfinset]
  simp

end Poincare
