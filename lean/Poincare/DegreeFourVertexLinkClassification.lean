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

end Poincare
