import Poincare.TriangulationTopologicalGeometricCarrier
import Poincare.VertexLinkTetrahedronBridge
import Mathlib.Analysis.Convex.Join

open Set

namespace Poincare

/--
The represented vertex link realized in the same topology-bearing Pi-space as
the global triangulation.  Its filled faces are precisely the basis-vector
realizations of the represented `LinkTriangle`s at `v`.
-/
noncomputable def triangulationTopologicalVertexLink
    (K : Triangulation) (v : Nat) : Set (Nat → ℝ) :=
  ⋃ (σ : LinkTriangle) (_ : σ ∈ vertexLinkTriangles K v),
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑σ.verts.toFinset : Set Nat))

/-- Exact facewise membership in the global Pi-space vertex-link realization. -/
theorem mem_triangulationTopologicalVertexLink_iff
    (K : Triangulation) (v : Nat) (x : Nat → ℝ) :
    x ∈ triangulationTopologicalVertexLink K v ↔
      ∃ σ : LinkTriangle,
        σ ∈ vertexLinkTriangles K v ∧
        x ∈ convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑σ.verts.toFinset : Set Nat)) := by
  simp [triangulationTopologicalVertexLink]

/--
The Pi-space realization of every represented vertex link is genuinely a
subspace of the global geometric realization.
-/
theorem triangulationTopologicalVertexLink_subset_space
    (K : Triangulation) (v : Nat) :
    triangulationTopologicalVertexLink K v ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  intro x hx
  obtain ⟨σ, hσ, hxσ⟩ :=
    (mem_triangulationTopologicalVertexLink_iff K v x).1 hx
  obtain ⟨τ, hτK, hτσ⟩ :=
    (mem_vertexLinkTriangles_iff K v σ).1 hσ
  apply (mem_triangulationTopologicalGeometricCarrier_iff K x).2
  refine ⟨σ.verts.toFinset, ?_, ⟨τ, hτK, ?_⟩, hxσ⟩
  · exact ⟨σ.v0, by simp [LinkTriangle.verts]⟩
  · intro y hy
    exact List.mem_toFinset.mpr
      (τ.linkTriangleAt?_verts_subset v σ hτσ y
        (List.mem_toFinset.mp hy))

/--
Realize a represented abstract link vertex by the identically labelled basis
vertex in the ambient Pi-space of the global triangulation.
-/
noncomputable def vertexLinkTopologicalGeometricVertex
    (K : Triangulation) (v : Nat)
    (x : ↥((vertexLinkVertices K v).toFinset)) : Nat → ℝ :=
  triangulationTopologicalGeometricVertex x.1

/--
The represented abstract vertex link, realized facewise in the same Pi-space as
the global triangulation.  This deliberately remains distinct from the
Euclidean tetrahedron realization used to certify the two-sphere.
-/
noncomputable def vertexLinkTopologicalGeometricRealization
    (K : Triangulation) (v : Nat) : Set (Nat → ℝ) :=
  ⋃ (σ : LinkTriangle) (_ : σ ∈ vertexLinkTriangles K v),
    convexHull ℝ
      (vertexLinkTopologicalGeometricVertex K v ''
        {x : ↥((vertexLinkVertices K v).toFinset) | x.1 ∈ σ.verts})

/--
The abstract-link realization in the ambient Pi-space is exactly the link
subspace already embedded in the global realization.
-/
theorem vertexLinkTopologicalGeometricRealization_eq
    (K : Triangulation) (v : Nat) :
    vertexLinkTopologicalGeometricRealization K v =
      triangulationTopologicalVertexLink K v := by
  apply iUnion_congr
  intro σ
  apply iUnion_congr
  intro hσ
  congr 1
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, List.mem_toFinset.mpr hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hyList : y ∈ σ.verts := List.mem_toFinset.mp hy
    have hyV : y ∈ vertexLinkVertices K v :=
      (mem_vertexLinkVertices_iff K v y).2 ⟨σ, hσ, hyList⟩
    let x : ↥((vertexLinkVertices K v).toFinset) :=
      ⟨y, List.mem_toFinset.mpr hyV⟩
    exact ⟨x, hyList, rfl⟩

/-- Every non-apex point of a represented tetrahedron incident to `v`
decomposes along the ray from the represented vertex through the opposite
filled vertex-link face. -/
theorem triangulationTopologicalTetrahedron_exists_vertexLink_cone_decomposition
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (v : Nat) (τ : Tet) (hτ : τ ∈ K.tets) (hv : v ∈ τ.verts)
    (p : Nat → ℝ)
    (hp : p ∈ convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑τ.verts.toFinset : Set Nat)))
    (hpv : p v < 1) :
    0 ≤ p v ∧ p v < 1 ∧ 0 < 1 - p v ∧
      ∃ q : Nat → ℝ,
        q ∈ triangulationTopologicalVertexLink K v ∧
        q v = 0 ∧
        p = p v • triangulationTopologicalGeometricVertex v +
          (1 - p v) • q := by
  classical
  obtain ⟨σ, hσlink, hσextract⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem K v τ hτ hv
  have hτnodup : τ.verts.Nodup := hcore.1 τ hτ
  have hvnotσ : v ∉ σ.verts :=
    τ.linkTriangleAt?_vertex_not_mem v σ hτnodup hσextract
  let e := triangulationTopologicalGeometricVertex v
  let S : Set (Nat → ℝ) :=
    triangulationTopologicalGeometricVertex ''
      (↑σ.verts.toFinset : Set Nat)
  have hvertices :
      triangulationTopologicalGeometricVertex ''
          (↑τ.verts.toFinset : Set Nat) = insert e S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      by_cases hyv : y = v
      · left
        simpa [e, hyv]
      · right
        refine ⟨y, ?_, rfl⟩
        exact List.mem_toFinset.mpr
          ((τ.mem_linkTriangleAt?_iff v y σ hσextract hyv).2
            (List.mem_toFinset.mp hy))
    · rintro (hx | hx)
      · subst x
        exact ⟨v, List.mem_toFinset.mpr hv, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨y, List.mem_toFinset.mpr
          (τ.linkTriangleAt?_verts_subset v σ hσextract y
            (List.mem_toFinset.mp hy)), rfl⟩
  have hSnonempty : S.Nonempty := by
    refine ⟨triangulationTopologicalGeometricVertex σ.v0, ?_⟩
    exact ⟨σ.v0, by simp [LinkTriangle.verts], rfl⟩
  rw [hvertices, convexHull_insert hSnonempty] at hp
  obtain ⟨x, hx, q, hqS, hpseg⟩ := (mem_convexJoin.mp hp)
  have hxe : x = e := by simpa using hx
  subst x
  obtain ⟨a, b, ha, hb, hab, hpab⟩ := hpseg
  have hqv : q v = 0 := by
    apply convexHull_min _ (convex_hyperplane
      ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hqS
    rintro _ ⟨y, hy, rfl⟩
    have hyv : y ≠ v := by
      intro h
      subst y
      exact hvnotσ (List.mem_toFinset.mp hy)
    simp [triangulationTopologicalGeometricVertex, hyv]
  have hpva : p v = a := by
    rw [← hpab]
    simp [e, triangulationTopologicalGeometricVertex, hqv]
  have hpvnonneg : 0 ≤ p v := hpva.symm ▸ ha
  have hone : 0 < 1 - p v := sub_pos.mpr hpv
  refine ⟨hpvnonneg, hpv, hone, q, ?_, hqv, ?_⟩
  · exact (mem_triangulationTopologicalVertexLink_iff K v q).2
      ⟨σ, hσlink, hqS⟩
  · rw [hpva]
    have hba : b = 1 - a := by linarith
    rw [← hba]
    simpa [e] using hpab.symm

end Poincare
