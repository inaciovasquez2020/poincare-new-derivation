import Poincare.TriangulationTopologicalVertexLink

open Set

namespace Poincare

/--
The linear realization-change map from the global Pi-space to the certified
Euclidean realization of a vertex link.  Only the represented link-vertex
coordinates contribute.
-/
noncomputable def vertexLinkPiToEuclideanLinearMap
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v) :
    (Nat → ℝ) →ₗ[ℝ] TetrahedronAmbient where
  toFun p := ∑ x : ↥((vertexLinkVertices K v).toFinset),
    p x.1 • vertexLinkGeometricVertex K hcore v hcert x
  map_add' p q := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a p := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
      mul_smul, Finset.smul_sum]

@[simp]
theorem vertexLinkPiToEuclideanLinearMap_basisVertex
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v)
    (x : ↥((vertexLinkVertices K v).toFinset)) :
    vertexLinkPiToEuclideanLinearMap K hcore v hcert
        (vertexLinkTopologicalGeometricVertex K v x) =
      vertexLinkGeometricVertex K hcore v hcert x := by
  classical
  unfold vertexLinkPiToEuclideanLinearMap
  change (∑ y : ↥((vertexLinkVertices K v).toFinset),
      vertexLinkTopologicalGeometricVertex K v x y.1 •
        vertexLinkGeometricVertex K hcore v hcert y) = _
  rw [Fintype.sum_eq_single x]
  · simp [vertexLinkTopologicalGeometricVertex,
      triangulationTopologicalGeometricVertex]
  · intro y hyx
    simp [vertexLinkTopologicalGeometricVertex,
      triangulationTopologicalGeometricVertex, hyx]

/--
On every represented link triangle, the realization-change map sends the
Pi-space filled face exactly onto its certified Euclidean filled face.
-/
theorem vertexLinkPiToEuclideanLinearMap_image_face
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v)
    (sigma : LinkTriangle) (hsigma : sigma ∈ vertexLinkTriangles K v) :
    vertexLinkPiToEuclideanLinearMap K hcore v hcert ''
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑sigma.verts.toFinset : Set Nat)) =
      vertexLinkGeometricFace K hcore v hcert sigma := by
  classical
  rw [LinearMap.image_convexHull]
  unfold vertexLinkGeometricFace
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyV : y ∈ vertexLinkVertices K v :=
      (mem_vertexLinkVertices_iff K v y).2
        ⟨sigma, hsigma, List.mem_toFinset.mp hy⟩
    let x : ↥((vertexLinkVertices K v).toFinset) :=
      ⟨y, List.mem_toFinset.mpr hyV⟩
    refine ⟨x, List.mem_toFinset.mp hy, ?_⟩
    change vertexLinkGeometricVertex K hcore v hcert x =
      vertexLinkPiToEuclideanLinearMap K hcore v hcert
        (vertexLinkTopologicalGeometricVertex K v x)
    exact (vertexLinkPiToEuclideanLinearMap_basisVertex
      K hcore v hcert x).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨vertexLinkTopologicalGeometricVertex K v x, ?_, ?_⟩
    · exact ⟨x.1, List.mem_toFinset.mpr hx, rfl⟩
    · exact vertexLinkPiToEuclideanLinearMap_basisVertex K hcore v hcert x

/--
The realization-change map sends the complete Pi-space vertex link exactly
onto the already certified Euclidean vertex-link realization.
-/
theorem vertexLinkPiToEuclideanLinearMap_image_realization
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v) :
    vertexLinkPiToEuclideanLinearMap K hcore v hcert ''
        triangulationTopologicalVertexLink K v =
      vertexLinkGeometricRealization K hcore v hcert := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨sigma, hsigma, hq⟩ :=
      (mem_triangulationTopologicalVertexLink_iff K v q).1 hq
    have hp : vertexLinkPiToEuclideanLinearMap K hcore v hcert q ∈
        vertexLinkPiToEuclideanLinearMap K hcore v hcert ''
          convexHull ℝ
            (triangulationTopologicalGeometricVertex ''
              (↑sigma.verts.toFinset : Set Nat)) := ⟨q, hq, rfl⟩
    rw [vertexLinkPiToEuclideanLinearMap_image_face
      K hcore v hcert sigma hsigma] at hp
    exact ⟨sigma, hsigma, hp⟩
  · rintro ⟨sigma, hsigma, hp⟩
    rw [← vertexLinkPiToEuclideanLinearMap_image_face
      K hcore v hcert sigma hsigma] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, ?_, rfl⟩
    exact (mem_triangulationTopologicalVertexLink_iff K v q).2
      ⟨sigma, hsigma, hq⟩

/--
The Pi-space realization of a represented vertex link is compact.  This is
the weakest topological input needed to upgrade the already constructed
realization-change bijection to a homeomorphism: the link is a finite union
of convex hulls of finite vertex sets.
-/
theorem triangulationTopologicalVertexLink_isCompact
    (K : Triangulation) (v : Nat) :
    IsCompact (triangulationTopologicalVertexLink K v) := by
  rw [triangulationTopologicalVertexLink]
  let f : LinkTriangle → Set (Nat → ℝ) := fun sigma ↦
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑sigma.verts.toFinset : Set Nat))
  change IsCompact (⋃ (sigma : LinkTriangle)
    (_ : sigma ∈ vertexLinkTriangles K v), f sigma)
  generalize vertexLinkTriangles K v = triangles
  induction triangles with
  | nil => simp
  | cons sigma triangles ih =>
      have hface : IsCompact (f sigma) :=
        (Set.toFinite
          (triangulationTopologicalGeometricVertex ''
            (↑sigma.verts.toFinset : Set Nat))).isCompact_convexHull ℝ
      have heq :
          (⋃ (tau : LinkTriangle) (_ : tau ∈ sigma :: triangles), f tau) =
            f sigma ∪
              (⋃ (tau : LinkTriangle) (_ : tau ∈ triangles), f tau) := by
        ext x
        simp
      rw [heq]
      exact hface.union ih

/-- Coordinates of a point of the Pi-space link sum to one over the represented
link vertices. -/
theorem triangulationTopologicalVertexLink_sum_coordinates
    (K : Triangulation) (v : Nat) (p : Nat → ℝ)
    (hp : p ∈ triangulationTopologicalVertexLink K v) :
    ∑ x : ↥((vertexLinkVertices K v).toFinset), p x.1 = 1 := by
  classical
  obtain ⟨sigma, hsigma, hp⟩ :=
    (mem_triangulationTopologicalVertexLink_iff K v p).1 hp
  apply convexHull_min _ (convex_hyperplane
    ⟨fun a b ↦ by simp [Finset.sum_add_distrib],
      fun a p ↦ by simp [Finset.mul_sum]⟩
    (1 : ℝ)) hp
  rintro _ ⟨y, hy, rfl⟩
  have hyV : y ∈ vertexLinkVertices K v :=
    (mem_vertexLinkVertices_iff K v y).2
      ⟨sigma, hsigma, List.mem_toFinset.mp hy⟩
  let x : ↥((vertexLinkVertices K v).toFinset) :=
    ⟨y, List.mem_toFinset.mpr hyV⟩
  change ∑ z : ↥((vertexLinkVertices K v).toFinset),
    triangulationTopologicalGeometricVertex y z.1 = 1
  rw [Fintype.sum_eq_single x]
  · simp [triangulationTopologicalGeometricVertex, x]
  · intro z hzx
    have hzy : z.1 ≠ y := by
      intro h
      apply hzx
      apply Subtype.ext
      exact h
    simp [triangulationTopologicalGeometricVertex, hzy]

/-- A point of the Pi-space link has zero coordinates away from its represented
link vertices. -/
theorem triangulationTopologicalVertexLink_coordinate_eq_zero
    (K : Triangulation) (v : Nat) (p : Nat → ℝ)
    (hp : p ∈ triangulationTopologicalVertexLink K v)
    (y : Nat) (hy : y ∉ vertexLinkVertices K v) :
    p y = 0 := by
  classical
  obtain ⟨sigma, hsigma, hp⟩ :=
    (mem_triangulationTopologicalVertexLink_iff K v p).1 hp
  apply convexHull_min _ (convex_hyperplane
    ⟨fun a b ↦ rfl, fun a p ↦ rfl⟩
    (0 : ℝ)) hp
  rintro _ ⟨z, hz, rfl⟩
  have hzy : z ≠ y := by
    intro h
    subst z
    exact hy ((mem_vertexLinkVertices_iff K v y).2
      ⟨sigma, hsigma, List.mem_toFinset.mp hz⟩)
  simp [triangulationTopologicalGeometricVertex, hzy]

/-- The realization-change linear map is injective on the represented
Pi-space vertex link. -/
theorem vertexLinkPiToEuclideanLinearMap_injOn
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v) :
    Set.InjOn (vertexLinkPiToEuclideanLinearMap K hcore v hcert)
      (triangulationTopologicalVertexLink K v) := by
  classical
  intro p hp q hq hpq
  have hpsum := triangulationTopologicalVertexLink_sum_coordinates K v p hp
  have hqsum := triangulationTopologicalVertexLink_sum_coordinates K v q hq
  have hcomb :
      Finset.univ.affineCombination ℝ
          (vertexLinkGeometricVertex K hcore v hcert)
          (fun x ↦ p x.1) =
        Finset.univ.affineCombination ℝ
          (vertexLinkGeometricVertex K hcore v hcert)
          (fun x ↦ q x.1) := by
    rw [Finset.affineCombination_eq_linear_combination
        Finset.univ _ _ (by simpa using hpsum),
      Finset.affineCombination_eq_linear_combination
        Finset.univ _ _ (by simpa using hqsum)]
    exact hpq
  have hind : AffineIndependent ℝ
      (vertexLinkGeometricVertex K hcore v hcert) := by
    unfold vertexLinkGeometricVertex
    exact tetrahedronSimplex.independent.comp_embedding
      (vertexLinkVertexEquivFin4 K hcore v hcert).toEmbedding
  have hweights : ∀ x : ↥((vertexLinkVertices K v).toFinset),
      p x.1 = q x.1 := by
    intro x
    exact (hind.affineCombination_eq_iff_eq
      (by simpa using hpsum) (by simpa using hqsum)).1 hcomb x (Finset.mem_univ x)
  funext y
  by_cases hy : y ∈ vertexLinkVertices K v
  · exact hweights ⟨y, List.mem_toFinset.mpr hy⟩
  · rw [triangulationTopologicalVertexLink_coordinate_eq_zero K v p hp y hy,
      triangulationTopologicalVertexLink_coordinate_eq_zero K v q hq y hy]

/-- The restriction of the realization-change map to the Pi-space link is
continuous. -/
theorem continuous_vertexLinkPiToEuclideanLinearMap
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v) :
    Continuous (vertexLinkPiToEuclideanLinearMap K hcore v hcert) := by
  unfold vertexLinkPiToEuclideanLinearMap
  change Continuous (fun p : Nat → ℝ ↦
    ∑ x : ↥((vertexLinkVertices K v).toFinset),
      p x.1 • vertexLinkGeometricVertex K hcore v hcert x)
  apply continuous_finset_sum Finset.univ
  intro x _
  exact (continuous_apply x.1 :
    Continuous (fun p : Nat → ℝ ↦ p x.1)).smul continuous_const

/-- The represented Pi-space vertex link is genuinely homeomorphic to its
already certified Euclidean realization. -/
noncomputable def vertexLinkPiRealizationHomeomorphEuclidean
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v) :
    ↥(triangulationTopologicalVertexLink K v) ≃ₜ
      ↥(vertexLinkGeometricRealization K hcore v hcert) := by
  let f : ↥(triangulationTopologicalVertexLink K v) →
      ↥(vertexLinkGeometricRealization K hcore v hcert) := fun p ↦
    ⟨vertexLinkPiToEuclideanLinearMap K hcore v hcert p.1,
      (vertexLinkPiToEuclideanLinearMap_image_realization
        K hcore v hcert) ▸ Set.mem_image_of_mem _ p.2⟩
  letI : CompactSpace ↥(triangulationTopologicalVertexLink K v) :=
    isCompact_iff_compactSpace.mp
      (triangulationTopologicalVertexLink_isCompact K v)
  have hfcont : Continuous f :=
    Continuous.subtype_mk
      ((continuous_vertexLinkPiToEuclideanLinearMap K hcore v hcert).comp
        continuous_subtype_val)
      _
  have hfinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact vertexLinkPiToEuclideanLinearMap_injOn K hcore v hcert
      p.2 q.2 (Subtype.ext_iff.mp hpq)
  have hfsurj : Function.Surjective f := by
    intro q
    have hq : q.1 ∈ vertexLinkPiToEuclideanLinearMap K hcore v hcert ''
        triangulationTopologicalVertexLink K v := by
      rw [vertexLinkPiToEuclideanLinearMap_image_realization K hcore v hcert]
      exact q.2
    obtain ⟨p, hp, hpq⟩ := hq
    refine ⟨⟨p, hp⟩, Subtype.ext ?_⟩
    exact hpq
  exact (IsHomeomorph.homeomorph f
    ((isHomeomorph_iff_continuous_bijective).2
      ⟨hfcont, hfinj, hfsurj⟩))

/--
The represented vertex link inside the global topology-bearing Pi-space is
homeomorphic to the unit two-sphere whenever the existing tetrahedral-boundary
certificate is supplied.  This composition keeps the Pi-space realization and
the independently certified Euclidean realization distinct.
-/
noncomputable def vertexLinkPiRealizationHomeomorphUnitSphere
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v) :
    ↥(triangulationTopologicalVertexLink K v) ≃ₜ
      ↥(Metric.sphere (0 : TetrahedronAmbient) 1) :=
  (vertexLinkPiRealizationHomeomorphEuclidean K hcore v hcert).trans
    (vertexLinkGeometricRealizationHomeomorphUnitSphere K hcore v hcert)

end Poincare
