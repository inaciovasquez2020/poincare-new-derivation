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

end Poincare
