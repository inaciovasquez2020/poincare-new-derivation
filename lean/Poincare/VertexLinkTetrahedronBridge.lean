import Poincare.VertexLink
import Poincare.TetrahedronSphere

open Set

namespace Poincare

/--
For each `Fin 4` label `i`, the unique certified complementary abstract
vertex-link face has the same vertex-label support as the geometric
tetrahedron face opposite `i`.

This is a support-level bridge between the combinatorial vertex-link
certificate and the geometric tetrahedron.  It does not yet construct a
topological realization of the whole abstract link.
-/
theorem vertexLinkComplementaryFace_matches_tetrahedronFacet
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert :
      VertexLinkTetrahedralBoundaryCertificate
        K hcore v)
    (i : Fin 4) :
    ∃ σ : LinkTriangle,
      σ ∈ vertexLinkTriangles K v ∧
      (∀ y : Nat,
        y ∈ σ.verts ↔
          y ∈ vertexLinkVertices K v ∧
            y ≠
              ((vertexLinkVertexEquivFin4
                K hcore v hcert).symm i).1) ∧
      vertexLinkFaceLabelSupport
          K hcore v hcert σ =
        Finset.univ.erase i ∧
      Set.range
          (tetrahedronSimplex.faceOpposite i).points =
        tetrahedronSimplex.points ''
          (↑(vertexLinkFaceLabelSupport
            K hcore v hcert σ) :
            Set (Fin 4)) := by

  obtain
    ⟨σ, hσprop, _⟩ :=
    vertexLinkFin4Label_has_unique_complementary_face
      K hcore v hcert i

  refine
    ⟨σ,
      hσprop.1,
      hσprop.2.1,
      hσprop.2.2,
      ?_⟩

  rw [
    hσprop.2.2
  ]

  exact
    tetrahedronFaceOpposite_vertexSet_eq_image_erase i


/--
Realize a represented abstract vertex-link vertex as the corresponding
geometric tetrahedron vertex.

The certified equivalence first assigns the abstract vertex its `Fin 4`
coordinate, and `tetrahedronSimplex.points` then realizes that coordinate
as an actual point of the geometric tetrahedron.
-/
noncomputable def vertexLinkGeometricVertex
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert :
      VertexLinkTetrahedralBoundaryCertificate
        K hcore v)
    (x :
      ↥((vertexLinkVertices K v).toFinset)) :
    TetrahedronAmbient :=
  tetrahedronSimplex.points
    (vertexLinkVertexEquivFin4
      K hcore v hcert x)

/--
The geometric realization of represented link vertices is injective.
-/
theorem vertexLinkGeometricVertex_injective
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert :
      VertexLinkTetrahedralBoundaryCertificate
        K hcore v) :
    Function.Injective
      (vertexLinkGeometricVertex
        K hcore v hcert) := by

  intro x y hxy

  apply
    (vertexLinkVertexEquivFin4
      K hcore v hcert).injective

  apply
    tetrahedronSimplex.independent.injective

  exact
    hxy

/--
The geometric realization of the abstract represented vertices has exactly
the four vertices of `tetrahedronSimplex` as its image.
-/
theorem vertexLinkGeometricVertex_range
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert :
      VertexLinkTetrahedralBoundaryCertificate
        K hcore v) :
    Set.range
        (vertexLinkGeometricVertex
          K hcore v hcert) =
      Set.range tetrahedronSimplex.points := by

  ext p

  constructor

  · rintro
      ⟨x, rfl⟩

    exact
      ⟨vertexLinkVertexEquivFin4
          K hcore v hcert x,
        rfl⟩

  · rintro
      ⟨i, rfl⟩

    refine
      ⟨(vertexLinkVertexEquivFin4
          K hcore v hcert).symm i,
        ?_⟩

    simp [
      vertexLinkGeometricVertex
    ]

end Poincare
