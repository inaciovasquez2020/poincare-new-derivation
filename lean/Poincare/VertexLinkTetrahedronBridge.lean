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


theorem vertexLinkGeometricVertex_image_faceSupport
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert :
      VertexLinkTetrahedralBoundaryCertificate
        K hcore v)
    (σ : LinkTriangle) :
    vertexLinkGeometricVertex
          K hcore v hcert ''
        {x :
          ↥((vertexLinkVertices K v).toFinset) |
            x.1 ∈ σ.verts} =
      tetrahedronSimplex.points ''
        (↑(vertexLinkFaceLabelSupport
          K hcore v hcert σ) : Set (Fin 4)) := by

  ext p
  constructor

  · rintro ⟨x, hx, rfl⟩
    refine
      ⟨vertexLinkVertexEquivFin4
          K hcore v hcert x,
        ?_,
        rfl⟩

    change
      vertexLinkVertexEquivFin4
          K hcore v hcert x ∈
        vertexLinkFaceLabelSupport
          K hcore v hcert σ

    rw [mem_vertexLinkFaceLabelSupport_iff]
    simpa using hx

  · rintro ⟨i, hi, rfl⟩

    change
      i ∈
        vertexLinkFaceLabelSupport
          K hcore v hcert σ at hi

    rw [mem_vertexLinkFaceLabelSupport_iff] at hi

    let x :
        ↥((vertexLinkVertices K v).toFinset) :=
      (vertexLinkVertexEquivFin4
        K hcore v hcert).symm i

    refine ⟨x, ?_, ?_⟩

    · simpa [x] using hi

    · simp [
        x,
        vertexLinkGeometricVertex
      ]


/--
For every `Fin 4` label, the unique certified complementary abstract
`LinkTriangle` is realized on exactly the vertex set of the corresponding
geometric tetrahedron facet opposite that label.
-/
theorem vertexLinkComplementaryFace_realizedVertices_eq_tetrahedronFacet
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert :
      VertexLinkTetrahedralBoundaryCertificate
        K hcore v)
    (i : Fin 4) :
    ∃! σ : LinkTriangle,
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
      vertexLinkGeometricVertex
            K hcore v hcert ''
          {x :
            ↥((vertexLinkVertices K v).toFinset) |
              x.1 ∈ σ.verts} =
        Set.range
          (tetrahedronSimplex.faceOpposite i).points := by

  obtain ⟨σ, hσ, hunique⟩ :=
    vertexLinkFin4Label_has_unique_complementary_face
      K hcore v hcert i

  rcases hσ with
    ⟨hσtri, hσverts, hσsupport⟩

  refine
    ⟨σ, ?_, ?_⟩

  · refine
      ⟨hσtri,
        hσverts,
        hσsupport,
        ?_⟩

    rw [
      vertexLinkGeometricVertex_image_faceSupport
        K hcore v hcert σ,
      hσsupport
    ]

    exact
      (tetrahedronFaceOpposite_vertexSet_eq_image_erase i).symm

  · intro τ hτ

    apply hunique τ

    exact
      ⟨hτ.1,
        hτ.2.1,
        hτ.2.2.1⟩


/--
The geometric realization of an abstract vertex-link triangle is the convex
hull of the geometric realizations of its represented vertices.
-/
noncomputable def vertexLinkGeometricFace
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert :
      VertexLinkTetrahedralBoundaryCertificate
        K hcore v)
    (σ : LinkTriangle) :
    Set TetrahedronAmbient :=
  convexHull ℝ
    (vertexLinkGeometricVertex
          K hcore v hcert ''
      {x :
        ↥((vertexLinkVertices K v).toFinset) |
          x.1 ∈ σ.verts})


/--
The unique certified complementary abstract link face at label `i`, when
realized as the convex hull of its geometric vertices, is exactly the convex
hull of the geometric tetrahedron facet opposite `i`.
-/
theorem vertexLinkComplementaryFace_geometricFace_eq_tetrahedronFacetConvexHull
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert :
      VertexLinkTetrahedralBoundaryCertificate
        K hcore v)
    (i : Fin 4) :
    ∃! σ : LinkTriangle,
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
      vertexLinkGeometricFace
          K hcore v hcert σ =
        convexHull ℝ
          (Set.range
            (tetrahedronSimplex.faceOpposite i).points) := by

  obtain ⟨σ, hσ, hunique⟩ :=
    vertexLinkFin4Label_has_unique_complementary_face
      K hcore v hcert i

  rcases hσ with
    ⟨hσtri, hσverts, hσsupport⟩

  have hrealized :
      vertexLinkGeometricVertex
            K hcore v hcert ''
          {x :
            ↥((vertexLinkVertices K v).toFinset) |
              x.1 ∈ σ.verts} =
        Set.range
          (tetrahedronSimplex.faceOpposite i).points := by

    rw [
      vertexLinkGeometricVertex_image_faceSupport
        K hcore v hcert σ,
      hσsupport
    ]

    exact
      (tetrahedronFaceOpposite_vertexSet_eq_image_erase i).symm

  refine
    ⟨σ, ?_, ?_⟩

  · refine
      ⟨hσtri,
        hσverts,
        hσsupport,
        ?_⟩

    unfold vertexLinkGeometricFace
    rw [hrealized]

  · intro τ hτ

    apply hunique τ

    exact
      ⟨hτ.1,
        hτ.2.1,
        hτ.2.2.1⟩


/--
The geometric realization of the complete abstract vertex link is the union
of the filled geometric realizations of all of its `LinkTriangle`s.
-/
noncomputable def vertexLinkGeometricRealization
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert :
      VertexLinkTetrahedralBoundaryCertificate
        K hcore v) :
    Set TetrahedronAmbient :=
  {p |
    ∃ σ : LinkTriangle,
      σ ∈ vertexLinkTriangles K v ∧
      p ∈ vertexLinkGeometricFace
        K hcore v hcert σ}

end Poincare
