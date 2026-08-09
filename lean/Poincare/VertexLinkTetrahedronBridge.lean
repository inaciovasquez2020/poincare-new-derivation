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

/--
The certified geometric realization of the complete abstract vertex link is
exactly the tetrahedral frontier.
-/
theorem vertexLinkGeometricRealization_eq_tetrahedronFrontier
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v) :
    vertexLinkGeometricRealization K hcore v hcert =
      frontier tetrahedronBody := by
  rw [tetrahedronFrontier_eq_facetUnion]
  ext p
  constructor
  · rintro ⟨σ, hσ, hpσ⟩
    let e := vertexLinkVertexEquivFin4 K hcore v hcert
    let S := vertexLinkFaceLabelSupport K hcore v hcert σ
    have hnodup := vertexLinkTriangles_triangle_nodup K hcore v σ hσ
    have hScard : S.card ≤ 3 := by
      have hmap : Set.MapsTo (fun i : Fin 4 => (e.symm i).1)
          (↑S : Set (Fin 4)) (↑σ.verts.toFinset : Set Nat) := by
        intro i hi
        change i ∈ vertexLinkFaceLabelSupport K hcore v hcert σ at hi
        rw [mem_vertexLinkFaceLabelSupport_iff] at hi
        simpa [e] using hi
      have hinj : Set.InjOn (fun i : Fin 4 => (e.symm i).1)
          (↑S : Set (Fin 4)) := by
        intro i _ j _ hij
        apply e.symm.injective
        apply Subtype.ext
        exact hij
      calc
        S.card ≤ σ.verts.toFinset.card :=
          Finset.card_le_card_of_injOn _ hmap hinj
        _ = σ.verts.length := List.toFinset_card_of_nodup hnodup
        _ = 3 := by simp [LinkTriangle.verts]
    have hmissing : ∃ i : Fin 4, i ∉ S := by
      by_contra h
      push_neg at h
      have hSuniv : S = Finset.univ := Finset.eq_univ_of_forall h
      rw [hSuniv] at hScard
      simp at hScard
    obtain ⟨i, hi⟩ := hmissing
    let x : ↥((vertexLinkVertices K v).toFinset) := e.symm i
    have hxV : x.1 ∈ vertexLinkVertices K v :=
      List.mem_toFinset.mp x.2
    have hxnot : x.1 ∉ σ.verts := by
      intro hx
      apply hi
      change i ∈ vertexLinkFaceLabelSupport K hcore v hcert σ
      rw [mem_vertexLinkFaceLabelSupport_iff]
      simpa [x, e] using hx
    have hσsubset : σ.verts.toFinset ⊆
        (vertexLinkVertices K v).toFinset.erase x.1 := by
      intro y hy
      have hylist : y ∈ σ.verts := List.mem_toFinset.mp hy
      have hyV : y ∈ vertexLinkVertices K v :=
        (mem_vertexLinkVertices_iff K v y).2 ⟨σ, hσ, hylist⟩
      simp only [Finset.mem_erase]
      exact ⟨fun hyx => hxnot (hyx ▸ hylist), List.mem_toFinset.mpr hyV⟩
    have hσsupport : ∀ y : Nat,
        y ∈ σ.verts ↔ y ∈ vertexLinkVertices K v ∧ y ≠ x.1 := by
      have hcardV : (vertexLinkVertices K v).toFinset.card = 4 := by
        have hVnodup : (vertexLinkVertices K v).Nodup := by
          unfold vertexLinkVertices
          exact eraseDups_nodup_nat _
        rw [List.toFinset_card_of_nodup hVnodup]
        exact hcert.1
      have hcardErase : ((vertexLinkVertices K v).toFinset.erase x.1).card = 3 := by
        rw [Finset.card_erase_of_mem x.2, hcardV]
      have heq : σ.verts.toFinset =
          (vertexLinkVertices K v).toFinset.erase x.1 := by
        apply Finset.eq_of_subset_of_card_le hσsubset
        rw [hcardErase, List.toFinset_card_of_nodup hnodup]
        simp [LinkTriangle.verts]
      intro y
      rw [← List.mem_toFinset, heq]
      simp [List.mem_toFinset, and_comm]
    obtain ⟨τ, hτ, huniq⟩ :=
      vertexLinkFin4Label_has_unique_complementary_face K hcore v hcert i
    have hστ : σ = τ := by
      apply huniq σ
      refine ⟨hσ, ?_, ?_⟩
      · simpa [x, e] using hσsupport
      · ext j
        rw [mem_vertexLinkFaceLabelSupport_iff]
        rw [hσsupport]
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · rintro ⟨_, hj⟩
          intro hji
          subst j
          apply hj
          simp [x, e]
        · intro hji
          refine ⟨List.mem_toFinset.mp ((e.symm j).2), ?_⟩
          intro hval
          apply hji
          apply e.symm.injective
          apply Subtype.ext
          simpa [x, e] using hval
    rw [hστ] at hpσ
    obtain ⟨ρ, hρ, _⟩ :=
      vertexLinkComplementaryFace_geometricFace_eq_tetrahedronFacetConvexHull
        K hcore v hcert i
    have hρτ : ρ = τ := by
      apply huniq ρ
      exact ⟨hρ.1, hρ.2.1, hρ.2.2.1⟩
    rw [hρτ] at hρ
    exact ⟨i, hρ.2.2.2 ▸ hpσ⟩
  · rintro ⟨i, hp⟩
    obtain ⟨σ, hσ, _⟩ :=
      vertexLinkComplementaryFace_geometricFace_eq_tetrahedronFacetConvexHull
        K hcore v hcert i
    rcases hσ with ⟨hσtri, _, _, hσface⟩
    exact ⟨σ, hσtri, hσface ▸ hp⟩

/--
The subtype of the certified geometric vertex-link realization is
homeomorphic to the unit two-sphere in the ambient Euclidean three-space.
-/
noncomputable def vertexLinkGeometricRealizationHomeomorphUnitSphere
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hcert : VertexLinkTetrahedralBoundaryCertificate K hcore v) :
    ↥(vertexLinkGeometricRealization K hcore v hcert) ≃ₜ
      ↥(Metric.sphere (0 : TetrahedronAmbient) 1) :=
  (Homeomorph.setCongr
      (vertexLinkGeometricRealization_eq_tetrahedronFrontier
        K hcore v hcert)).trans
    tetrahedronFrontierHomeomorphUnitSphere

end Poincare
