import Poincare.TriangulationTopologicalVertexLinkStarConnectedness
import Poincare.TriangulationTopologicalGeometricDecomposition
import Poincare.TriangulationTopologicalVertexStarNeighborhood

open Set

namespace Poincare

/-- The canonical midpoint of the represented geometric edge with endpoints `v` and `x`. -/
noncomputable def triangulationTopologicalGeometricEdgeMidpoint
    (v x : Nat) : Nat → ℝ :=
  (2 : ℝ)⁻¹ • triangulationTopologicalGeometricVertex v +
    (2 : ℝ)⁻¹ • triangulationTopologicalGeometricVertex x

@[simp] theorem triangulationTopologicalGeometricEdgeMidpoint_apply
    (v x j : Nat) :
    triangulationTopologicalGeometricEdgeMidpoint v x j =
      (if v = j then (2 : ℝ)⁻¹ else 0) +
        (if x = j then (2 : ℝ)⁻¹ else 0) := by
  simp [triangulationTopologicalGeometricEdgeMidpoint,
    triangulationTopologicalGeometricVertex, Pi.single_apply, eq_comm]

private theorem geometricEdgeMidpoint_mem_tetrahedron
    {v x : Nat} {tau : Tet} (hv : v ∈ tau.verts) (hx : x ∈ tau.verts) :
    triangulationTopologicalGeometricEdgeMidpoint v x ∈
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑tau.verts.toFinset : Set Nat)) := by
  apply mem_convexHull_of_exists_fintype
    (fun _ : Fin 2 ↦ (2 : ℝ)⁻¹)
    (fun i : Fin 2 ↦ if i = 0 then
      triangulationTopologicalGeometricVertex v
    else triangulationTopologicalGeometricVertex x)
  · intro i
    positivity
  · norm_num [Fin.sum_univ_two]
  · intro i
    fin_cases i
    · exact ⟨v, List.mem_toFinset.mpr hv, rfl⟩
    · exact ⟨x, List.mem_toFinset.mpr hx, rfl⟩
  · simp [Fin.sum_univ_two, triangulationTopologicalGeometricEdgeMidpoint]

/-- A represented link vertex determines an actual carrier point in the
interior of the corresponding represented geometric edge. -/
theorem triangulationTopologicalGeometricEdgeMidpoint_mem_carrier
    (K : Triangulation) {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x) :
    triangulationTopologicalGeometricEdgeMidpoint v x ∈
      (triangulationTopologicalGeometricComplex K).space := by
  obtain ⟨sigma, hsigma, hxsigma⟩ := hrep
  obtain ⟨tau, htau, hextract⟩ :=
    (mem_vertexLinkTriangles_iff K v sigma).1 hsigma
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  apply Set.mem_iUnion_of_mem tau
  apply Set.mem_iUnion_of_mem htau
  apply geometricEdgeMidpoint_mem_tetrahedron
  · rw [← tau.linkTriangleAt?_isSome_iff v]
    simp [hextract]
  · exact tau.linkTriangleAt?_verts_subset v sigma hextract x hxsigma

/-- The canonical open-edge point, bundled in the genuine realization. -/
noncomputable def triangulationTopologicalCarrierEdgeMidpoint
    (K : Triangulation) (v x : Nat)
    (hrep : VertexLinkVertexRepresented K v x) :
    triangulationTopologicalGeometricCarrier K :=
  ⟨triangulationTopologicalGeometricEdgeMidpoint v x,
    triangulationTopologicalGeometricEdgeMidpoint_mem_carrier K hrep⟩

/-- The endpoints of a represented link edge are distinct. -/
theorem ne_of_vertexLinkVertexRepresented
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    v ≠ x := by
  obtain ⟨sigma, hsigma, hxsigma⟩ := hrep
  obtain ⟨tau, htau, hextract⟩ :=
    (mem_vertexLinkTriangles_iff K v sigma).1 hsigma
  have hvnot : v ∉ sigma.verts :=
    tau.linkTriangleAt?_vertex_not_mem v sigma (hcore.1 tau htau) hextract
  exact fun hvx ↦ hvnot (hvx ▸ hxsigma)

/-- The coordinate-positive neighborhood isolating the interior of the
represented edge `v-x`. -/
def triangulationTopologicalOpenEdgeNeighborhood
    (K : Triangulation) (v x : Nat) :
    Set (triangulationTopologicalGeometricCarrier K) :=
  {p | 0 < p.1 v ∧ 0 < p.1 x}

/-- The finite geometric edge star: the union of precisely those represented
tetrahedra containing both endpoints. -/
noncomputable def triangulationTopologicalGeometricEdgeStar
    (K : Triangulation) (v x : Nat) : Set (Nat → ℝ) :=
  ⋃ (tau : Tet) (_ : tau ∈ K.tets) (_ : v ∈ tau.verts)
      (_ : x ∈ tau.verts),
    triangulationTopologicalTetBody tau

theorem triangulationTopologicalOpenEdgeNeighborhood_isOpen
    (K : Triangulation) (v x : Nat) :
    IsOpen (triangulationTopologicalOpenEdgeNeighborhood K v x) := by
  exact (isOpen_Ioi.preimage
    ((continuous_apply v).comp continuous_subtype_val)).inter
      (isOpen_Ioi.preimage
        ((continuous_apply x).comp continuous_subtype_val))

theorem triangulationTopologicalCarrierEdgeMidpoint_mem_openEdgeNeighborhood
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    triangulationTopologicalCarrierEdgeMidpoint K v x hrep ∈
      triangulationTopologicalOpenEdgeNeighborhood K v x := by
  have hvx := ne_of_vertexLinkVertexRepresented K hcore hrep
  constructor <;>
    simp [triangulationTopologicalCarrierEdgeMidpoint,
      triangulationTopologicalGeometricEdgeMidpoint_apply, hvx, hvx.symm]

/-- Every tetrahedron containing a point of the open-edge neighborhood
contains both represented edge endpoints.  Thus this neighborhood is entirely
inside the finite tetrahedral edge star. -/
theorem triangulationTopologicalOpenEdgeNeighborhood_tet_contains_endpoints
    (K : Triangulation) (v x : Nat)
    {p : triangulationTopologicalGeometricCarrier K}
    (hp : p ∈ triangulationTopologicalOpenEdgeNeighborhood K v x)
    {tau : Tet}
    (hptau : p.1 ∈ triangulationTopologicalTetBody tau) :
    v ∈ tau.verts ∧ x ∈ tau.verts := by
  constructor
  · by_contra hv
    have hz := triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
      tau v hv hptau
    exact (ne_of_gt hp.1) hz
  · by_contra hx
    have hz := triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
      tau x hx hptau
    exact (ne_of_gt hp.2) hz

theorem triangulationTopologicalOpenEdgeNeighborhood_subset_edgeStar
    (K : Triangulation) (v x : Nat) :
    ∀ p ∈ triangulationTopologicalOpenEdgeNeighborhood K v x,
      p.1 ∈ triangulationTopologicalGeometricEdgeStar K v x := by
  intro p hp
  have hspace := p.property
  have hspace' : p.1 ∈ ⋃ (tau : Tet) (_ : tau ∈ K.tets),
      triangulationTopologicalTetBody tau := by
    simpa only [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
      using hspace
  simp only [mem_iUnion] at hspace'
  obtain ⟨tau, htau, hptau⟩ := hspace'
  obtain ⟨hv, hx⟩ :=
    triangulationTopologicalOpenEdgeNeighborhood_tet_contains_endpoints
      K v x hp hptau
  exact Set.mem_iUnion_of_mem tau <|
    Set.mem_iUnion_of_mem htau <|
      Set.mem_iUnion_of_mem hv <|
        Set.mem_iUnion_of_mem hx hptau

/-- The isolated open-edge neighborhood lies in the represented star at either
endpoint.  This is the entry point for the existing radial product model. -/
theorem triangulationTopologicalOpenEdgeNeighborhood_subset_vertexStar
    (K : Triangulation) (v x : Nat) :
    ∀ p ∈ triangulationTopologicalOpenEdgeNeighborhood K v x,
      p.1 ∈ triangulationTopologicalVertexStar K v := by
  intro p hp
  exact triangulationTopologicalVertexStar_mem_of_mem_space_of_coordinate_pos
    K v p.property hp.1

/-- At a represented nondegenerate edge, every point of the isolated
open-edge neighborhood is non-apical in the radial model based at `v`. -/
theorem triangulationTopologicalOpenEdgeNeighborhood_coordinate_lt_one
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    ∀ p ∈ triangulationTopologicalOpenEdgeNeighborhood K v x, p.1 v < 1 := by
  intro p hp
  apply triangulationTopologicalVertexStar_coordinate_lt_one_of_ne_vertex
    K hcore
    (triangulationTopologicalOpenEdgeNeighborhood_subset_vertexStar K v x p hp)
  intro heq
  have hxzero : p.1 x = 0 := by
    rw [heq]
    simp [triangulationTopologicalGeometricVertex,
      ne_of_vertexLinkVertexRepresented K hcore hrep]
  exact (ne_of_gt hp.2) hxzero

/-- A point of the isolated edge neighborhood, bundled in the exact
non-apex-star subtype on which the radial link homeomorphism is defined. -/
noncomputable def triangulationTopologicalOpenEdgeNeighborhoodRadialPoint
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x)
    (p : ↑(triangulationTopologicalOpenEdgeNeighborhood K v x)) :
    ↑{q : Nat → ℝ |
      q ∈ triangulationTopologicalVertexStar K v ∧ q v < 1} :=
  ⟨p.1.1,
    triangulationTopologicalOpenEdgeNeighborhood_subset_vertexStar
      K v x p.1 p.2,
    triangulationTopologicalOpenEdgeNeighborhood_coordinate_lt_one
      K hcore hrep p.1 p.2⟩

theorem triangulationTopologicalOpenEdgeNeighborhood_mem_nhds
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    triangulationTopologicalOpenEdgeNeighborhood K v x ∈
      nhds (triangulationTopologicalCarrierEdgeMidpoint K v x hrep) := by
  exact (triangulationTopologicalOpenEdgeNeighborhood_isOpen K v x).mem_nhds
    (triangulationTopologicalCarrierEdgeMidpoint_mem_openEdgeNeighborhood
      K hcore hrep)

/-- In the radial product based at `v`, positivity of the second edge
coordinate is exactly positivity of the corresponding transverse-link
coordinate.  Thus the isolated open-edge neighborhood has no hidden radial
condition in the `x` direction. -/
theorem triangulationTopologicalOpenEdgeNeighborhood_radialProjection_coordinate_pos_iff
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x)
    (p : ↑(triangulationTopologicalOpenEdgeNeighborhood K v x)) :
    0 < triangulationTopologicalRadialLinkProjection K v
        (triangulationTopologicalOpenEdgeNeighborhoodRadialPoint
          K hcore hrep p) x ↔
      0 < p.1.1 x := by
  have hvx : v ≠ x := ne_of_vertexLinkVertexRepresented K hcore hrep
  have hdenom : 0 < 1 - p.1.1 v := sub_pos.mpr
    (triangulationTopologicalOpenEdgeNeighborhood_coordinate_lt_one
      K hcore hrep p.1 p.2)
  simp only [triangulationTopologicalRadialLinkProjection, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  rw [show triangulationTopologicalGeometricVertex v x = 0 by
    simp [triangulationTopologicalGeometricVertex, hvx]]
  simp only [mul_zero, sub_zero, one_div]
  exact mul_pos_iff_of_pos_left (inv_pos.mpr hdenom)

/-- Exact radial-coordinate description of the two positive coordinates that
cut out the open geometric edge neighborhood. -/
theorem triangulationTopologicalRadialLink_openEdge_coordinates_iff
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x)
    (tq : ↑(Set.Ico (0 : ℝ) 1) ×
      ↑(triangulationTopologicalVertexLink K v)) :
    let p :=
      (triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
        K hcore v) tq
    (0 < p.1 v ∧ 0 < p.1 x) ↔
      (0 < tq.1.1 ∧ 0 < tq.2.1 x) := by
  dsimp
  change
    (0 < (tq.1.1 • triangulationTopologicalGeometricVertex v +
          (1 - tq.1.1) • tq.2.1) v ∧
      0 < (tq.1.1 • triangulationTopologicalGeometricVertex v +
          (1 - tq.1.1) • tq.2.1) x) ↔ _
  have hvx : v ≠ x := ne_of_vertexLinkVertexRepresented K hcore hrep
  have hfactor : 0 < 1 - tq.1.1 := sub_pos.mpr tq.1.2.2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show triangulationTopologicalGeometricVertex v v = 1 by
      simp [triangulationTopologicalGeometricVertex],
    show tq.2.1 v = 0 by
      exact triangulationTopologicalVertexLink_apex_coordinate_eq_zero
        K hcore v tq.2.1 tq.2.2,
    show triangulationTopologicalGeometricVertex v x = 0 by
      simp [triangulationTopologicalGeometricVertex, hvx]]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  rw [mul_pos_iff_of_pos_left hfactor]

/-- Set-level form of the open-edge radial-coordinate calculation.  The
preimage of the isolated geometric open-edge neighborhood under the radial
product homeomorphism is exactly the product locus where both the radial
parameter and the transverse `x` coordinate are positive. -/
theorem triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink_preimage_openEdge
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    (triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
        K hcore v) ⁻¹'
      {p | 0 < p.1 v ∧ 0 < p.1 x} =
      {tq | 0 < tq.1.1 ∧ 0 < tq.2.1 x} := by
  ext tq
  exact triangulationTopologicalRadialLink_openEdge_coordinates_iff
    K hcore hrep tq

/-- The exact finite radial local model carried by the isolated open-edge
neighborhood.  This packages the preceding set equality as a homeomorphism of
subspaces, so subsequent component or homology arguments can work entirely in
the product/transverse coordinates. -/
noncomputable def triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLink
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    {tq : ↑(Set.Ico (0 : ℝ) 1) ×
        ↑(triangulationTopologicalVertexLink K v) |
      0 < tq.1.1 ∧ 0 < tq.2.1 x} ≃ₜ
    {p : ↑{q : Nat → ℝ |
        q ∈ triangulationTopologicalVertexStar K v ∧ q v < 1} |
      0 < p.1 v ∧ 0 < p.1 x} :=
  (triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
      K hcore v).subtype fun tq ↦
    triangulationTopologicalRadialLink_openEdge_coordinates_iff
      K hcore hrep tq |>.symm

/-- The radial edge model with the geometric carrier, rather than the
auxiliary non-apex vertex-star subtype, as its target. -/
noncomputable def
    triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLinkCarrier
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    {tq : ↑(Set.Ico (0 : ℝ) 1) ×
        ↑(triangulationTopologicalVertexLink K v) |
      0 < tq.1.1 ∧ 0 < tq.2.1 x} ≃ₜ
    ↑(triangulationTopologicalOpenEdgeNeighborhood K v x) :=
  (triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLink
      K hcore hrep).trans
    { toFun := fun p ↦
        ⟨⟨p.1.1,
          triangulationTopologicalVertexStar_subset_space K v p.1.2.1⟩,
          p.2⟩
      invFun := fun p ↦
        ⟨⟨p.1.1,
          triangulationTopologicalOpenEdgeNeighborhood_subset_vertexStar
            K v x p.1 p.2,
          triangulationTopologicalOpenEdgeNeighborhood_coordinate_lt_one
            K hcore hrep p.1 p.2⟩,
          p.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun :=
        Continuous.subtype_mk
          (Continuous.subtype_mk
            (continuous_subtype_val.comp continuous_subtype_val) _)
          _
      continuous_invFun :=
        Continuous.subtype_mk
          (Continuous.subtype_mk
            (continuous_subtype_val.comp continuous_subtype_val) _)
          _ }

end Poincare
