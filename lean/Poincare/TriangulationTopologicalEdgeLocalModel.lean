import Poincare.TriangulationTopologicalVertexLinkStarConnectedness
import Poincare.TriangulationTopologicalGeometricDecomposition
import Poincare.TriangulationTopologicalVertexStarNeighborhood
import Poincare.CircleNotSimplyConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

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

/-- The radial-product coordinates of the represented geometric edge
midpoint.  This is the unique point that must be deleted in the transverse
circle-retraction argument. -/
noncomputable def triangulationTopologicalOpenEdgeRadialMidpoint
    (K : Triangulation)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    {tq : ↑(Set.Ico (0 : ℝ) 1) ×
        ↑(triangulationTopologicalVertexLink K v) |
      0 < tq.1.1 ∧ 0 < tq.2.1 x} := by
  have hxlink : triangulationTopologicalGeometricVertex x ∈
      triangulationTopologicalVertexLink K v := by
    obtain ⟨sigma, hsigma, hxsigma⟩ := hrep
    apply (mem_triangulationTopologicalVertexLink_iff K v _).2
    refine ⟨sigma, hsigma, ?_⟩
    apply subset_convexHull ℝ
    exact ⟨x, List.mem_toFinset.mpr hxsigma, rfl⟩
  exact ⟨⟨⟨(2 : ℝ)⁻¹, by norm_num, by norm_num⟩,
      ⟨triangulationTopologicalGeometricVertex x, hxlink⟩⟩,
    by simp [triangulationTopologicalGeometricVertex]⟩

/-- Under the exact radial local model, `(1/2, apex x)` is literally the
represented geometric edge midpoint. -/
@[simp] theorem
triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLinkCarrier_midpoint
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLinkCarrier
        K hcore hrep
        (triangulationTopologicalOpenEdgeRadialMidpoint K hrep) =
      ⟨triangulationTopologicalCarrierEdgeMidpoint K v x hrep,
        triangulationTopologicalCarrierEdgeMidpoint_mem_openEdgeNeighborhood
          K hcore hrep⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  change
    ((triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
      K hcore v)
      (triangulationTopologicalOpenEdgeRadialMidpoint K hrep).1).1 = _
  rw [triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink_apply_val]
  funext j
  norm_num [triangulationTopologicalOpenEdgeRadialMidpoint,
    triangulationTopologicalCarrierEdgeMidpoint,
    triangulationTopologicalGeometricEdgeMidpoint, Pi.add_apply, Pi.smul_apply]

/-- Bundle the transverse coordinate of an open-edge radial point in the
represented star of `x`. -/
noncomputable def triangulationTopologicalOpenEdgeTransverseStarPoint
    (K : Triangulation) (v x : Nat)
    (tq : {tq : ↑(Set.Ico (0 : ℝ) 1) ×
        ↑(triangulationTopologicalVertexLink K v) |
      0 < tq.1.1 ∧ 0 < tq.2.1 x}) :
    ↑(triangulationTopologicalVertexLinkStar K v x) :=
  ⟨tq.1.2.1,
    triangulationTopologicalVertexLink_mem_vertexLinkStar_of_coordinate_pos
      K v x tq.1.2.2 tq.2.2⟩

@[continuity, fun_prop] theorem
continuous_triangulationTopologicalOpenEdgeTransverseStarPoint
    (K : Triangulation) (v x : Nat) :
    Continuous (triangulationTopologicalOpenEdgeTransverseStarPoint K v x) := by
  apply Continuous.subtype_mk
  fun_prop

/-- The axial coordinate together with any signed radial coordinate can
vanish only at the deleted edge midpoint.  This is the nonvanishing fact
needed to normalize the pair to the unit circle. -/
theorem edgeRadial_signedCoordinate_ne_zero
    (K : Triangulation) {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x)
    (g : ↑(triangulationTopologicalVertexLinkStar K v x) → ℝ)
    (habs : ∀ q, |g q| = 1 - q.1 x)
    (tq : {tq : ↑(Set.Ico (0 : ℝ) 1) ×
        ↑(triangulationTopologicalVertexLink K v) |
      0 < tq.1.1 ∧ 0 < tq.2.1 x})
    (hne : tq ≠ triangulationTopologicalOpenEdgeRadialMidpoint K hrep) :
    (tq.1.1.1 - (2 : ℝ)⁻¹,
        g (triangulationTopologicalOpenEdgeTransverseStarPoint K v x tq)) ≠
      (0, 0) := by
  intro hzero
  have ht : tq.1.1.1 = (2 : ℝ)⁻¹ := by
    linarith [congrArg Prod.fst hzero]
  have hg : g (triangulationTopologicalOpenEdgeTransverseStarPoint K v x tq) = 0 :=
    congrArg Prod.snd hzero
  have hx : tq.1.2.1 x = 1 := by
    have := habs (triangulationTopologicalOpenEdgeTransverseStarPoint K v x tq)
    simp only [hg, abs_zero] at this
    dsimp [triangulationTopologicalOpenEdgeTransverseStarPoint] at this
    linarith
  have hq : tq.1.2.1 = triangulationTopologicalGeometricVertex x :=
    (triangulationTopologicalVertexLinkStar_apex_coordinate K v x
      (triangulationTopologicalOpenEdgeTransverseStarPoint K v x tq).2).2.2.1 hx
  apply hne
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact ht
  · apply Subtype.ext
    exact hq

/-- Normalize the axial and signed transverse coordinates of the deleted
radial edge model to the unit circle. -/
noncomputable def edgeRadialCircleMap
    (K : Triangulation) {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x)
    (g : ↑(triangulationTopologicalVertexLinkStar K v x) → ℝ)
    (habs : ∀ q, |g q| = 1 - q.1 x) :
    ↑({triangulationTopologicalOpenEdgeRadialMidpoint K hrep}ᶜ : Set
      {tq : ↑(Set.Ico (0 : ℝ) 1) ×
          ↑(triangulationTopologicalVertexLink K v) |
        0 < tq.1.1 ∧ 0 < tq.2.1 x}) → Circle := fun tq ↦ by
  let z : ℂ :=
    (tq.1.1.1 - (2 : ℝ)⁻¹ : ℝ) +
      (g (triangulationTopologicalOpenEdgeTransverseStarPoint K v x tq.1) : ℝ) *
        Complex.I
  have hz : z ≠ 0 := by
    intro hz0
    have hre : tq.1.1.1 - (2 : ℝ)⁻¹ = 0 := by
      simpa [z] using congrArg Complex.re hz0
    have him :
        g (triangulationTopologicalOpenEdgeTransverseStarPoint K v x tq.1) = 0 := by
      simpa [z] using congrArg Complex.im hz0
    exact edgeRadial_signedCoordinate_ne_zero K hrep g habs tq.1 tq.2
      (Prod.ext hre him)
  exact ⟨z / ‖z‖, by
    change z / (‖z‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div]
    simpa using div_self (norm_ne_zero_iff.mpr hz)⟩

/-- The normalized signed radial coordinate is continuous on the open-edge
radial model with its midpoint deleted. -/
theorem continuous_edgeRadialCircleMap
    (K : Triangulation) {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x)
    (g : ↑(triangulationTopologicalVertexLinkStar K v x) → ℝ)
    (hg : Continuous g)
    (habs : ∀ q, |g q| = 1 - q.1 x) :
    Continuous (edgeRadialCircleMap K hrep g habs) := by
  apply Continuous.subtype_mk
  dsimp only [edgeRadialCircleMap]
  let z : ↑({triangulationTopologicalOpenEdgeRadialMidpoint K hrep}ᶜ : Set
      {tq : ↑(Set.Ico (0 : ℝ) 1) ×
          ↑(triangulationTopologicalVertexLink K v) |
        0 < tq.1.1 ∧ 0 < tq.2.1 x}) → ℂ := fun tq ↦
    (tq.1.1.1 - (2 : ℝ)⁻¹ : ℝ) +
      (g (triangulationTopologicalOpenEdgeTransverseStarPoint K v x tq.1) : ℝ) *
        Complex.I
  have hz : Continuous z := by
    dsimp [z]
    fun_prop
  have hzne : ∀ tq, z tq ≠ 0 := by
    intro tq hzero
    have hre : tq.1.1.1 - (2 : ℝ)⁻¹ = 0 := by
      simpa [z] using congrArg Complex.re hzero
    have him :
        g (triangulationTopologicalOpenEdgeTransverseStarPoint K v x tq.1) = 0 := by
      simpa [z] using congrArg Complex.im hzero
    exact edgeRadial_signedCoordinate_ne_zero K hrep g habs tq.1 tq.2
      (Prod.ext hre him)
  change Continuous (fun tq ↦ z tq / ‖z tq‖)
  exact hz.div₀ (Complex.continuous_ofReal.comp hz.norm) fun tq ↦
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hzne tq))

/-- The two nonempty clopen sides supply transverse points with strictly
positive radial lengths and opposite signed-coordinate values.  These are
the two endpoints used by the explicit circle inclusion. -/
theorem exists_edgeRadial_opposite_side_witnesses
    (K : Triangulation) (v x : Nat)
    (A B : Set
      ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (g : ↑(triangulationTopologicalVertexLinkStar K v x) → ℝ)
    (hgA : ∀ q (hq : q.1 ≠ triangulationTopologicalGeometricVertex x),
      (⟨q.1, q.2, hq⟩ :
        ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∈ A →
        g q = 1 - q.1 x)
    (hgB : ∀ q (hq : q.1 ≠ triangulationTopologicalGeometricVertex x),
      (⟨q.1, q.2, hq⟩ :
        ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∈ B →
        g q = -(1 - q.1 x)) :
    ∃ qA ∈ A, ∃ qB ∈ B,
      0 < 1 - qA.1 x ∧
      0 < 1 - qB.1 x ∧
      g ⟨qA.1, qA.2.1⟩ = 1 - qA.1 x ∧
      g ⟨qB.1, qB.2.1⟩ = -(1 - qB.1 x) := by
  obtain ⟨qA, hqA⟩ := hAne
  obtain ⟨qB, hqB⟩ := hBne
  refine ⟨qA, hqA, qB, hqB, ?_, ?_, ?_, ?_⟩
  · exact triangulationTopologicalVertexLinkStar_one_sub_coordinate_pos
      K v x qA.2.1 qA.2.2
  · exact triangulationTopologicalVertexLinkStar_one_sub_coordinate_pos
      K v x qB.2.1 qB.2.2
  · exact hgA ⟨qA.1, qA.2.1⟩ qA.2.2 hqA
  · exact hgB ⟨qB.1, qB.2.1⟩ qB.2.2 hqB

/-- Two transverse witnesses of positive radial length admit a common
positive circle scale which stays below both lengths and below `1/4`.  This
is the quantitative input ensuring that the explicit circle inclusion stays
inside the open axial interval and never reaches either transverse endpoint.
-/
theorem exists_edgeRadial_circleScale
    {rA rB : ℝ} (hrA : 0 < rA) (hrB : 0 < rB) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (4 : ℝ)⁻¹ ∧ δ < rA ∧ δ < rB := by
  let m := min ((4 : ℝ)⁻¹) (min rA rB)
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min (by norm_num) (lt_min hrA hrB)
  refine ⟨m / 2, half_pos hm, ?_, ?_, ?_⟩
  · exact (half_lt_self hm).trans_le (min_le_left _ _)
  · exact (half_lt_self hm).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  · exact (half_lt_self hm).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))

private theorem edgeRadial_lineMap_mem
    (K : Triangulation) (v x : Nat)
    (q : ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (AffineMap.lineMap (triangulationTopologicalGeometricVertex x) q.1) c ∈
      triangulationTopologicalVertexLinkStar K v x := by
  obtain ⟨sigma, hsigma, hqsigma⟩ :=
    (mem_triangulationTopologicalVertexLinkStar_iff K v x q.1).1 q.2.1
  have hxverts : x ∈ sigma.verts :=
    (mem_vertexLinkStarTriangles_iff K v x sigma).1 hsigma |>.2
  have hxbody : triangulationTopologicalGeometricVertex x ∈
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑sigma.verts.toFinset : Set Nat)) := by
    apply subset_convexHull
    exact ⟨x, List.mem_toFinset.mpr hxverts, rfl⟩
  apply (mem_triangulationTopologicalVertexLinkStar_iff K v x _).2
  exact ⟨sigma, hsigma,
    (convex_convexHull ℝ _).lineMap_mem hxbody hqsigma ⟨hc0, hc1⟩⟩

/-- The transverse point of the explicit small circle.  On each closed
semicircle it follows the radial segment from the apex into the corresponding
clopen side. -/
noncomputable def edgeRadialCircleTransversePoint
    (K : Triangulation) (v x : Nat)
    (qA qB : ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδA : δ < 1 - qA.1 x) (hδB : δ < 1 - qB.1 x)
    (z : Circle) : ↑(triangulationTopologicalVertexLinkStar K v x) := by
  let rA := 1 - qA.1 x
  let rB := 1 - qB.1 x
  let c : ℝ := if 0 ≤ z.1.im then δ * z.1.im / rA else δ * (-z.1.im) / rB
  let q := if 0 ≤ z.1.im then qA else qB
  refine ⟨(AffineMap.lineMap
    (triangulationTopologicalGeometricVertex x) q.1) c, ?_⟩
  apply edgeRadial_lineMap_mem K v x q
  · dsimp [c, q, rA, rB]
    split_ifs with hz
    · exact div_nonneg (mul_nonneg hδ0.le hz) (sub_nonneg.mpr
        (triangulationTopologicalVertexLinkStar_apex_coordinate K v x qA.2.1).2.1)
    · exact div_nonneg (mul_nonneg hδ0.le (neg_nonneg.mpr (le_of_not_ge hz)))
        (sub_nonneg.mpr
          (triangulationTopologicalVertexLinkStar_apex_coordinate K v x qB.2.1).2.1)
  · have him : |z.1.im| ≤ 1 := by
      calc |z.1.im| ≤ ‖(z.1 : ℂ)‖ := Complex.abs_im_le_norm _
        _ = 1 := Circle.norm_coe z
    dsimp [c, q, rA, rB]
    split_ifs with hz
    · have hrA : 0 < 1 - qA.1 x := lt_trans hδ0 hδA
      apply (div_le_one hrA).2
      nlinarith [le_trans (le_abs_self z.1.im) him]
    · have hrB : 0 < 1 - qB.1 x := lt_trans hδ0 hδB
      apply (div_le_one hrB).2
      nlinarith [le_trans (neg_le_abs z.1.im) him]

/-- The explicit inclusion of the unit circle in the deleted open-edge radial
model, at a scale smaller than both chosen transverse radial lengths. -/
noncomputable def edgeRadialCircleInclusion
    (K : Triangulation) {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x)
    (qA qB : ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (δ : ℝ) (hδ0 : 0 < δ) (hδquarter : δ < (4 : ℝ)⁻¹)
    (hδA : δ < 1 - qA.1 x) (hδB : δ < 1 - qB.1 x) :
    Circle → ↑({triangulationTopologicalOpenEdgeRadialMidpoint K hrep}ᶜ : Set
      {tq : ↑(Set.Ico (0 : ℝ) 1) ×
          ↑(triangulationTopologicalVertexLink K v) |
        0 < tq.1.1 ∧ 0 < tq.2.1 x}) := fun z ↦ by
  let t : ℝ := (2 : ℝ)⁻¹ + δ * z.1.re
  let q := edgeRadialCircleTransversePoint K v x qA qB δ hδ0 hδA hδB z
  have hre : |z.1.re| ≤ 1 := by
    calc |z.1.re| ≤ ‖(z.1 : ℂ)‖ := Complex.abs_re_le_norm _
      _ = 1 := Circle.norm_coe z
  have him : |z.1.im| ≤ 1 := by
    calc |z.1.im| ≤ ‖(z.1 : ℂ)‖ := Complex.abs_im_le_norm _
      _ = 1 := Circle.norm_coe z
  have ht0 : 0 < t := by dsimp [t]; nlinarith [neg_abs_le z.1.re, hδquarter]
  have ht1 : t < 1 := by dsimp [t]; nlinarith [le_abs_self z.1.re, hδquarter]
  have hqx : 0 < q.1 x := by
    dsimp [q, edgeRadialCircleTransversePoint]
    simp only [AffineMap.lineMap_apply]
    split_ifs with hz
    · have hqAx :=
        (triangulationTopologicalVertexLinkStar_apex_coordinate K v x qA.2.1).1
      have hrA : 0 < 1 - qA.1 x := lt_trans hδ0 hδA
      have hc : δ * z.1.im / (1 - qA.1 x) < 1 :=
        (div_lt_one hrA).2 (by nlinarith [le_trans (le_abs_self z.1.im) him])
      simp [triangulationTopologicalGeometricVertex]
      rw [show δ * z.1.im / (1 - qA.1 x) * (qA.1 x - 1) + 1 =
        (1 - δ * z.1.im / (1 - qA.1 x)) * (1 - qA.1 x) + qA.1 x by ring]
      have hp : 0 < (1 - δ * z.1.im / (1 - qA.1 x)) * (1 - qA.1 x) :=
        mul_pos (sub_pos.mpr hc) hrA
      linarith
    · have hqBx :=
        (triangulationTopologicalVertexLinkStar_apex_coordinate K v x qB.2.1).1
      have hrB : 0 < 1 - qB.1 x := lt_trans hδ0 hδB
      have hc : δ * (-z.1.im) / (1 - qB.1 x) < 1 :=
        (div_lt_one hrB).2 (by nlinarith [le_trans (neg_le_abs z.1.im) him])
      simp [triangulationTopologicalGeometricVertex]
      rw [show -(δ * z.1.im) / (1 - qB.1 x) * (qB.1 x - 1) + 1 =
        (1 - δ * (-z.1.im) / (1 - qB.1 x)) * (1 - qB.1 x) + qB.1 x by ring]
      have hp : 0 < (1 - δ * (-z.1.im) / (1 - qB.1 x)) * (1 - qB.1 x) :=
        mul_pos (sub_pos.mpr hc) hrB
      linarith
  refine ⟨⟨⟨⟨t, ht0.le, ht1⟩, ⟨q.1, ?_⟩⟩, ht0, hqx⟩, ?_⟩
  · exact triangulationTopologicalVertexLinkStar_subset_vertexLink K v x q.2
  · intro heq
    simp only [Set.mem_singleton_iff] at heq
    have ht := congrArg (fun p ↦ p.1.1.1) heq
    dsimp [t, triangulationTopologicalOpenEdgeRadialMidpoint] at ht
    have hzre : z.1.re = 0 := by nlinarith
    have hq := congrArg (fun p ↦ p.1.2.1 x) heq
    dsimp [q, edgeRadialCircleTransversePoint] at hq
    have hzim : z.1.im = 0 := by
      split_ifs at hq with hz
      · have hrA : 0 < 1 - qA.1 x := lt_trans hδ0 hδA
        simp [AffineMap.lineMap_apply, triangulationTopologicalGeometricVertex,
          triangulationTopologicalOpenEdgeRadialMidpoint] at hq
        field_simp at hq
        rcases hq with ((h | h) | h) | h
        · exact False.elim ((ne_of_gt hδ0) h)
        · exact h
        · exact False.elim ((ne_of_gt hrA) h)
        · nlinarith
      · have hrB : 0 < 1 - qB.1 x := lt_trans hδ0 hδB
        simp [AffineMap.lineMap_apply, triangulationTopologicalGeometricVertex,
          triangulationTopologicalOpenEdgeRadialMidpoint] at hq
        field_simp at hq
        rcases hq with ((h | h) | h) | h
        · exact False.elim ((ne_of_gt hδ0) h)
        · exact h
        · exact False.elim ((ne_of_gt hrB) h)
        · nlinarith
    have hnorm := Circle.normSq_coe z
    simp [Complex.normSq_apply, hzre, hzim] at hnorm

theorem continuous_edgeRadialCircleTransversePoint
    (K : Triangulation) (v x : Nat)
    (qA qB : ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδA : δ < 1 - qA.1 x) (hδB : δ < 1 - qB.1 x) :
    Continuous (edgeRadialCircleTransversePoint K v x qA qB δ hδ0 hδA hδB) := by
  apply Continuous.subtype_mk
  dsimp only [edgeRadialCircleTransversePoint]
  have hc : Continuous (fun z : Circle ↦ if 0 ≤ z.1.im then
    (AffineMap.lineMap (triangulationTopologicalGeometricVertex x) qA.1)
      (δ * z.1.im / (1 - qA.1 x)) else
    (AffineMap.lineMap (triangulationTopologicalGeometricVertex x) qB.1)
      (δ * (-z.1.im) / (1 - qB.1 x))) := by
    apply continuous_if_le continuous_const
      (Complex.continuous_im.comp continuous_subtype_val)
    · fun_prop
    · fun_prop
    · intro z hz
      change 0 = z.1.im at hz
      rw [← hz]
      simp [AffineMap.lineMap_apply]
  exact hc.congr fun z ↦ by split_ifs <;> rfl

theorem continuous_edgeRadialCircleInclusion
    (K : Triangulation) {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x)
    (qA qB : ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (δ : ℝ) (hδ0 : 0 < δ) (hδquarter : δ < (4 : ℝ)⁻¹)
    (hδA : δ < 1 - qA.1 x) (hδB : δ < 1 - qB.1 x) :
    Continuous (edgeRadialCircleInclusion K hrep qA qB δ hδ0 hδquarter hδA hδB) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    fun_prop
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (continuous_edgeRadialCircleTransversePoint K v x qA qB δ hδ0 hδA hδB)

theorem edgeRadialCircleTransversePoint_signedCoordinate
    (K : Triangulation) (v x : Nat)
    (A B : Set ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (hAcl : IsClopen A) (hBcl : IsClopen B)
    (qA qB : ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (hqA : qA ∈ A) (hqB : qB ∈ B)
    (g : ↑(triangulationTopologicalVertexLinkStar K v x) → ℝ)
    (habs : ∀ q, |g q| = 1 - q.1 x)
    (hgA : ∀ q (hq : q.1 ≠ triangulationTopologicalGeometricVertex x),
      (⟨q.1, q.2, hq⟩ :
        ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∈ A →
        g q = 1 - q.1 x)
    (hgB : ∀ q (hq : q.1 ≠ triangulationTopologicalGeometricVertex x),
      (⟨q.1, q.2, hq⟩ :
        ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∈ B →
        g q = -(1 - q.1 x))
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδA : δ < 1 - qA.1 x) (hδB : δ < 1 - qB.1 x)
    (z : Circle) :
    g (edgeRadialCircleTransversePoint K v x qA qB δ hδ0 hδA hδB z) =
      δ * z.1.im := by
  by_cases hz0 : z.1.im = 0
  · have hcoord :
        (edgeRadialCircleTransversePoint K v x qA qB δ hδ0 hδA hδB z).1 x = 1 := by
      dsimp [edgeRadialCircleTransversePoint]
      simp [hz0, AffineMap.lineMap_apply,
        triangulationTopologicalGeometricVertex]
    have hgabs := habs
      (edgeRadialCircleTransversePoint K v x qA qB δ hδ0 hδA hδB z)
    rw [hcoord] at hgabs
    simp only [sub_self, abs_eq_zero] at hgabs
    simp [hz0, hgabs]
  · by_cases hz : 0 < z.1.im
    · have hrA : 0 < 1 - qA.1 x := lt_trans hδ0 hδA
      let c := δ * z.1.im / (1 - qA.1 x)
      have hc0 : 0 < c := div_pos (mul_pos hδ0 hz) hrA
      have him : z.1.im ≤ 1 := by
        calc z.1.im ≤ |z.1.im| := le_abs_self _
          _ ≤ ‖(z.1 : ℂ)‖ := Complex.abs_im_le_norm _
          _ = 1 := Circle.norm_coe z
      have hc1 : c ≤ 1 := by
        apply (div_le_one hrA).2
        nlinarith
      obtain ⟨hp, hpA⟩ :=
        IsClopen.vertexLinkStar_radial_mem K v x hAcl qA hqA hc0 hc1
      let p := (AffineMap.lineMap
        (triangulationTopologicalGeometricVertex x) qA.1) c
      have hpne : p ≠ triangulationTopologicalGeometricVertex x := by
        intro heq
        have heqx := congrFun heq x
        have hrad := triangulationTopologicalVertexLinkStar_one_sub_coordinate_pos
          K v x qA.2.1 qA.2.2
        dsimp [p, c] at heqx
        simp [AffineMap.lineMap_apply,
          triangulationTopologicalGeometricVertex] at heqx
        field_simp at heqx
        rcases heqx with ((h | h) | h) | h
        · exact (ne_of_gt hδ0) h
        · exact hz0 h
        · exact (ne_of_gt hrA) h
        · nlinarith
      have htrans :
          edgeRadialCircleTransversePoint K v x qA qB δ hδ0 hδA hδB z =
            ⟨p, hp⟩ := by
        apply Subtype.ext
        dsimp [edgeRadialCircleTransversePoint, p, c]
        simp [hz.le]
      rw [htrans]
      rw [hgA ⟨p, hp⟩ hpne hpA]
      dsimp [p, c]
      simp [AffineMap.lineMap_apply, triangulationTopologicalGeometricVertex]
      field_simp
      ring

    · have hzneg : z.1.im < 0 := lt_of_le_of_ne (le_of_not_gt hz) hz0
      have hrB : 0 < 1 - qB.1 x := lt_trans hδ0 hδB
      let c := δ * (-z.1.im) / (1 - qB.1 x)
      have hc0 : 0 < c := div_pos (mul_pos hδ0 (neg_pos.mpr hzneg)) hrB
      have him : -z.1.im ≤ 1 := by
        calc -z.1.im ≤ |z.1.im| := neg_le_abs _
          _ ≤ ‖(z.1 : ℂ)‖ := Complex.abs_im_le_norm _
          _ = 1 := Circle.norm_coe z
      have hc1 : c ≤ 1 := by
        apply (div_le_one hrB).2
        nlinarith
      obtain ⟨hp, hpB⟩ :=
        IsClopen.vertexLinkStar_radial_mem K v x hBcl qB hqB hc0 hc1
      let p := (AffineMap.lineMap
        (triangulationTopologicalGeometricVertex x) qB.1) c
      have hpne : p ≠ triangulationTopologicalGeometricVertex x := by
        intro heq
        have heqx := congrFun heq x
        have hrad := triangulationTopologicalVertexLinkStar_one_sub_coordinate_pos
          K v x qB.2.1 qB.2.2
        dsimp [p, c] at heqx
        simp [AffineMap.lineMap_apply,
          triangulationTopologicalGeometricVertex] at heqx
        field_simp at heqx
        rcases heqx with ((h | h) | h) | h
        · exact (ne_of_gt hδ0) h
        · exact hz0 h
        · exact (ne_of_gt hrB) h
        · nlinarith
      have htrans :
          edgeRadialCircleTransversePoint K v x qA qB δ hδ0 hδA hδB z =
            ⟨p, hp⟩ := by
        apply Subtype.ext
        dsimp [edgeRadialCircleTransversePoint, p, c]
        simp [not_le.mpr hzneg]
      rw [htrans]
      rw [hgB ⟨p, hp⟩ hpne hpB]
      dsimp [p, c]
      simp [AffineMap.lineMap_apply, triangulationTopologicalGeometricVertex]
      field_simp
      ring

/-- The explicit small-circle inclusion is a genuine right inverse of the
normalized radial circle map. -/
theorem edgeRadialCircleMap_comp_edgeRadialCircleInclusion
    (K : Triangulation) {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x)
    (A B : Set ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (hAcl : IsClopen A) (hBcl : IsClopen B)
    (qA qB : ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (hqA : qA ∈ A) (hqB : qB ∈ B)
    (g : ↑(triangulationTopologicalVertexLinkStar K v x) → ℝ)
    (habs : ∀ q, |g q| = 1 - q.1 x)
    (hgA : ∀ q (hq : q.1 ≠ triangulationTopologicalGeometricVertex x),
      (⟨q.1, q.2, hq⟩ :
        ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∈ A →
        g q = 1 - q.1 x)
    (hgB : ∀ q (hq : q.1 ≠ triangulationTopologicalGeometricVertex x),
      (⟨q.1, q.2, hq⟩ :
        ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∈ B →
        g q = -(1 - q.1 x))
    (δ : ℝ) (hδ0 : 0 < δ) (hδquarter : δ < (4 : ℝ)⁻¹)
    (hδA : δ < 1 - qA.1 x) (hδB : δ < 1 - qB.1 x)
    (z : Circle) :
    edgeRadialCircleMap K hrep g habs
        (edgeRadialCircleInclusion K hrep qA qB δ hδ0 hδquarter hδA hδB z) = z := by
  apply Subtype.ext
  have hg := edgeRadialCircleTransversePoint_signedCoordinate
    K v x A B hAcl hBcl qA qB hqA hqB g habs hgA hgB
      δ hδ0 hδA hδB z
  dsimp [edgeRadialCircleMap, edgeRadialCircleInclusion,
    triangulationTopologicalOpenEdgeTransverseStarPoint]
  rw [hg]
  have hcomplex :
      ((δ * z.1.re : ℝ) : ℂ) + ((δ * z.1.im : ℝ) : ℂ) * Complex.I =
        (δ : ℂ) * z.1 := by
    apply Complex.ext <;> simp
  rw [show ((2 : ℝ)⁻¹ + δ * z.1.re) - (2 : ℝ)⁻¹ =
      δ * z.1.re by ring, hcomplex, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_of_nonneg hδ0.le]
  exact (div_eq_iff (Complex.ofReal_ne_zero.mpr (ne_of_gt hδ0))).2
    (mul_comm _ _)

/-- If the transverse star of a represented edge is disconnected, deleting
its midpoint from the genuine open-edge neighborhood leaves a space which is
not simply connected. -/
theorem openEdgeNeighborhood_delete_midpoint_not_simplyConnected
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x)
    (hnot : ¬ VertexLinkStarConnected K v x) :
    ¬ SimplyConnectedSpace
      ↑({⟨triangulationTopologicalCarrierEdgeMidpoint K v x hrep,
          triangulationTopologicalCarrierEdgeMidpoint_mem_openEdgeNeighborhood
            K hcore hrep⟩}ᶜ :
        Set ↑(triangulationTopologicalOpenEdgeNeighborhood K v x)) := by
  obtain ⟨A, B, hAcl, hBcl, hAne, hBne, -, -, g, hg, habs, hgA, hgB⟩ :=
    exists_continuous_signedRadialCoordinate_of_not_starConnected
      K hcore v x hrep hnot
  obtain ⟨qA, hqA, qB, hqB, hrA, hrB, -, -⟩ :=
    exists_edgeRadial_opposite_side_witnesses
      K v x A B hAne hBne g hgA hgB
  obtain ⟨δ, hδ0, hδquarter, hδA, hδB⟩ :=
    exists_edgeRadial_circleScale hrA hrB
  let i : C(Circle,
      ↑({triangulationTopologicalOpenEdgeRadialMidpoint K hrep}ᶜ : Set
        {tq : ↑(Set.Ico (0 : ℝ) 1) ×
            ↑(triangulationTopologicalVertexLink K v) |
          0 < tq.1.1 ∧ 0 < tq.2.1 x})) :=
    ⟨edgeRadialCircleInclusion
        K hrep qA qB δ hδ0 hδquarter hδA hδB,
      continuous_edgeRadialCircleInclusion
        K hrep qA qB δ hδ0 hδquarter hδA hδB⟩
  let r : C(
      ↑({triangulationTopologicalOpenEdgeRadialMidpoint K hrep}ᶜ : Set
        {tq : ↑(Set.Ico (0 : ℝ) 1) ×
            ↑(triangulationTopologicalVertexLink K v) |
          0 < tq.1.1 ∧ 0 < tq.2.1 x}), Circle) :=
    ⟨edgeRadialCircleMap K hrep g habs,
      continuous_edgeRadialCircleMap K hrep g hg habs⟩
  have hradial : ¬ SimplyConnectedSpace
      ↑({triangulationTopologicalOpenEdgeRadialMidpoint K hrep}ᶜ : Set
        {tq : ↑(Set.Ico (0 : ℝ) 1) ×
            ↑(triangulationTopologicalVertexLink K v) |
          0 < tq.1.1 ∧ 0 < tq.2.1 x}) :=
    not_simplyConnectedSpace_of_circle_retract i r fun z ↦
      edgeRadialCircleMap_comp_edgeRadialCircleInclusion
        K hrep A B hAcl hBcl qA qB hqA hqB g habs hgA hgB
          δ hδ0 hδquarter hδA hδB z
  let e0 := triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLinkCarrier
    K hcore hrep
  let e :
      ↑({triangulationTopologicalOpenEdgeRadialMidpoint K hrep}ᶜ : Set
        {tq : ↑(Set.Ico (0 : ℝ) 1) ×
            ↑(triangulationTopologicalVertexLink K v) |
          0 < tq.1.1 ∧ 0 < tq.2.1 x}) ≃ₜ
      ↑({⟨triangulationTopologicalCarrierEdgeMidpoint K v x hrep,
          triangulationTopologicalCarrierEdgeMidpoint_mem_openEdgeNeighborhood
            K hcore hrep⟩}ᶜ :
        Set ↑(triangulationTopologicalOpenEdgeNeighborhood K v x)) :=
    e0.subtype fun tq ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rw [← triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLinkCarrier_midpoint
        K hcore hrep]
      exact e0.injective.eq_iff.not.symm
  intro hcarrier
  letI : SimplyConnectedSpace
      ↑({⟨triangulationTopologicalCarrierEdgeMidpoint K v x hrep,
          triangulationTopologicalCarrierEdgeMidpoint_mem_openEdgeNeighborhood
            K hcore hrep⟩}ᶜ :
        Set ↑(triangulationTopologicalOpenEdgeNeighborhood K v x)) := hcarrier
  haveI : SimplyConnectedSpace
      ↑({triangulationTopologicalOpenEdgeRadialMidpoint K hrep}ᶜ : Set
        {tq : ↑(Set.Ico (0 : ℝ) 1) ×
            ↑(triangulationTopologicalVertexLink K v) |
          0 < tq.1.1 ∧ 0 < tq.2.1 x}) :=
    e.toHomotopyEquiv.simplyConnectedSpace
  exact hradial inferInstance

/-- The ambient-coordinate family underlying the small radial circles.  Unlike
`edgeRadialCircleInclusion`, it is also defined at scale zero; there the whole
circle collapses to the radial midpoint.  Keeping this preliminary family in
the ambient product avoids putting positivity proofs into the parameter type.
-/
noncomputable def edgeRadialCircleAmbientFamily
    (x : Nat) (qA qB : Nat → ℝ) (δz : ℝ × Circle) : ℝ × (Nat → ℝ) :=
  let δ := δz.1
  let z := δz.2
  let q := if 0 ≤ z.1.im then
      (AffineMap.lineMap (triangulationTopologicalGeometricVertex x) qA)
        (δ * z.1.im / (1 - qA x))
    else
      (AffineMap.lineMap (triangulationTopologicalGeometricVertex x) qB)
        (δ * (-z.1.im) / (1 - qB x))
  ((2 : ℝ)⁻¹ + δ * z.1.re, q)

/-- The small radial-circle formula is jointly continuous in its scale and
circle variables, including at scale zero. -/
theorem continuous_edgeRadialCircleAmbientFamily
    (x : Nat) (qA qB : Nat → ℝ) :
    Continuous (edgeRadialCircleAmbientFamily x qA qB) := by
  apply Continuous.prodMk
  · fun_prop
  · dsimp only [edgeRadialCircleAmbientFamily]
    apply continuous_if_le continuous_const
      (Complex.continuous_im.comp
        (continuous_subtype_val.comp continuous_snd))
    · fun_prop
    · fun_prop
    · intro δz hz
      change 0 = δz.2.1.im at hz
      rw [← hz]
      simp [AffineMap.lineMap_apply]

/-- At scale zero the joint family is exactly the radial midpoint, uniformly
in the circle variable. -/
@[simp] theorem edgeRadialCircleAmbientFamily_zero
    (x : Nat) (qA qB : Nat → ℝ) (z : Circle) :
    edgeRadialCircleAmbientFamily x qA qB (0, z) =
      ((2 : ℝ)⁻¹, triangulationTopologicalGeometricVertex x) := by
  simp [edgeRadialCircleAmbientFamily, AffineMap.lineMap_apply]

/-- Every neighborhood of the radial midpoint contains all members of the
small-circle family at every sufficiently small scale.  Compactness of the
circle makes the scale bound uniform in the circle variable. -/
theorem eventually_edgeRadialCircleAmbientFamily_mem_of_mem_nhds
    (x : Nat) (qA qB : Nat → ℝ)
    (U : Set (ℝ × (Nat → ℝ)))
    (hU : U ∈ nhds (((2 : ℝ)⁻¹,
      triangulationTopologicalGeometricVertex x))) :
    ∀ᶠ δ in nhds (0 : ℝ), ∀ z : Circle,
      edgeRadialCircleAmbientFamily x qA qB (δ, z) ∈ U := by
  have hpoint : ∀ z : Circle,
      ∀ᶠ δz : ℝ × Circle in nhds ((0 : ℝ), z),
        edgeRadialCircleAmbientFamily x qA qB δz ∈ U := by
    intro z
    have hU' : U ∈ nhds
        (edgeRadialCircleAmbientFamily x qA qB ((0 : ℝ), z)) := by
      rw [edgeRadialCircleAmbientFamily_zero]
      exact hU
    exact (continuous_edgeRadialCircleAmbientFamily x qA qB).continuousAt.eventually hU'
  simpa only [Set.mem_univ, forall_const] using
    (isCompact_univ.eventually_forall_of_forall_eventually
      (K := (Set.univ : Set Circle)) (x₀ := (0 : ℝ)) (P := fun δ z ↦
        edgeRadialCircleAmbientFamily x qA qB (δ, z) ∈ U)
      (fun z _ ↦ hpoint z))

/-- Every ambient neighborhood of the radial midpoint contains a genuine
small circle satisfying all the bounds required by `edgeRadialCircleInclusion`.
This is the quantitative packaging of uniform shrinking used to restrict the
circle retract to arbitrarily small edge neighborhoods. -/
theorem exists_edgeRadial_circleScale_image_subset
    (K : Triangulation) (v x : Nat)
    (qA qB : ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (U : Set (ℝ × (Nat → ℝ)))
    (hU : U ∈ nhds (((2 : ℝ)⁻¹,
      triangulationTopologicalGeometricVertex x))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (4 : ℝ)⁻¹ ∧
      δ < 1 - qA.1 x ∧ δ < 1 - qB.1 x ∧
      ∀ z : Circle, edgeRadialCircleAmbientFamily x qA.1 qB.1 (δ, z) ∈ U := by
  have hrA : 0 < 1 - qA.1 x :=
    triangulationTopologicalVertexLinkStar_one_sub_coordinate_pos
      K v x qA.2.1 qA.2.2
  have hrB : 0 < 1 - qB.1 x :=
    triangulationTopologicalVertexLinkStar_one_sub_coordinate_pos
      K v x qB.2.1 qB.2.2
  obtain ⟨δ0, hδ0, hδquarter, hδA, hδB⟩ :=
    exists_edgeRadial_circleScale hrA hrB
  let S : Set ℝ := {δ | ∀ z : Circle,
    edgeRadialCircleAmbientFamily x qA.1 qB.1 (δ, z) ∈ U}
  have hS : S ∈ nhds (0 : ℝ) :=
    eventually_edgeRadialCircleAmbientFamily_mem_of_mem_nhds
      x qA.1 qB.1 U hU
  obtain ⟨ε, hε0, hεS⟩ := Metric.mem_nhds_iff.mp hS
  let δ := min δ0 (ε / 2)
  have hδpos : 0 < δ := lt_min hδ0 (half_pos hε0)
  have hδle : δ ≤ δ0 := min_le_left _ _
  have hδε : δ < ε :=
    (min_le_right δ0 (ε / 2)).trans_lt (half_lt_self hε0)
  refine ⟨δ, hδpos, hδle.trans_lt hδquarter,
    hδle.trans_lt hδA, hδle.trans_lt hδB, ?_⟩
  exact hεS (by simpa [Real.dist_eq, abs_of_pos hδpos] using hδε)


end Poincare
