import Poincare.TriangulationTopologicalVertexLinkStarConnectedness
import Poincare.TriangulationTopologicalGeometricDecomposition

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

end Poincare
