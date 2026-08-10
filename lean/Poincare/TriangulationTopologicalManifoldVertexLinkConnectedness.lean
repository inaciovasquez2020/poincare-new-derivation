import Poincare.TriangulationTopologicalManifoldPuncturedNeighborhood

open Set

namespace Poincare

/-- A non-apex point of a represented vertex star has apex coordinate strictly
less than one. -/
theorem triangulationTopologicalVertexStar_coordinate_lt_one_of_ne_vertex
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    {v : Nat}
    {p : Nat → ℝ}
    (hp : p ∈ triangulationTopologicalVertexStar K v)
    (hne : p ≠ triangulationTopologicalGeometricVertex v) :
    p v < 1 := by
  classical
  obtain ⟨tau, htau, hvtau, hpbody⟩ :=
    (mem_triangulationTopologicalVertexStar_iff K v p).1 hp
  obtain ⟨sigma, _hsigmalink, hsigmaextract⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem K v tau htau hvtau
  let e := triangulationTopologicalGeometricVertex v
  let S : Set (Nat → ℝ) :=
    triangulationTopologicalGeometricVertex ''
      (↑sigma.verts.toFinset : Set Nat)
  have hSnonempty : S.Nonempty := by
    refine ⟨triangulationTopologicalGeometricVertex sigma.v0, ?_⟩
    exact ⟨sigma.v0, by simp [LinkTriangle.verts], rfl⟩
  rw [triangulationTopologicalGeometricVertex_image_tet_eq_insert_linkTriangle
    tau v sigma hsigmaextract, convexHull_insert hSnonempty] at hpbody
  obtain ⟨x, hx, q, hqS, hpseg⟩ := mem_convexJoin.mp hpbody
  have hxe : x = e := by simpa using hx
  subst x
  obtain ⟨a, b, ha, hb, hab, hpab⟩ := hpseg
  have hvnotSigma : v ∉ sigma.verts :=
    tau.linkTriangleAt?_vertex_not_mem v sigma (hcore.1 tau htau) hsigmaextract
  have hqv : q v = 0 := by
    apply convexHull_min _ (convex_hyperplane
      ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hqS
    rintro _ ⟨y, hy, rfl⟩
    have hyv : y ≠ v := by
      intro hyv
      subst y
      exact hvnotSigma (List.mem_toFinset.mp hy)
    simp [triangulationTopologicalGeometricVertex, hyv]
  have hpva : p v = a := by
    rw [← hpab]
    simp [triangulationTopologicalGeometricVertex, hqv]
  have ha_le : a ≤ 1 := by linarith
  rw [hpva]
  apply lt_of_le_of_ne ha_le
  intro ha1
  have hb0 : b = 0 := by linarith
  apply hne
  rw [← hpab, ha1, hb0]
  simp

/-- For an honest topological three-manifold triangulation, the represented
vertex link is connected in its actual ambient Pi-space. -/
theorem triangulationTopologicalVertexLink_isConnected_of_topologicalThreeManifold
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (hM :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v : Nat}
    (hv : v ∈ vertexSupport K) :
    IsConnected (triangulationTopologicalVertexLink K v) := by
  obtain ⟨U, hUopen, hxU, hUstar, hCconnected⟩ :=
    triangulationTopological_exists_open_punctured_connected_neighborhood
      K hM hv
  let x := triangulationTopologicalCarrierVertex K v hv
  let C : Set (triangulationTopologicalGeometricCarrier K) := U \ {x}
  let G : ↥C → ↥{p : Nat → ℝ |
      p ∈ triangulationTopologicalVertexStar K v ∧ p v < 1} := fun p ↦
    ⟨p.1.1, hUstar p.1 p.2.1,
      triangulationTopologicalVertexStar_coordinate_lt_one_of_ne_vertex
        K hcore (hUstar p.1 p.2.1) (by
          intro hp
          apply p.2.2
          apply Subtype.ext
          simpa [x, triangulationTopologicalCarrierVertex] using hp)⟩
  have hG : Continuous G := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  let e :=
    triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink K hcore v
  let F : ↥C → ↥(triangulationTopologicalVertexLink K v) := fun p ↦
    (e.symm (G p)).2
  have hF : Continuous F := by
    exact continuous_snd.comp (e.symm.continuous.comp hG)
  have hFsurj : Function.Surjective F := by
    intro q
    obtain ⟨t, htU⟩ :=
      triangulationTopological_open_mem_apex_intersects_radialRay
        K hcore hv q hUopen hxU
    let r := triangulationTopologicalRadialCarrierPoint K v t q
    have hrne : r ≠ x := by
      exact triangulationTopologicalRadialCarrierPoint_ne_carrierVertex
        K hcore hv t q
    let rC : ↥C := ⟨r, htU, hrne⟩
    have hGr : G rC = e (t, q) := by
      apply Subtype.ext
      change (triangulationTopologicalRadialCarrierPoint K v t q).1 =
        ((triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
          K hcore v) (t, q)).1
      rw [triangulationTopologicalRadialCarrierPoint_val,
        triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink_apply_val]
    refine ⟨rC, ?_⟩
    change (e.symm (G rC)).2 = q
    rw [hGr]
    exact congrArg Prod.snd (e.symm_apply_apply (t, q))
  letI : ConnectedSpace ↥C := by
    apply Subtype.connectedSpace
    simpa [C, x] using hCconnected
  haveI : ConnectedSpace ↥(triangulationTopologicalVertexLink K v) :=
    hFsurj.connectedSpace hF
  have hsubtype : IsConnected
      (Set.univ : Set ↥(triangulationTopologicalVertexLink K v)) :=
    isConnected_univ
  simpa only [Set.image_univ, Subtype.range_val] using
    hsubtype.image
      ((↑) : ↥(triangulationTopologicalVertexLink K v) → Nat → ℝ)
      continuous_subtype_val.continuousOn

end Poincare
