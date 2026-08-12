import Poincare.TriangulationTopologicalManifoldVertexLinkConnectedness
import Poincare.TriangulationTopologicalVertexStarRadialAccess
import Poincare.CircleNotSimplyConnected

open Set Filter

namespace Poincare

theorem triangulationTopologicalVertexLink_simplyConnected_of_topologicalThreeManifold
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (hM :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v : Nat}
    (hv : v ∈ vertexSupport K) :
    IsSimplyConnected (triangulationTopologicalVertexLink K v) := by

  let x :=
    triangulationTopologicalCarrierVertex K v hv

  let N :=
    triangulationTopologicalTruncatedVertexStarNeighborhood K v

  have hNnhds : N ∈ nhds x := by
    simpa [N, x] using
      triangulationTopologicalTruncatedVertexStarNeighborhood_mem_nhds K hv

  obtain ⟨U, hUopen, hxU, hUN, hCsimply⟩ :=
    triangulationTopological_exists_open_punctured_simplyConnected_neighborhood_sub
      K hM x hNnhds

  have hUstar :
      ∀ p ∈ U,
        p.1 ∈ triangulationTopologicalVertexStar K v := by
    intro p hp
    apply
      triangulationTopologicalTruncatedVertexStarNeighborhood_subset_vertexStar
        K v
    exact hUN hp

  let C :
      Set (triangulationTopologicalGeometricCarrier K) :=
    U \ {x}

  haveI : SimplyConnectedSpace ↥C := by
    simpa [C] using hCsimply

  let G :
      ↥C →
        ↥{p : Nat → ℝ |
          p ∈ triangulationTopologicalVertexStar K v ∧
          p v < 1} :=
    fun p =>
      ⟨
        p.1.1,
        hUstar p.1 p.2.1,
        triangulationTopologicalVertexStar_coordinate_lt_one_of_ne_vertex
          K hcore
          (hUstar p.1 p.2.1)
          (by
            intro hp
            apply p.2.2
            apply Subtype.ext
            simpa [x, triangulationTopologicalCarrierVertex] using hp)
      ⟩

  have hG : Continuous G := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

  let e :=
    triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
      K hcore v

  let F :
      ↥C →
        ↥(triangulationTopologicalVertexLink K v) :=
    fun p =>
      (e.symm (G p)).2

  have hF : Continuous F := by
    exact continuous_snd.comp (e.symm.continuous.comp hG)

  obtain ⟨n, hnU⟩ :=
    triangulationTopological_exists_uniform_radialCarrierPoint_mem_of_mem_nhds
      K hcore hv
      (hUopen.mem_nhds hxU)

  let t :=
    triangulationTopologicalRadialApproachParameter n

  let I :
      ↥(triangulationTopologicalVertexLink K v) →
        ↥C :=
    fun q =>
      ⟨
        triangulationTopologicalRadialCarrierPoint K v t q,
        hnU q,
        by
          simpa [x] using
            (triangulationTopologicalRadialCarrierPoint_ne_carrierVertex
              K hcore hv t q)
      ⟩

  have hI : Continuous I := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change
      Continuous
        (fun q :
          ↥(triangulationTopologicalVertexLink K v) =>
            t.1 • triangulationTopologicalGeometricVertex v +
              (1 - t.1) • q.1)
    fun_prop

  have hFI :
      ∀ q : ↥(triangulationTopologicalVertexLink K v),
        F (I q) = q := by
    intro q

    have hGI :
        G (I q) = e (t, q) := by
      apply Subtype.ext
      change
        (triangulationTopologicalRadialCarrierPoint K v t q).1 =
        ((triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
          K hcore v) (t, q)).1
      rw [
        triangulationTopologicalRadialCarrierPoint_val,
        triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink_apply_val
      ]

    change (e.symm (G (I q))).2 = q
    rw [hGI]

    exact congrArg Prod.snd (e.symm_apply_apply (t, q))

  let i :
      C(
        ↥(triangulationTopologicalVertexLink K v),
        ↥C) :=
    ⟨I, hI⟩

  let r :
      C(
        ↥C,
        ↥(triangulationTopologicalVertexLink K v)) :=
    ⟨F, hF⟩

  haveI :
      SimplyConnectedSpace
        ↥(triangulationTopologicalVertexLink K v) :=
    simplyConnectedSpace_of_retract
      i r
      (by
        intro q
        exact hFI q)

  change
    SimplyConnectedSpace
      ↥(triangulationTopologicalVertexLink K v)

  exact inferInstance

end Poincare
