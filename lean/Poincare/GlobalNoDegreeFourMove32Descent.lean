import Poincare.GlobalPhiSupportDegreeGap
import Poincare.Move32TopologyPreservingDescent
import Mathlib.Tactic

namespace Poincare

private theorem
    mem_vertexSupport_iff_vertexDegree_pos_move32_local
    (K : Triangulation)
    (v : Nat) :
    v ∈ vertexSupport K ↔
      0 < vertexDegree K v := by
  rw [mem_vertexSupport_iff]
  change
    v ∈ allVerts K ↔
      0 < (allVerts K).count v
  simpa using
    ((Multiset.count_pos
      (a := v)
      (s := (↑(allVerts K) : Multiset Nat))).symm)

/--
In the no-degree-four branch of a closed core, both shared-edge endpoints
of every legal 3→2 move have degree at least six.
-/
theorem ClosedTriangulationCore.move32Site_sharedEdge_degrees_ge_six_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hlegal : s.LegalIn K) :
    6 ≤ vertexDegree K s.d ∧
      6 ≤ vertexDegree K s.e := by

  rcases
    hcore.move32Site_sharedEdge_vertexDegree_lower_bound
      s hlegal
    with ⟨hdLower, heLower⟩

  have hdPos :
      0 < vertexDegree K s.d := by
    omega

  have hePos :
      0 < vertexDegree K s.e := by
    omega

  have hdMem :
      s.d ∈ vertexSupport K :=
    (mem_vertexSupport_iff_vertexDegree_pos_move32_local
      K s.d).2 hdPos

  have heMem :
      s.e ∈ vertexSupport K :=
    (mem_vertexSupport_iff_vertexDegree_pos_move32_local
      K s.e).2 hePos

  have hdSix :
      6 ≤ vertexDegree K s.d :=
    hcore.vertexDegree_ge_six_of_mem_vertexSupport_of_ne_four
      hdMem
      (hNoFour s.d hdMem)

  have heSix :
      6 ≤ vertexDegree K s.e :=
    hcore.vertexDegree_ge_six_of_mem_vertexSupport_of_ne_four
      heMem
      (hNoFour s.e heMem)

  exact ⟨hdSix, heSix⟩

/--
Every legal 3→2 move is automatically a strict topology-preserving
PhiSupport descent in the closed-core branch with no degree-four
represented vertices.
-/
theorem ClosedTriangulationCore.move32Site_replace_topologyPreserving_descent_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hlegal : s.LegalIn K) :
    ClosedTriangulationCore (s.replace K) ∧
      PhiSupport (s.replace K) < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier
            (s.replace K)) := by

  rcases
    hcore.move32Site_sharedEdge_degrees_ge_six_of_no_degree_four
      hNoFour s hlegal
    with ⟨hdSix, heSix⟩

  exact
    hcore.move32Site_replace_topologyPreserving_descent
      s
      hlegal
      ⟨by omega, by omega, Or.inl hdSix⟩

/--
Existential form used directly by the global PhiSupport descent theorem.
-/
theorem exists_closedCore_homeomorphic_PhiSupport_lt_of_move32_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hlegal : s.LegalIn K) :
    ∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K') := by

  exact
    ⟨s.replace K,
      hcore.move32Site_replace_topologyPreserving_descent_of_no_degree_four
        hNoFour
        s
        hlegal⟩

end Poincare
