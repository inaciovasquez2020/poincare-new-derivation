import Poincare.Validity
import Poincare.SupportDegreeFour

namespace Poincare

/-- In a closed triangulation, the multiplicity definition of vertex degree
agrees with the number of tetrahedra incident to the vertex. -/
theorem ClosedTriangulationCore.vertexDegree_eq_incidentTetCount
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v : Nat) :
    vertexDegree K v =
      (K.tets.filter (fun τ => v ∈ τ.verts)).length := by
  have haux : ∀ tets : List Tet,
      (∀ τ ∈ tets, τ.verts.Nodup) →
      (tets.flatMap Tet.verts).count v =
        (tets.filter (fun τ => v ∈ τ.verts)).length := by
    intro tets hnodup
    induction tets with
    | nil => simp
    | cons τ tets ih =>
        have hτ : τ.verts.Nodup := hnodup τ (by simp)
        have htets : ∀ ρ ∈ tets, ρ.verts.Nodup := by
          intro ρ hρ
          exact hnodup ρ (by simp [hρ])
        by_cases hv : v ∈ τ.verts
        · rw [List.flatMap_cons, List.count_append,
            List.count_eq_one_of_mem hτ hv, ih htets]
          simp [hv, Nat.add_comm]
        · have hcount : τ.verts.count v = 0 := by
            simpa [hv] using (List.Nodup.count (a := v) hτ)
          rw [List.flatMap_cons, List.count_append, hcount, ih htets]
          simp [hv]
  exact haux K.tets hcore.1

/-- At vanishing support defect, every represented vertex is incident to
exactly four tetrahedra. -/
theorem ClosedTriangulationCore.incidentTetCount_eq_four_of_PhiSupport_eq_zero
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v : Nat}
    (hPhi : PhiSupport K = 0)
    (hv : v ∈ vertexSupport K) :
    (K.tets.filter (fun τ => v ∈ τ.verts)).length = 4 := by
  rw [← hcore.vertexDegree_eq_incidentTetCount v]
  exact (PhiSupport_zero_iff_vertexDegree_eq_four K).mp hPhi v hv

end Poincare
