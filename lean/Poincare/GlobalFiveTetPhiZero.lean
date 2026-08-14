import Poincare.GlobalFiveTetDegreeFourConverse
import Poincare.SupportDegreeFour

namespace Poincare

/-- If the represented tetrahedra are covered by five fixed tetrahedra, then
every represented vertex of a closed core has degree four.  Consequently the
support defect vanishes. -/
theorem ClosedTriangulationCore.PhiSupport_eq_zero_of_five_tet_cover
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (tau0 tau1 tau2 tau3 target : Tet)
    (hglobal :
      ∀ rho ∈ K.tets,
        rho = tau0 ∨ rho = tau1 ∨ rho = tau2 ∨
          rho = tau3 ∨ rho = target) :
    PhiSupport K = 0 := by
  classical
  have hnodup : K.tets.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hcore.2.1.imp (fun {x y} hxy h => by
      subst y
      exact hxy (sameTetVertices_refl x))
  let C : Finset Tet := {tau0, tau1, tau2, tau3, target}
  have hsubset : K.tets.toFinset ⊆ C := by
    intro rho hrho
    rcases hglobal rho (List.mem_toFinset.mp hrho) with
      rfl | rfl | rfl | rfl | rfl <;> simp [C]
  have hlength : K.tets.length ≤ 5 := by
    rw [← List.toFinset_card_of_nodup hnodup]
    apply le_trans (Finset.card_le_card hsubset)
    have h0 := Finset.card_insert_le tau0
      ({tau1, tau2, tau3, target} : Finset Tet)
    have h1 := Finset.card_insert_le tau1
      ({tau2, tau3, target} : Finset Tet)
    have h2 := Finset.card_insert_le tau2
      ({tau3, target} : Finset Tet)
    have h3 := Finset.card_insert_le tau3 ({target} : Finset Tet)
    simp only [Finset.card_singleton] at h3
    dsimp [C]
    omega
  rw [PhiSupport_zero_iff_vertexDegree_eq_four]
  intro v hv
  have hcount : vertexDegree K v ≤ K.tets.length := by
    rw [hcore.vertexDegree_eq_incidentTetCount v]
    exact List.length_filter_le _ _
  rcases hcore.vertexDegree_eq_four_or_ge_six_of_mem_vertexSupport hv with
    hfour | hsix
  · exact hfour
  · omega

/-- The global five-tetrahedron terminal branch is incompatible with positive
support defect. -/
theorem ClosedTriangulationCore.not_five_tet_cover_of_PhiSupport_pos
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hphi : 0 < PhiSupport K)
    (tau0 tau1 tau2 tau3 target : Tet)
    (hglobal :
      ∀ rho ∈ K.tets,
        rho = tau0 ∨ rho = tau1 ∨ rho = tau2 ∨
          rho = tau3 ∨ rho = target) :
    False := by
  have := hcore.PhiSupport_eq_zero_of_five_tet_cover
    tau0 tau1 tau2 tau3 target hglobal
  omega

end Poincare
