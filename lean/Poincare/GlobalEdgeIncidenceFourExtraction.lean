import Poincare.GlobalRepresentedEdgeIncidenceSplit
import Mathlib.Tactic

namespace Poincare

/-- Incidence at least four exposes four pairwise distinct represented
tetrahedra containing the edge.  This is the unordered finite input for a
subsequent cyclic edge-fan ordering theorem. -/
theorem ClosedTriangulationCore.exists_four_distinct_tets_containing_edge_of_four_le
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hfour :
      4 ≤ (K.tets.filter (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length) :
    ∃ tau0 tau1 tau2 tau3,
      tau0 ∈ K.tets ∧ tau1 ∈ K.tets ∧ tau2 ∈ K.tets ∧ tau3 ∈ K.tets ∧
      v ∈ tau0.verts ∧ x ∈ tau0.verts ∧
      v ∈ tau1.verts ∧ x ∈ tau1.verts ∧
      v ∈ tau2.verts ∧ x ∈ tau2.verts ∧
      v ∈ tau3.verts ∧ x ∈ tau3.verts ∧
      tau0 ≠ tau1 ∧ tau0 ≠ tau2 ∧ tau0 ≠ tau3 ∧
      tau1 ≠ tau2 ∧ tau1 ≠ tau3 ∧ tau2 ≠ tau3 := by
  classical
  let edgeTets :=
    K.tets.filter (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)
  have hedgeNodup : edgeTets.Nodup := by
    have hKtets : K.tets.Nodup := by
      rw [List.nodup_iff_pairwise_ne]
      exact hcore.2.1.imp (fun {tau rho} hne heq => by
        subst rho
        exact hne (sameTetVertices_refl tau))
    exact hKtets.filter _
  have hedgeLength : 4 ≤ edgeTets.length := by
    simpa [edgeTets] using hfour
  cases hedge : edgeTets with
  | nil => simp [hedge] at hedgeLength
  | cons tau0 rest0 =>
    cases rest0 with
    | nil => simp [hedge] at hedgeLength
    | cons tau1 rest1 =>
      cases rest1 with
      | nil => simp [hedge] at hedgeLength
      | cons tau2 rest2 =>
        cases rest2 with
        | nil => simp [hedge] at hedgeLength
        | cons tau3 rest3 =>
          have h0 : tau0 ∈ edgeTets := by simp [hedge]
          have h1 : tau1 ∈ edgeTets := by simp [hedge]
          have h2 : tau2 ∈ edgeTets := by simp [hedge]
          have h3 : tau3 ∈ edgeTets := by simp [hedge]
          have hn : [tau0, tau1, tau2, tau3].Nodup := by
            exact hedgeNodup.sublist (by simp [hedge])
          have h0' : tau0 ∈ K.tets ∧ v ∈ tau0.verts ∧ x ∈ tau0.verts := by
            simpa [edgeTets] using h0
          have h1' : tau1 ∈ K.tets ∧ v ∈ tau1.verts ∧ x ∈ tau1.verts := by
            simpa [edgeTets] using h1
          have h2' : tau2 ∈ K.tets ∧ v ∈ tau2.verts ∧ x ∈ tau2.verts := by
            simpa [edgeTets] using h2
          have h3' : tau3 ∈ K.tets ∧ v ∈ tau3.verts ∧ x ∈ tau3.verts := by
            simpa [edgeTets] using h3
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
            or_false] at hn
          refine ⟨tau0, tau1, tau2, tau3,
            h0'.1, h1'.1, h2'.1, h3'.1,
            h0'.2.1, h0'.2.2, h1'.2.1, h1'.2.2,
            h2'.2.1, h2'.2.2, h3'.2.1, h3'.2.2, ?_⟩
          aesop

end Poincare
