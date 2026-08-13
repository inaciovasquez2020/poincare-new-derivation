import Poincare.GlobalMove32WitnessedFiniteRecurrenceReturn
import Poincare.GlobalMove32ReentryReturnCrossingConfiguration
import Mathlib.Tactic

namespace Poincare

/--
A perpetual sequence of witnessed incidence-three Move32 source-face
reentries has a finite nonconsecutive return whose repeated supported-edge
state carries the full same-witness crossing geometry at the return step.

This is a finite recurrent configuration theorem only.  It does not assert
that such a recurrent configuration is impossible and does not prove
termination.
-/
theorem
    ClosedTriangulationCore.exists_finite_recurrent_return_crossing_configuration_of_perpetual_witnessedReentry
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (sites : ℕ → Move32Site)
    (hrealized : ∀ n, (sites n).RealizedIn K)
    (hthree : ∀ n, (sites n).SharedEdgeExactlyThree K)
    (hwitnessed :
      ∀ n,
        Move32SourceFaceWitnessedReentry
          K (sites n) (sites (n + 1))) :
    ∃ i k tau rho sigma,
      i + 1 < k + 1 ∧
      k + 1 ≤ Fintype.card (SupportedEdgeState K) ∧
      tau ∈ K.tets ∧
      rho ∈ K.tets ∧
      sigma ∈ K.tets ∧
      ¬ SameTetVertices tau rho ∧
      (sites k).a ∈ tau.verts ∧
      (sites k).b ∈ tau.verts ∧
      (sites k).c ∈ tau.verts ∧
      (sites k).a ∈ rho.verts ∧
      (sites k).b ∈ rho.verts ∧
      (sites k).c ∈ rho.verts ∧
      (sites (k + 1)).d ∈ tau.verts ∧
      (sites (k + 1)).e ∈ rho.verts ∧
      (sites (k + 1)).d ∈ sigma.verts ∧
      (sites (k + 1)).e ∈ sigma.verts ∧
      (sites (k + 1)).e ∉ tau.verts ∧
      (sites (k + 1)).d ∉ rho.verts ∧
      ¬ SameTetVertices sigma tau ∧
      ¬ SameTetVertices sigma rho ∧
      (((sites (k + 1)).d = (sites i).d ∧
          (sites (k + 1)).e = (sites i).e) ∨
       ((sites (k + 1)).d = (sites i).e ∧
          (sites (k + 1)).e = (sites i).d)) ∧
      (SameTetVertices sigma (sites i).targetTet₀ ∨
       SameTetVertices sigma (sites i).targetTet₁ ∨
       SameTetVertices sigma (sites i).targetTet₂) := by
  obtain ⟨i, k, hgap, hbound, hstate, hstep, _hreturn⟩ :=
    hcore.exists_recurrent_returnSigma_target_of_perpetual_witnessedReentry
      sites hrealized hthree hwitnessed

  obtain ⟨tau, rho, sigma, hconfig⟩ :=
    hcore.exists_witnessedReentry_return_crossing_anchor_target_of_sharedSupportedEdgeState_eq
      (sites i)
      (sites k)
      (sites (k + 1))
      (hrealized i)
      (hthree i)
      (hrealized k)
      (hrealized (k + 1))
      hstep
      hstate

  exact ⟨i, k, tau, rho, sigma, hgap, hbound, hconfig⟩

end Poincare
