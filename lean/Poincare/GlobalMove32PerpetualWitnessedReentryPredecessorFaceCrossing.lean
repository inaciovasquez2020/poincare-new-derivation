import Poincare.GlobalMove32PerpetualWitnessedReentryRecurrentCrossing
import Poincare.GlobalMove32ReentryPredecessorSourceFaceObstruction

namespace Poincare

/--
Under the global no-degree-four hypotheses, perpetual witnessed incidence-three
Move32 reentry produces a nonconsecutive recurrent return to an earlier
supported shared edge together with the full certified crossing geometry.

Moreover, the source face of the predecessor immediately before that returned
edge cannot have the same unordered support as the earlier anchor source face.

Thus the recurrent return is not merely nonconsecutive: it is forced to
approach the returned anchor edge through a genuinely different predecessor
source face.
-/
theorem
    ClosedTriangulationCore.exists_finite_recurrent_return_crossing_with_predecessor_sourceFace_ne_of_perpetual_witnessedReentry_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn :
      TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (sites : ℕ → Move32Site)
    (hrealized :
      ∀ n,
        (sites n).RealizedIn K)
    (hthree :
      ∀ n,
        (sites n).SharedEdgeExactlyThree K)
    (hwitnessed :
      ∀ n,
        Move32SourceFaceWitnessedReentry
          K (sites n) (sites (n + 1))) :
    ∃ i k tau rho sigma,
      i + 1 < k + 1 ∧
      k + 1 ≤ Fintype.card (SupportedEdgeState K) ∧
      ((tau ∈ K.tets ∧
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
         SameTetVertices sigma (sites i).targetTet₂)) ∧
       ¬ (∀ z : Nat,
          z ∈ [(sites k).a, (sites k).b, (sites k).c] ↔
          z ∈ [(sites i).a, (sites i).b, (sites i).c])) := by

  obtain ⟨i, k, hgap, hbound, hstate, hstep, hreturn⟩ :=
    hcore.exists_recurrent_returnSigma_target_of_perpetual_witnessedReentry
      sites
      hrealized
      hthree
      hwitnessed

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

  have hreturnEdge :
      (((sites (k + 1)).d = (sites i).d ∧
          (sites (k + 1)).e = (sites i).e) ∨
        ((sites (k + 1)).d = (sites i).e ∧
          (sites (k + 1)).e = (sites i).d)) := by
    obtain ⟨_, _, _, hcross⟩ :=
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
    aesop

  have hpred :
      ¬ (∀ z : Nat,
        z ∈ [(sites k).a, (sites k).b, (sites k).c] ↔
        z ∈ [(sites i).a, (sites i).b, (sites i).c]) :=
    hcore.not_predecessor_sourceFace_support_eq_anchor_of_witnessedReentry_return_edge_of_no_degree_four
      hlinks
      hconn
      hNoFour
      (sites i)
      (sites k)
      (sites (k + 1))
      (hrealized i)
      hstep
      hreturnEdge

  exact
    ⟨i, k, tau, rho, sigma,
      hgap,
      hbound,
      hconfig,
      hpred⟩

end Poincare
