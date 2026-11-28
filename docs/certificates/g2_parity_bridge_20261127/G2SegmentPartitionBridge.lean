/-!
Append-only candidate for a temporary copy of
research/candidates/G2PiecewisePrimalLoopCancellation.lean
from PR #200 at 36df38d563014164bf288d17448255de4817abb8.
The enclosing file must also import Poincare.CarrierPolygonalPath.
NOT_RUN: this is not a standalone Lean module or a kernel certificate.
The exact orderedTransitionPath_closed_partition source is unavailable;
its arc-coverage conclusion is exposed as hcover, not claimed discharged.
-/

namespace Poincare

/-- Convert an ordered partition of canonical vertex-to-vertex carrier
segments into the piecewise-affine hypotheses of the G2 cancellation theorem.
The null homotopy is supplied by actual carrier simple connectivity. -/
theorem g2_closed_primal_walk_pairing_zero_of_segment_partition
    {K : Triangulation}
    (hSC : TriangulationRealizationSimplyConnected K)
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ u, w u u = 0)
    (hsym : ∀ u v, w u v = w v u)
    (htri : ∀ tau : Tet, ∀ a b c : Nat,
      a ∈ tau.verts → b ∈ tau.verts → c ∈ tau.verts →
      w a b + w b c + w c a = 0)
    (m : Nat) (hm : 0 < m)
    (vertex : Nat → Nat)
    (p : Nat → triangulationTopologicalGeometricCarrier K)
    (hp : ∀ k, k ≤ m →
      (p k).1 = triangulationTopologicalGeometricVertex (vertex k))
    (tau : Nat → Tet)
    (htau : ∀ k, k < m → tau k ∈ K.tets)
    (hleft : ∀ k, k < m →
      (p k).1 ∈ triangulationTopologicalTetBody (tau k))
    (hright : ∀ k, k < m →
      (p (k+1)).1 ∈ triangulationTopologicalTetBody (tau k))
    (loop : Path (p 0) (p 0))
    (time : Nat → unitInterval)
    (hfirst : time 0 = 0) (hlast : time m = 1)
    (horder : ∀ k, k < m → (time k : ℝ) < (time (k+1) : ℝ))
    (hdistinct : ∀ k, k < m → vertex k ≠ vertex (k+1))
    (hvisit : ∀ k, k ≤ m → loop (time k) = p k)
    (hcover : ∀ k (hk : k < m), ∀ q : unitInterval,
      (time k : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ (time (k+1) : ℝ) →
      ∃ t : unitInterval, loop q =
        carrierSegmentInTet K (tau k) (htau k hk) (p k) (p (k+1))
          (hleft k hk) (hright k hk) t) :
    (∑ k ∈ Finset.range m, w (vertex k) (vertex (k+1))) = 0 := by
  obtain ⟨H⟩ := exists_carrierLoopNullHomotopyData hSC loop
  apply g2_piecewise_primal_loop_pairing_zero H w hzero hsym htri
    m hm vertex time hfirst hlast horder hdistinct
  · intro k hk
    rw [hvisit k hk, hp k hk]
  · intro k hk q hq0 hq1
    obtain ⟨t, ht⟩ := hcover k hk q hq0 hq1
    refine ⟨(t : ℝ), ?_⟩
    rw [ht, carrierSegmentInTet_coe, hp k (Nat.le_of_lt hk),
      hp (k+1) (by omega)]

#print axioms g2_closed_primal_walk_pairing_zero_of_segment_partition

end Poincare
