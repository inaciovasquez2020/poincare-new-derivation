import Poincare.G2PrimalEdgeCoordinateSupport

namespace Poincare

open CarrierLoopNullHomotopyData

/-- Strictly ordered parameters lie in weakly ordered boundary cells. -/
theorem g2_boundary_cell_index_mono
    (N : Nat) (hN : 0 < N)
    (a b : Fin N) (s t : unitInterval)
    (hst : (s : ℝ) < (t : ℝ))
    (ha : ((0 : unitInterval), s) ∈ squareGridCell N hN ⟨0,hN⟩ a)
    (hb : ((0 : unitInterval), t) ∈ squareGridCell N hN ⟨0,hN⟩ b) :
    a ≤ b := by
  by_contra hn
  have hba : (b : Nat) < (a : Nat) := by
    exact lt_of_not_ge hn
  have hba' : (b : ℝ) + 1 ≤ (a : ℝ) := by
    exact_mod_cast (show (b : Nat) + 1 ≤ (a : Nat) by omega)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsep : (squareGridParameter N hN b.succ : ℝ) ≤
      (squareGridParameter N hN a.castSucc : ℝ) := by
    change ((b.succ : Fin (N+1)) : ℝ) / N ≤ (a : ℝ) / N
    rw [show ((b.succ : Fin (N+1)) : ℝ) = (b : ℝ)+1 by norm_num]
    exact div_le_div_of_nonneg_right hba' hNr.le
  have hts : (t : ℝ) ≤ (s : ℝ) :=
    hb.2.2.2.trans (hsep.trans ha.2.2.1)
  exact (not_lt_of_ge hts) hst

/-- Distinct consecutive primal vertices at ordered parameters force strictly
ordered anchor cells in any genuinely positive-coordinate grid. -/
theorem g2_distinct_breakpoint_anchor_strict
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
      ∀ z ∈ squareGridCell N hN i j,
        0 < (H.homotopy z).1 (label i j))
    (a b : Fin N) (s t : unitInterval)
    (hst : (s : ℝ) < (t : ℝ))
    (ha : ((0 : unitInterval), s) ∈ squareGridCell N hN ⟨0,hN⟩ a)
    (hb : ((0 : unitInterval), t) ∈ squareGridCell N hN ⟨0,hN⟩ b)
    (u v : Nat) (huv : u ≠ v)
    (hs : (loop s).1 = triangulationTopologicalGeometricVertex u)
    (ht : (loop t).1 = triangulationTopologicalGeometricVertex v) :
    a < b := by
  have hab := g2_boundary_cell_index_mono N hN a b s t hst ha hb
  apply lt_of_le_of_ne hab
  intro heq
  subst b
  exact huv (carrier_grid_boundary_cell_breakpoints_same_vertex
    H N hN label hpositive ⟨0,hN⟩ a s t ha hb u v hs ht)

#print axioms g2_boundary_cell_index_mono
#print axioms g2_distinct_breakpoint_anchor_strict

end Poincare
