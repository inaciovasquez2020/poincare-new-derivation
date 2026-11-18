import Poincare.G2PrimalEdgeCoordinateSupport

namespace Poincare

open CarrierLoopNullHomotopyData

/-- A cell between two ordered breakpoint cells intersects the parameter
interval between their breakpoints. No grid alignment is required. -/
theorem g2_intermediate_left_cell_meets_interval
    (N : Nat) (hN : 0 < N)
    (a b j : Fin N) (s t : unitInterval)
    (hst : (s : ℝ) ≤ (t : ℝ))
    (ha : ((0 : unitInterval), s) ∈ squareGridCell N hN ⟨0,hN⟩ a)
    (hb : ((0 : unitInterval), t) ∈ squareGridCell N hN ⟨0,hN⟩ b)
    (haj : a ≤ j) (hjb : j ≤ b) :
    ∃ q : unitInterval,
      (s : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (t : ℝ) ∧
      ((0 : unitInterval), q) ∈ squareGridCell N hN ⟨0,hN⟩ j := by
  rcases ha with ⟨hx0,hx1,has,has'⟩
  rcases hb with ⟨_,_,hbt,hbt'⟩
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have haj' : (a : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast (show (a : Nat) ≤ (j : Nat) from haj)
  have hjb' : (j : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast (show (j : Nat) ≤ (b : Nat) from hjb)
  have hl : (squareGridParameter N hN j.castSucc : ℝ) ≤
      (squareGridParameter N hN b.castSucc : ℝ) := by
    change (j : ℝ) / N ≤ (b : ℝ) / N
    exact div_le_div_of_nonneg_right hjb' hNr.le
  have hu : (squareGridParameter N hN a.succ : ℝ) ≤
      (squareGridParameter N hN j.succ : ℝ) := by
    change ((a.succ : Fin (N+1)) : ℝ) / N ≤
      ((j.succ : Fin (N+1)) : ℝ) / N
    rw [show ((a.succ : Fin (N+1)) : ℝ) = (a : ℝ)+1 by norm_num,
        show ((j.succ : Fin (N+1)) : ℝ) = (j : ℝ)+1 by norm_num]
    exact div_le_div_of_nonneg_right (by linarith) hNr.le
  let l := squareGridParameter N hN j.castSucc
  let r := squareGridParameter N hN j.succ
  have hsrc := squareGridCellSource_mem_probe N hN ⟨0,hN⟩ j
  have hlr : (l : ℝ) ≤ (r : ℝ) := hsrc.2.2.2
  let q : unitInterval := ⟨max (s : ℝ) (l : ℝ),
    le_trans s.property.1 (le_max_left _ _),
    max_le s.property.2 l.property.2⟩
  refine ⟨q, le_max_left _ _, max_le hst (hl.trans hbt), ?_⟩
  exact ⟨hx0,hx1,le_max_right _ _,max_le (has'.trans hu) hlr⟩

/-- Every cell between breakpoint anchors has one of the two primal
edge endpoint labels, whenever the actual loop segment lies on that edge. -/
theorem g2_actual_intermediate_boundary_labels
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
      ∀ z ∈ squareGridCell N hN i j,
        0 < (H.homotopy z).1 (label i j))
    (a b j : Fin N) (s t : unitInterval)
    (hst : (s : ℝ) ≤ (t : ℝ))
    (ha : ((0 : unitInterval), s) ∈ squareGridCell N hN ⟨0,hN⟩ a)
    (hb : ((0 : unitInterval), t) ∈ squareGridCell N hN ⟨0,hN⟩ b)
    (haj : a ≤ j) (hjb : j ≤ b)
    (u v : Nat)
    (hsegment : ∀ q : unitInterval, (s : ℝ) ≤ (q : ℝ) →
      (q : ℝ) ≤ (t : ℝ) → ∃ r : ℝ,
      (loop q).1 = AffineMap.lineMap
        (triangulationTopologicalGeometricVertex u)
        (triangulationTopologicalGeometricVertex v) r) :
    label ⟨0,hN⟩ j = u ∨ label ⟨0,hN⟩ j = v := by
  obtain ⟨q,hq1,hq2,hcell⟩ :=
    g2_intermediate_left_cell_meets_interval N hN a b j s t hst ha hb haj hjb
  obtain ⟨r,hr⟩ := hsegment q hq1 hq2
  exact carrier_grid_loopBoundary_label_is_edge_endpoint
    H N hN label hpositive ⟨0,hN⟩ j q hcell u v r hr

#print axioms g2_intermediate_left_cell_meets_interval
#print axioms g2_actual_intermediate_boundary_labels

end Poincare
