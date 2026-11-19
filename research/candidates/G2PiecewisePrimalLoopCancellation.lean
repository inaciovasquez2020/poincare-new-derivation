import Poincare.G2OrderedBoundaryWordParity
import Poincare.G2OrderedBreakpointAnchors
import Poincare.G2IntermediateBoundaryLabels
import Poincare.G2ActualActiveBoundaryZero

namespace Poincare
open CarrierLoopNullHomotopyData

/-- Piecewise primal-edge loops with an actual null-homotopy have zero
cocycle pairing. Grid labels, anchors, their order, and support are derived,
not assumed. The piecewise-edge representation is an explicit hypothesis. -/
theorem g2_piecewise_primal_loop_pairing_zero
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ u, w u u = 0)
    (hsym : ∀ u v, w u v = w v u)
    (htri : ∀ tau : Tet, ∀ a b c : Nat,
      a ∈ tau.verts → b ∈ tau.verts → c ∈ tau.verts →
      w a b + w b c + w c a = 0)
    (m : Nat) (hm : 0 < m)
    (vertex : Nat → Nat) (time : Nat → unitInterval)
    (hfirst : time 0 = 0) (hlast : time m = 1)
    (horder : ∀ k, k < m → (time k : ℝ) < (time (k+1) : ℝ))
    (hdistinct : ∀ k, k < m → vertex k ≠ vertex (k+1))
    (hvertex : ∀ k, k ≤ m →
      (loop (time k)).1 = triangulationTopologicalGeometricVertex (vertex k))
    (hsegment : ∀ k, k < m → ∀ q : unitInterval,
      (time k : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ (time (k+1) : ℝ) →
      ∃ r : ℝ, (loop q).1 = AffineMap.lineMap
        (triangulationTopologicalGeometricVertex (vertex k))
        (triangulationTopologicalGeometricVertex (vertex (k+1))) r) :
    (∑ k ∈ Finset.range m, w (vertex k) (vertex (k+1))) = 0 := by
  classical
  obtain ⟨N,hN,label,_,hpositive⟩ :=
    H.exists_finite_squareGrid_positiveCoordinate_labelling_probe
  have hex : ∀ k : Nat, ∃ j : Fin N,
      ((0 : unitInterval), time k) ∈ squareGridCell N hN ⟨0,hN⟩ j := by
    intro k
    exact exists_squareGrid_left_cell_probe N hN (time k)
  choose b hb using hex
  let a : Nat → Nat := fun k => (b k : Nat)
  let get : Nat → Fin N := fun j => ⟨j % N, Nat.mod_lt j hN⟩
  let L : Nat → Nat := fun j => label (get 0) (get j)
  have hg0 : get 0 = ⟨0,hN⟩ := by
    apply Fin.ext
    change 0 % N = 0
    exact Nat.zero_mod N
  have hg (j : Fin N) : get (j : Nat) = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.isLt
  have ha0 : a 0 = 0 := by
    have hh := (hb 0).2.2.1
    rw [hfirst] at hh
    change ((b 0 : Fin N) : ℝ) / (N : ℝ) ≤ 0 at hh
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hz : ((b 0 : Fin N) : ℝ) ≤ 0 := by
      have h := (div_le_iff₀ hNr).mp hh
      simpa using h
    have hn : (b 0 : Nat) ≤ 0 := by exact_mod_cast hz
    change (b 0 : Nat) = 0
    omega
  have ham : a m = N-1 := by
    have hh := (hb m).2.2.2
    rw [hlast] at hh
    change (1 : ℝ) ≤ (((b m).succ : Fin (N+1)) : ℝ) / (N : ℝ) at hh
    rw [show (((b m).succ : Fin (N+1)) : ℝ) =
      ((b m : Fin N) : ℝ)+1 by norm_num] at hh
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hz : (N : ℝ) ≤ ((b m : Fin N) : ℝ)+1 := by
      have h := (le_div_iff₀ hNr).mp hh
      simpa using h
    have hn : N ≤ (b m : Nat)+1 := by exact_mod_cast hz
    have hlt := (b m).isLt
    change (b m : Nat) = N-1
    omega
  have hmono : ∀ k, k < m → a k ≤ a (k+1) := by
    intro k hk
    exact g2_boundary_cell_index_mono N hN (b k) (b (k+1))
      (time k) (time (k+1)) (horder k hk) (hb k) (hb (k+1))
  have hanchor : ∀ k, k ≤ m → L (a k) = vertex k := by
    intro k hk
    change label (get 0) (get (b k : Nat)) = vertex k
    rw [hg0,hg]
    exact carrier_grid_loopBoundary_vertex_forces_label
      H N hN label hpositive ⟨0,hN⟩ (b k) (time k)
      (hb k) (vertex k) (hvertex k hk)
  have hsupp : ∀ k, k < m → ∀ j,
      a k ≤ j → j ≤ a (k+1) →
      L j = vertex k ∨ L j = vertex (k+1) := by
    intro k hk j hj1 hj2
    have hjN : j < N := by
      have hbN := (b (k+1)).isLt
      change j ≤ (b (k+1) : Nat) at hj2
      omega
    have hjget : (get j : Nat) = j := Nat.mod_eq_of_lt hjN
    have hleft : b k ≤ get j := by
      change (b k : Nat) ≤ (get j : Nat)
      rw [hjget]
      exact hj1
    have hright : get j ≤ b (k+1) := by
      change (get j : Nat) ≤ (b (k+1) : Nat)
      rw [hjget]
      exact hj2
    change label (get 0) (get j) = vertex k ∨
      label (get 0) (get j) = vertex (k+1)
    rw [hg0]
    exact g2_actual_intermediate_boundary_labels H N hN label hpositive
      (b k) (b (k+1)) (get j) (time k) (time (k+1))
      (le_of_lt (horder k hk)) (hb k) (hb (k+1))
      hleft hright (vertex k) (vertex (k+1)) (hsegment k hk)
  have hbase : x.1 = triangulationTopologicalGeometricVertex (vertex 0) := by
    have hh := hvertex 0 (Nat.zero_le m)
    rw [hfirst, loop.source] at hh
    exact hh
  have hz := g2_actual_carrier_active_boundary_pairing_zero
    H N hN label hpositive w hzero hsym htri (vertex 0) hbase
  change (∑ j ∈ Finset.range (N-1), w (L j) (L (j+1))) = 0 at hz
  have heq := G2Boundary.g2_ordered_boundary_word_parity
    w hzero hsym L vertex a m ha0 hmono hdistinct hanchor hsupp
  rw [ham,hz] at heq
  exact heq.symm

#print axioms g2_piecewise_primal_loop_pairing_zero

end Poincare
