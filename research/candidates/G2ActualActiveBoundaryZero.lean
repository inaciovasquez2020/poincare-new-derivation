import Poincare.G2ActiveBoundaryZero
import Poincare.G2ActualThreeConstantSides

/-!
# Actual carrier-grid active-side cocycle vanishing

This connects the true null-homotopy's three constant sides directly to
the verified finite Stokes identity. There are no assumptions on the
labels of the three constant sides: those are derived from geometry.

The active label word has not yet been equated to a primal edge path.
-/

namespace Poincare

open CarrierLoopNullHomotopyData

theorem g2_actual_carrier_active_boundary_pairing_zero
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
      ∀ z ∈ squareGridCell N hN i j,
        0 < (H.homotopy z).1 (label i j))
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ u, w u u = 0)
    (hsym : ∀ u v, w u v = w v u)
    (htri : ∀ tau : Tet, ∀ a b c : Nat,
      a ∈ tau.verts → b ∈ tau.verts → c ∈ tau.verts →
      w a b + w b c + w c a = 0)
    (base : Nat)
    (hbase : x.1 = triangulationTopologicalGeometricVertex base) :
    let get : Nat → Fin N := fun k => ⟨k % N, Nat.mod_lt k hN⟩
    let f : Nat → Nat → Nat := fun i j => label (get i) (get j)
    (∑ j ∈ Finset.range (N - 1), w (f 0 j) (f 0 (j+1))) = 0 := by
  obtain ⟨hbottom, htop, hright⟩ :=
    g2_carrier_grid_three_constant_sides_labels
      H N hN label hpositive base hbase
  exact carrier_grid_active_side_pairing_zero
    H N hN label hpositive w hzero hsym htri
    base hbottom htop hright

#print axioms g2_actual_carrier_active_boundary_pairing_zero

end Poincare
