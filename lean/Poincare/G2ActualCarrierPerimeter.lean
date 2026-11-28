import Poincare.G2GridFourCellCorner
import Poincare.G2CarrierGridCocyclePerimeter

/-!
# Actual carrier-grid cocycle perimeter

This connects the existing finite positive-coordinate labeling to the
four-cell common-tetrahedron lemma and the finite rectangular Stokes
identity. The perimeter is the boundary of the *cell-label grid*
of size N-1, not the parameter-square grid of size N.

No geometric boundary-word identification is assumed or claimed.
-/

namespace Poincare

open CarrierLoopNullHomotopyData

/-- For every positively labelled finite square grid on an actual
carrier null-homotopy, the cocycle pairing with the perimeter of
the cell-label grid vanishes. -/
theorem carrier_grid_positive_labels_cocycle_perimeter_zero
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
    (hsym : ∀ u v, w u v = w v u)
    (htri : ∀ tau : Tet, tau ∈ K.tets → ∀ a b c : Nat,
      a ∈ tau.verts → b ∈ tau.verts → c ∈ tau.verts →
      w a b + w b c + w c a = 0) :
    let get : Nat → Fin N := fun k =>
      ⟨k % N, Nat.mod_lt k hN⟩
    let f : Nat → Nat → Nat := fun i j => label (get i) (get j)
    (∑ i ∈ Finset.range (N - 1), w (f i 0) (f (i+1) 0)) +
    (∑ i ∈ Finset.range (N - 1), w (f i (N-1)) (f (i+1) (N-1))) +
    (∑ j ∈ Finset.range (N - 1), w (f 0 j) (f 0 (j+1))) +
    (∑ j ∈ Finset.range (N - 1), w (f (N-1) j) (f (N-1) (j+1))) = 0 := by
  let get : Nat → Fin N := fun k =>
    ⟨k % N, Nat.mod_lt k hN⟩
  let f : Nat → Nat → Nat := fun i j => label (get i) (get j)
  have hcommon :
      ∀ i ∈ Finset.range (N-1), ∀ j ∈ Finset.range (N-1),
        ∃ tau : Tet, tau ∈ K.tets ∧
          f i j ∈ tau.verts ∧
          f (i+1) j ∈ tau.verts ∧
          f (i+1) (j+1) ∈ tau.verts ∧
          f i (j+1) ∈ tau.verts := by
    intro i hi j hj
    have hi0 : i < N := by
      have hi' := Finset.mem_range.mp hi
      omega
    have hi1 : i+1 < N := by
      have hi' := Finset.mem_range.mp hi
      omega
    have hj0 : j < N := by
      have hj' := Finset.mem_range.mp hj
      omega
    have hj1 : j+1 < N := by
      have hj' := Finset.mem_range.mp hj
      omega
    have hnexti : ((get i : Fin N) : Nat) + 1 =
        ((get (i+1) : Fin N) : Nat) := by
      change i % N + 1 = (i + 1) % N
      rw [Nat.mod_eq_of_lt hi0, Nat.mod_eq_of_lt hi1]
    have hnextj : ((get j : Fin N) : Nat) + 1 =
        ((get (j+1) : Fin N) : Nat) := by
      change j % N + 1 = (j + 1) % N
      rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    obtain ⟨tau, htau, ha, hb, hc, hd⟩ :=
      squareGrid_four_neighbor_labels_common_tet_probe
        H N hN label hpositive
        (get i) (get (i+1)) (get j) (get (j+1))
        hnexti hnextj
    exact ⟨tau, htau, ha, hb, hc, hd⟩
  exact carrier_grid_cocycle_perimeter_zero_of_common_tet
    (K:=K) w hsym htri (N-1) f hcommon

#print axioms carrier_grid_positive_labels_cocycle_perimeter_zero

end Poincare
