import Poincare.G2ActualCarrierPerimeter

/-!
# Active side of the actual carrier grid

The finite Stokes theorem uses cell labels indexed 0,...,N-1, not the N+1
parameter-grid vertices. If the three constant boundary sides are labelled
by the base vertex, the entire cocycle pairing reduces to the active side.
The hypotheses on the three sides are explicit and will be discharged by
the already verified constant-boundary coordinate lemma.
-/

namespace Poincare

theorem carrier_grid_active_side_pairing_zero
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
      ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell N hN i j,
        0 < (H.homotopy z).1 (label i j))
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ u, w u u = 0)
    (hsym : ∀ u v, w u v = w v u)
    (htri : ∀ tau : Tet, tau ∈ K.tets → ∀ a b c : Nat,
      a ∈ tau.verts → b ∈ tau.verts → c ∈ tau.verts →
      w a b + w b c + w c a = 0)
    (base : Nat)
    (hbottom : ∀ i : Fin N, label i ⟨0, hN⟩ = base)
    (htop : ∀ i : Fin N, label i ⟨N-1, by omega⟩ = base)
    (hright : ∀ j : Fin N, label ⟨N-1, by omega⟩ j = base) :
    let get : Nat → Fin N := fun k => ⟨k % N, Nat.mod_lt k hN⟩
    let f : Nat → Nat → Nat := fun i j => label (get i) (get j)
    (∑ j ∈ Finset.range (N - 1), w (f 0 j) (f 0 (j+1))) = 0 := by
  let get : Nat → Fin N := fun k => ⟨k % N, Nat.mod_lt k hN⟩
  let f : Nat → Nat → Nat := fun i j => label (get i) (get j)
  have hlast : (get (N-1) : Nat) = N-1 := by
    change (N-1) % N = N-1
    exact Nat.mod_eq_of_lt (by omega)
  have hgetzero : get 0 = ⟨0, hN⟩ := by
    apply Fin.ext
    change 0 % N = 0
    exact Nat.zero_mod N
  have hgetlast : get (N-1) = ⟨N-1, by omega⟩ := by
    apply Fin.ext
    exact hlast
  have hbot : ∀ i, f i 0 = base := by
    intro i
    simp only [f, hgetzero]
    exact hbottom (get i)
  have htop' : ∀ i, f i (N-1) = base := by
    intro i
    simp only [f, hgetlast]
    exact htop (get i)
  have hright' : ∀ j, f (N-1) j = base := by
    intro j
    simp only [f, hgetlast]
    exact hright (get j)
  have ha : (∑ i ∈ Finset.range (N-1),
    w (f i 0) (f (i+1) 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hbot i, hbot (i+1), hzero]
  have hb : (∑ i ∈ Finset.range (N-1),
    w (f i (N-1)) (f (i+1) (N-1))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [htop' i, htop' (i+1), hzero]
  have hc : (∑ j ∈ Finset.range (N-1),
    w (f (N-1) j) (f (N-1) (j+1))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hright' j, hright' (j+1), hzero]
  have hperimeter :=
    carrier_grid_positive_labels_cocycle_perimeter_zero
      H N hN label hpositive w hsym htri
  change
    (∑ i ∈ Finset.range (N-1), w (f i 0) (f (i+1) 0)) +
    (∑ i ∈ Finset.range (N-1), w (f i (N-1)) (f (i+1) (N-1))) +
    (∑ j ∈ Finset.range (N-1), w (f 0 j) (f 0 (j+1))) +
    (∑ j ∈ Finset.range (N-1), w (f (N-1) j) (f (N-1) (j+1))) = 0
    at hperimeter
  rw [ha, hb, hc] at hperimeter
  simpa using hperimeter

#print axioms carrier_grid_active_side_pairing_zero

end Poincare
