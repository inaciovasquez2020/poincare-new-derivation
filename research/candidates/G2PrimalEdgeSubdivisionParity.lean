import Mathlib

/-!
Exact mod-two boundary parity of a subdivided primal edge.

This is the finite endpoint-recovery identity needed after a geometric
positive-coordinate labeling has been constructed. It does not assume that
the geometric labels have already been aligned with primal-edge breakpoints.
-/

namespace Poincare.G2Boundary

private theorem twice_zero (a : ZMod 2) : a + a = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  calc
    a + a = (2 : ZMod 2) * a := by ring
    _ = 0 := by rw [htwo]; ring

private theorem telescoping (f : Nat → ZMod 2) (n : Nat) :
    (∑ i ∈ Finset.range n, (f i + f (i + 1))) = f 0 + f n := by
  induction n with
  | zero => simp [twice_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      calc
        f 0 + f n + (f n + f (n + 1)) =
            (f 0 + f (n + 1)) + (f n + f n) := by abel
        _ = f 0 + f (n + 1) := by rw [twice_zero]; simp

/-- Any edge weights on a two-vertex support are a coboundary. -/
theorem two_label_edge_weight_eq_coboundary
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ x, w x x = 0)
    (hsym : ∀ a b, w a b = w b a)
    (u v a b : Nat) (huv : u ≠ v)
    (ha : a = u ∨ a = v)
    (hb : b = u ∨ b = v) :
    w a b = (if a = u then 0 else w u v) +
      (if b = u then 0 else w u v) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb]
    simp [hzero]
  · rw [ha, hb]
    simp [huv.symm]
  · rw [ha, hb]
    simpa [huv, huv.symm] using (hsym v u)
  · rw [ha, hb]
    simp [huv.symm, hzero, twice_zero]

/-- A finite walk from u to v whose labels all lie in {u,v} has exactly
the parity of the original edge uv, even with repeated labels/backtracks. -/
theorem primal_edge_subdivision_parity
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ x, w x x = 0)
    (hsym : ∀ a b, w a b = w b a)
    (u v : Nat) (huv : u ≠ v)
    (n : Nat) (p : Nat → Nat)
    (hp : ∀ i, i ≤ n → p i = u ∨ p i = v)
    (hstart : p 0 = u) (hend : p n = v) :
    (∑ i ∈ Finset.range n, w (p i) (p (i + 1))) = w u v := by
  let g : Nat → ZMod 2 := fun i =>
    if p i = u then 0 else w u v
  have hpair (i : Nat) (hi : i ∈ Finset.range n) :
      w (p i) (p (i + 1)) = g i + g (i + 1) := by
    have hin : i < n := Finset.mem_range.mp hi
    have hi1 : i + 1 ≤ n := by omega
    simpa only [g] using
      two_label_edge_weight_eq_coboundary w hzero hsym
        u v (p i) (p (i + 1)) huv
        (hp i (by omega)) (hp (i + 1) hi1)
  calc
    (∑ i ∈ Finset.range n, w (p i) (p (i + 1))) =
        ∑ i ∈ Finset.range n, (g i + g (i + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpair i hi
    _ = g 0 + g n := telescoping g n
    _ = w u v := by simp [g, hstart, hend, huv.symm]


/-- Finite boundary-word assembly over *arbitrarily many* successive
primal edges, allowing a different positive number of subedges in
each block. Consecutive blocks share the prescribed primal vertex
because their endpoint equations use the same vertex function.

The geometric task left open is to obtain these block data from the
actual labeled null-homotopy boundary; no such assumption is hidden
inside this theorem. -/
theorem assembled_primal_edge_loop_subdivision_parity
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ x, w x x = 0)
    (hsym : ∀ a b, w a b = w b a)
    (m : Nat)
    (vertex length : Nat → Nat)
    (label : Nat → Nat → Nat)
    (hdistinct : ∀ k, k < m → vertex k ≠ vertex (k + 1))
    (hsupport : ∀ k, k < m → ∀ i,
      i ≤ length k →
        label k i = vertex k ∨ label k i = vertex (k + 1))
    (hstart : ∀ k, k < m → label k 0 = vertex k)
    (hend : ∀ k, k < m → label k (length k) = vertex (k + 1)) :
    (∑ k ∈ Finset.range m,
      ∑ i ∈ Finset.range (length k),
        w (label k i) (label k (i + 1))) =
    ∑ k ∈ Finset.range m, w (vertex k) (vertex (k + 1)) := by
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k < m := Finset.mem_range.mp hk
  exact primal_edge_subdivision_parity
    w hzero hsym (vertex k) (vertex (k + 1))
    (hdistinct k hkm) (length k) (label k)
    (hsupport k hkm) (hstart k hkm) (hend k hkm)


#print axioms two_label_edge_weight_eq_coboundary
#print axioms primal_edge_subdivision_parity
#print axioms assembled_primal_edge_loop_subdivision_parity

end Poincare.G2Boundary
