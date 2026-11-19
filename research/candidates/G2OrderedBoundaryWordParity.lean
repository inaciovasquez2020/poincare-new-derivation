import Poincare.G2PrimalEdgeSubdivisionParity

namespace Poincare.G2Boundary

/-- Prefix differences recover a contiguous block, including empty blocks. -/
theorem g2_prefix_block_sum (f : Nat → ZMod 2) (a n : Nat) :
    (∑ j ∈ Finset.range (a+n), f j) =
      (∑ j ∈ Finset.range a, f j) +
      (∑ j ∈ Finset.range n, f (a+j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + (n+1) = (a+n)+1 by omega,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    abel

/-- Merge adjacent variable-length blocks into the original grid word.
Every transition is counted once; only block endpoints are shared. -/
theorem g2_ordered_boundary_word_parity
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ x, w x x = 0)
    (hsym : ∀ a b, w a b = w b a)
    (L vertex anchor : Nat → Nat) (m : Nat)
    (hfirst : anchor 0 = 0)
    (hmono : ∀ k, k < m → anchor k ≤ anchor (k+1))
    (hdistinct : ∀ k, k < m → vertex k ≠ vertex (k+1))
    (hanchor : ∀ k, k ≤ m → L (anchor k) = vertex k)
    (hsupport : ∀ k, k < m → ∀ j,
      anchor k ≤ j → j ≤ anchor (k+1) →
      L j = vertex k ∨ L j = vertex (k+1)) :
    (∑ j ∈ Finset.range (anchor m), w (L j) (L (j+1))) =
      ∑ k ∈ Finset.range m, w (vertex k) (vertex (k+1)) := by
  let f : Nat → ZMod 2 := fun j => w (L j) (L (j+1))
  have hstep : ∀ k, k < m →
      (∑ j ∈ Finset.range (anchor (k+1)), f j) =
        (∑ j ∈ Finset.range (anchor k), f j) +
        w (vertex k) (vertex (k+1)) := by
    intro k hk
    let n := anchor (k+1) - anchor k
    have hn : anchor k + n = anchor (k+1) := by
      dsimp [n]
      have hh := hmono k hk
      omega
    have hblock := primal_edge_subdivision_parity w hzero hsym
      (vertex k) (vertex (k+1)) (hdistinct k hk) n
      (fun j => L (anchor k + j))
      (by
        intro j hj
        apply hsupport k hk
        · omega
        · omega)
      (by simpa using hanchor k (by omega))
      (by rw [hn]; exact hanchor (k+1) (by omega))
    have hb : (∑ j ∈ Finset.range n, f (anchor k+j)) =
        w (vertex k) (vertex (k+1)) := by
      simpa only [f, Nat.add_assoc] using hblock
    have hp := g2_prefix_block_sum f (anchor k) n
    rw [hn, hb] at hp
    exact hp
  have hall : ∀ r, r ≤ m →
      (∑ j ∈ Finset.range (anchor r), f j) =
        ∑ k ∈ Finset.range r, w (vertex k) (vertex (k+1)) := by
    intro r
    induction r with
    | zero => intro _; simp [hfirst]
    | succ r ih =>
      intro hr
      rw [hstep r (by omega), ih (by omega), Finset.sum_range_succ]
  exact hall m le_rfl

#print axioms g2_prefix_block_sum
#print axioms g2_ordered_boundary_word_parity

end Poincare.G2Boundary
