import Poincare.GlobalFanChordTransitionNonself
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

namespace Poincare

/--
A perpetual chained sequence of fan-chord transitions on one fixed
triangulation must revisit a canonical supported-edge state.

Every consecutive state is nevertheless distinct, by
`FanChordTransition.edgeState_ne_parent`.  Thus any perpetual continuation
contains a nonconsecutive finite-state recurrence among the first
`card + 1` parent edges.

This is only a finite-recurrence theorem.  It does not assert that the
recurrent segment is impossible, nor that fan-chord continuation terminates.
-/
theorem
    exists_repeated_supportedEdgeState_of_perpetual_fanChordTransition
    {K : Triangulation}
    (v x : Nat → Nat)
    (hv : ∀ n, v n ∈ vertexSupport K)
    (hx : ∀ n, x n ∈ vertexSupport K)
    (hvx : ∀ n, v n ≠ x n)
    (T : ∀ n, FanChordTransition K (v n) (x n))
    (hchain :
      ∀ n,
        v (n + 1) = (T n).z0 ∧
        x (n + 1) = (T n).z1) :
    ∃ i j,
      i + 1 < j ∧
      j ≤ Fintype.card (SupportedEdgeState K) ∧
      supportedEdgeStateOfDistinct
          K (v i) (x i) (hv i) (hx i) (hvx i) =
        supportedEdgeStateOfDistinct
          K (v j) (x j) (hv j) (hx j) (hvx j) ∧
      ∀ n,
        i ≤ n →
        n < j →
        supportedEdgeStateOfDistinct
            K (v (n + 1)) (x (n + 1))
              (hv (n + 1)) (hx (n + 1)) (hvx (n + 1)) ≠
          supportedEdgeStateOfDistinct
            K (v n) (x n) (hv n) (hx n) (hvx n) := by
  classical

  let f : Nat → SupportedEdgeState K :=
    fun n =>
      supportedEdgeStateOfDistinct
        K (v n) (x n) (hv n) (hx n) (hvx n)

  have hnext :
      ∀ n,
        f (n + 1) = (T n).edgeState := by
    intro n
    obtain ⟨hvnext, hxnext⟩ := hchain n
    rw [show f (n + 1) =
        supportedEdgeStateOfDistinct
          K (v (n + 1)) (x (n + 1))
            (hv (n + 1)) (hx (n + 1)) (hvx (n + 1)) by rfl]
    rw [hvnext, hxnext]
    exact (T n).edgeState_eq.symm

  have hconsecutive :
      ∀ n,
        f (n + 1) ≠ f n := by
    intro n
    rw [hnext n]
    exact
      (T n).edgeState_ne_parent
        (hv n)
        (hx n)
        (hvx n)

  let N : Nat :=
    Fintype.card (SupportedEdgeState K)

  let S : Finset Nat :=
    Finset.range (N + 1)

  let U : Finset (SupportedEdgeState K) :=
    Finset.univ

  have hcard :
      U.card < S.card := by
    simpa [U, S, N]

  have hmaps :
      Set.MapsTo
        f
        (↑S : Set Nat)
        (↑U : Set (SupportedEdgeState K)) := by
    intro n hn
    simp [U]

  obtain
      ⟨i, hiS,
        j, hjS,
        hij,
        hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := S)
      (t := U)
      hcard
      hmaps

  have hiBound :
      i ≤ N := by
    have hiLt : i < N + 1 := by
      simpa [S] using hiS
    omega

  have hjBound :
      j ≤ N := by
    have hjLt : j < N + 1 := by
      simpa [S] using hjS
    omega

  have horder :
      i < j ∨ j < i :=
    Nat.lt_or_gt_of_ne hij

  rcases horder with hijlt | hjilt

  · have hgap : i + 1 < j := by
      by_contra hnot
      have hsucc : j = i + 1 := by
        omega
      subst j
      exact (hconsecutive i) hfij.symm

    refine ⟨i, j, hgap, ?_, ?_, ?_⟩

    · simpa [N] using hjBound

    · simpa [f] using hfij

    · intro n hin hnj
      simpa [f] using hconsecutive n

  · have hgap : j + 1 < i := by
      by_contra hnot
      have hsucc : i = j + 1 := by
        omega
      subst i
      exact (hconsecutive j) hfij

    refine ⟨j, i, hgap, ?_, ?_, ?_⟩

    · simpa [N] using hiBound

    · simpa [f] using hfij.symm

    · intro n hjn hni
      simpa [f] using hconsecutive n

end Poincare
