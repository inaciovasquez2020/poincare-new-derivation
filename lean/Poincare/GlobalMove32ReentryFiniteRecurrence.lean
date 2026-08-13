import Poincare.GlobalMove32SupportedEdgeState
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

namespace Poincare

/--
One incidence-three source-face reentry step.

The next Move32 site is realized on the same triangulation, has shared-edge
incidence exactly three, again carries a represented source-face obstruction,
and its unordered shared edge differs from that of the preceding site.

This definition records only the reentry alternative already produced by the
one-step source-face theorem.  It makes no termination or acyclicity claim.
-/
def Move32SourceFaceReentry
    (K : Triangulation)
    (s s' : Move32Site) : Prop :=
  s'.RealizedIn K ∧
    s'.SharedEdgeExactlyThree K ∧
      (∃ tau ∈ K.tets,
        s'.a ∈ tau.verts ∧
        s'.b ∈ tau.verts ∧
        s'.c ∈ tau.verts) ∧
        ¬ (
          (s'.d = s.d ∧
           s'.e = s.e) ∨
          (s'.d = s.e ∧
           s'.e = s.d)
        )

/--
Every source-face reentry step changes the canonical finite shared-edge
state.
-/
theorem
    ClosedTriangulationCore.sharedSupportedEdgeState_ne_of_sourceFaceReentry
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s s' : Move32Site)
    (hrealized : s.RealizedIn K)
    (hstep : Move32SourceFaceReentry K s s') :
    sharedSupportedEdgeState
        hcore s' hstep.1 ≠
      sharedSupportedEdgeState
        hcore s hrealized := by
  exact
    hcore.sharedSupportedEdgeState_ne_of_nonself
      s
      s'
      hrealized
      hstep.1
      hstep.2.2.2

/--
If a sequence of realized Move32 sites reenters forever and every step is a
genuine nonself source-face reentry, then the finite canonical shared-edge
state must recur.

More precisely, there are indices `i < j`, in fact `i + 1 < j`, among the
first `card + 1` sites such that the canonical shared-edge states at `i` and
`j` agree.  Every transition along that segment remains a source-face reentry
and every pair of consecutive canonical states remains distinct.

This is the exact finite-recurrence conclusion.  It does not assert that the
recurrent segment is impossible, nor that reentry terminates.
-/
theorem
    ClosedTriangulationCore.exists_repeated_sharedSupportedEdgeState_of_perpetual_sourceFaceReentry
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (sites : Nat → Move32Site)
    (hrealized :
      ∀ n,
        (sites n).RealizedIn K)
    (hreentry :
      ∀ n,
        Move32SourceFaceReentry
          K
          (sites n)
          (sites (n + 1))) :
    ∃ i j,
      i + 1 < j ∧
      j ≤ Fintype.card (SupportedEdgeState K) ∧
      sharedSupportedEdgeState
          hcore
          (sites i)
          (hrealized i) =
        sharedSupportedEdgeState
          hcore
          (sites j)
          (hrealized j) ∧
      (∀ n,
        i ≤ n →
        n < j →
        Move32SourceFaceReentry
          K
          (sites n)
          (sites (n + 1))) ∧
      ∀ n,
        i ≤ n →
        n < j →
        sharedSupportedEdgeState
            hcore
            (sites (n + 1))
            (hrealized (n + 1)) ≠
          sharedSupportedEdgeState
            hcore
            (sites n)
            (hrealized n) := by
  classical

  let N :
      Nat :=
    Fintype.card
      (SupportedEdgeState K)

  let f :
      Nat → SupportedEdgeState K :=
    fun n =>
      sharedSupportedEdgeState
        hcore
        (sites n)
        (hrealized n)

  let S :
      Finset Nat :=
    Finset.range (N + 1)

  let T :
      Finset (SupportedEdgeState K) :=
    Finset.univ

  have hcard :
      T.card < S.card := by
    simpa [T, S, N]

  have hmaps :
      Set.MapsTo
        f
        (↑S : Set Nat)
        (↑T : Set (SupportedEdgeState K)) := by
    intro n hn
    simp [T]

  obtain
      ⟨i, hiS,
        j, hjS,
        hij,
        hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := S)
      (t := T)
      hcard
      hmaps

  have hiBound :
      i ≤ N := by
    have hiLt :
        i < N + 1 := by
      simpa [S] using hiS
    omega

  have hjBound :
      j ≤ N := by
    have hjLt :
        j < N + 1 := by
      simpa [S] using hjS
    omega

  have hconsecutive :
      ∀ n,
        f (n + 1) ≠
          f n := by
    intro n

    have hnonself :
        ¬ (
          ((sites (n + 1)).d =
              (sites n).d ∧
            (sites (n + 1)).e =
              (sites n).e) ∨
          ((sites (n + 1)).d =
              (sites n).e ∧
            (sites (n + 1)).e =
              (sites n).d)
        ) :=
      (hreentry n).2.2.2

    have hne :=
      hcore.sharedSupportedEdgeState_ne_of_nonself
        (sites n)
        (sites (n + 1))
        (hrealized n)
        (hrealized (n + 1))
        hnonself

    simpa [f] using hne

  have horder :
      i < j ∨
      j < i :=
    Nat.lt_or_gt_of_ne hij

  rcases horder with
    hijlt | hjilt

  · have hgap :
        i + 1 < j := by
      by_contra hnot

      have hsucc :
          j = i + 1 := by
        omega

      subst j

      exact
        (hconsecutive i)
          hfij.symm

    refine
      ⟨i,
        j,
        hgap,
        ?_,
        ?_,
        ?_,
        ?_⟩

    · simpa [N] using hjBound

    · simpa [f] using hfij

    · intro n hin hnj
      exact hreentry n

    · intro n hin hnj
      simpa [f] using
        hconsecutive n

  · have hgap :
        j + 1 < i := by
      by_contra hnot

      have hsucc :
          i = j + 1 := by
        omega

      subst i

      exact
        (hconsecutive j)
          hfij

    refine
      ⟨j,
        i,
        hgap,
        ?_,
        ?_,
        ?_,
        ?_⟩

    · simpa [N] using hiBound

    · simpa [f] using hfij.symm

    · intro n hjn hni
      exact hreentry n

    · intro n hjn hni
      simpa [f] using
        hconsecutive n

end Poincare
