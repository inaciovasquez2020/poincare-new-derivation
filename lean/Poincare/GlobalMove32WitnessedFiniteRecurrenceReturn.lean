import Poincare.GlobalMove32ReentryFiniteRecurrence
import Poincare.GlobalMove32ReentryReturnTargetCompatibility
import Mathlib.Tactic

namespace Poincare

/--
A perpetual sequence of witnessed incidence-three Move32 source-face reentries
contains a nonconsecutive recurrent canonical shared-edge state whose actual
return step retains a represented tetrahedron lying in one of the anchor
Move32 target tetrahedra.

This is a finite recurrent-configuration theorem only.  It makes no
contradiction, acyclicity, termination, or high-incidence closure claim.
-/
theorem
    ClosedTriangulationCore.exists_recurrent_returnSigma_target_of_perpetual_witnessedReentry
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (sites : Nat → Move32Site)
    (hrealized :
      ∀ n,
        (sites n).RealizedIn K)
    (hthree :
      ∀ n,
        (sites n).SharedEdgeExactlyThree K)
    (hwitnessed :
      ∀ n,
        Move32SourceFaceWitnessedReentry
          K
          (sites n)
          (sites (n + 1))) :
    ∃ i k,
      i + 1 < k + 1 ∧
      k + 1 ≤ Fintype.card (SupportedEdgeState K) ∧
      sharedSupportedEdgeState
          hcore
          (sites i)
          (hrealized i) =
        sharedSupportedEdgeState
          hcore
          (sites (k + 1))
          (hrealized (k + 1)) ∧
      Move32SourceFaceWitnessedReentry
        K
        (sites k)
        (sites (k + 1)) ∧
      ∃ sigma,
        sigma ∈ K.tets ∧
        (sites i).d ∈ sigma.verts ∧
        (sites i).e ∈ sigma.verts ∧
        (SameTetVertices
            sigma
            (sites i).targetTet₀ ∨
          SameTetVertices
            sigma
            (sites i).targetTet₁ ∨
          SameTetVertices
            sigma
            (sites i).targetTet₂) := by
  classical

  have hreentry :
      ∀ n,
        Move32SourceFaceReentry
          K
          (sites n)
          (sites (n + 1)) := by
    intro n
    exact
      (hwitnessed n).toSourceFaceReentry

  obtain
      ⟨i,
        j,
        hgap,
        hjBound,
        hstate,
        _hsegment,
        _hconsecutive⟩ :=
    hcore.exists_repeated_sharedSupportedEdgeState_of_perpetual_sourceFaceReentry
      sites
      hrealized
      hreentry

  have hj0 :
      j ≠ 0 := by
    omega

  obtain
      ⟨k, hk⟩ :=
    Nat.exists_eq_succ_of_ne_zero hj0

  subst j

  have hgap' :
      i + 1 < k + 1 := by
    simpa [Nat.succ_eq_add_one] using hgap

  have hkBound :
      k + 1 ≤
        Fintype.card (SupportedEdgeState K) := by
    simpa [Nat.succ_eq_add_one] using hjBound

  have hstate' :
      sharedSupportedEdgeState
          hcore
          (sites i)
          (hrealized i) =
        sharedSupportedEdgeState
          hcore
          (sites (k + 1))
          (hrealized (k + 1)) := by
    simpa [Nat.succ_eq_add_one] using hstate

  have hstep :
      Move32SourceFaceWitnessedReentry
        K
        (sites k)
        (sites (k + 1)) :=
    hwitnessed k

  have hreturn :=
    hcore.exists_returnSigma_same_anchor_target_of_witnessedReentry_of_sharedSupportedEdgeState_eq
      (sites i)
      (sites k)
      (sites (k + 1))
      (hrealized i)
      (hthree i)
      (hrealized (k + 1))
      hstep
      hstate'.symm

  exact
    ⟨i,
      k,
      hgap',
      hkBound,
      hstate',
      hstep,
      hreturn⟩

end Poincare
