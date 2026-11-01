import Poincare.GlobalFanReentryModeLinkedStep
import Poincare.GlobalFanChordWitnessAnchoredContinuation

namespace Poincare

/-- The classifier branch of a witness-anchored high-fan continuation
produces a genuine linked fan successor while retaining the exact adjacent
link triangles and the transverse shared-face vertex.  No claim about
return-cycle exclusion is made. -/
theorem ClosedTriangulationCore.exists_witnessAnchored_linked_fan_successor
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (old : HighFanState K)
    (S : WitnessAnchoredFanStep K old.v old.x old.transition)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hhigh :
      4 ≤ (K.tets.filter
        (fun tau =>
          old.transition.z0 ∈ tau.verts ∧
          old.transition.z1 ∈ tau.verts)).length) :
    ∃ next : HighFanState K,
      FanReentryModeStep K (.fan old) (.fan next) ∧
      next.transition.sigma.1 = S.witnessPos.1 ∧
      next.transition.rho.1 = S.neighbor.1 ∧
      next.transition.transverse = S.sharedThird := by
  rcases S.outcome with hmove23 | hthree | hclassifier
  · exact (hNoMove23 hmove23).elim
  · omega
  · obtain ⟨y, U, hσ, hρ, hy, hyw, hyn⟩ := hclassifier
    have hlineage :=
      S.classifier_branch_successor_lineage
        hcore hσ hρ hy hyw hyn
    let next : HighFanState K :=
      { v := old.transition.z0
        x := old.transition.z1
        v_supported := old.transition.z0_supported
        x_supported := old.transition.z1_supported
        endpoints_ne := old.transition.endpoints_ne
        transition := U }
    exact ⟨next, FanReentryModeStep.fan_next old next rfl rfl,
      congrArg Subtype.val hlineage.1,
      congrArg Subtype.val hlineage.2.1, hlineage.2.2⟩

end Poincare
