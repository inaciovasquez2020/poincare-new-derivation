import Poincare.AscentBarrierInvariant

namespace Poincare

/-- An actual legal bistellar step between closed triangulation cores.
The 1→4 case is the inverse of a certified legal 4→1 replacement,
not the placeholder global `applyMoveImpl`. -/
inductive CertifiedPachnerStep : Triangulation → Triangulation → Prop where
  | move23 {K : Triangulation}
      (hcore : ClosedTriangulationCore K)
      (s : Move23Site) (hlegal : s.LegalIn K) :
      CertifiedPachnerStep K (s.replace K)
  | move32 {K : Triangulation}
      (hcore : ClosedTriangulationCore K)
      (s : Move32Site) (hlegal : s.LegalIn K) :
      CertifiedPachnerStep K (s.replace K)
  | move41 {K : Triangulation}
      (hcore : ClosedTriangulationCore K)
      (s : Move41Site) (hlegal : s.LegalIn K) :
      CertifiedPachnerStep K (s.replace K)
  | move14 {K : Triangulation}
      (hcore : ClosedTriangulationCore K)
      (s : Move41Site) (hlegal : s.LegalIn K) :
      CertifiedPachnerStep (s.replace K) K

theorem CertifiedPachnerStep.homeomorphic
    {K L : Triangulation} (h : CertifiedPachnerStep K L) :
    Nonempty
      (triangulationTopologicalGeometricCarrier K ≃ₜ
        triangulationTopologicalGeometricCarrier L) := by
  cases h with
  | move23 hcore s hlegal =>
      exact ⟨hcore.move23GeometricCarrierHomeomorph s hlegal⟩
  | move32 hcore s hlegal =>
      exact ⟨hcore.move32GeometricCarrierHomeomorph s hlegal⟩
  | move41 hcore s hlegal =>
      exact ⟨hcore.move41GeometricCarrierHomeomorph s hlegal⟩
  | move14 hcore s hlegal =>
      exact ⟨(hcore.move41GeometricCarrierHomeomorph s hlegal).symm⟩

/-- Arbitrary finite legal Pachner histories, including vertex insertion
and any temporary increase in the nonnegative supported defect. -/
inductive CertifiedPachnerPath : Triangulation → Triangulation → Prop where
  | refl (K : Triangulation) : CertifiedPachnerPath K K
  | snoc {K L M : Triangulation}
      (hpath : CertifiedPachnerPath K L)
      (hstep : CertifiedPachnerStep L M) :
      CertifiedPachnerPath K M

theorem CertifiedPachnerPath.homeomorphic
    {K L : Triangulation} (h : CertifiedPachnerPath K L) :
    Nonempty
      (triangulationTopologicalGeometricCarrier K ≃ₜ
        triangulationTopologicalGeometricCarrier L) := by
  induction h with
  | refl =>
      exact ⟨Homeomorph.refl _⟩
  | snoc hpath hstep ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨f⟩ := hstep.homeomorphic
      exact ⟨e.trans f⟩

/-- Proposed universal endpoint descent, allowing arbitrary finite
nonmonotone sequences and certified inverse-4→1 (1→4) stabilizations.
This is an open proposition, NOT an established theorem or axiom. -/
def SimplyConnectedStabilizedPathDescent : Prop :=
  ∀ K : Triangulation,
    ClosedTriangulationCore K →
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K →
    TriangulationRealizationSimplyConnected K →
    0 < PhiSupport K →
    ∃ L : Triangulation,
      ClosedTriangulationCore L ∧
      CertifiedPachnerPath K L ∧
      PhiSupport L < PhiSupport K

/-- A finite certified path with smaller endpoint has the already required
topology-preserving descent property; no unproved global hypothesis is
introduced in this theorem. -/
theorem stabilizedPathDescent_implies_globalDescent
    (hcoverage : SimplyConnectedStabilizedPathDescent) :
    SimplyConnectedGlobalPhiSupportDescent := by
  intro K hcore hM hSC hpos
  obtain ⟨L, hcoreL, hpath, hlt⟩ :=
    hcoverage K hcore hM hSC hpos
  exact ⟨L, hcoreL, hlt, hpath.homeomorphic⟩

/-- Already certified three-move escape instantiates the longer-path
relation, demonstrating that endpoint descent need not be one-step descent. -/
theorem crossPolytopeBoundary4_stabilized_path_escape :
    CertifiedPachnerPath crossPolytopeBoundary4 crossPolytopeEscapeFinal := by
  apply CertifiedPachnerPath.snoc
  · apply CertifiedPachnerPath.snoc
    · apply CertifiedPachnerPath.snoc
      · exact CertifiedPachnerPath.refl crossPolytopeBoundary4
      · exact CertifiedPachnerStep.move23
          crossPolytopeBoundary4_closedCore
          crossPolytopeEscapeMove23 crossPolytopeEscapeMove23_legal
    · exact CertifiedPachnerStep.move32
        crossPolytopeEscapeAfter23_closedCore
        crossPolytopeEscapeMove32₁ crossPolytopeEscapeMove32₁_legal
  · exact CertifiedPachnerStep.move32
      crossPolytopeEscapeAfter32One_closedCore
      crossPolytopeEscapeMove32₂ crossPolytopeEscapeMove32₂_legal

theorem crossPolytopeBoundary4_stabilized_path_strict_descent :
    ∃ L : Triangulation,
      CertifiedPachnerPath crossPolytopeBoundary4 L ∧
      PhiSupport L < PhiSupport crossPolytopeBoundary4 := by
  exact ⟨crossPolytopeEscapeFinal,
    crossPolytopeBoundary4_stabilized_path_escape,
    by rw [crossPolytopeEscapeFinal_PhiSupport,
      crossPolytopeEscapeInitial_PhiSupport]; omega⟩

end Poincare
