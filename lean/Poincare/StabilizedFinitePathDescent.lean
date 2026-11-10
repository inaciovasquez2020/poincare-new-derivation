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


/-- Exactly characterize the four certified labeled move constructors.
The inverse 1-to-4 case requires a legal 4-to-1 predecessor; this
does not establish representation of every abstract bistellar move. -/
theorem certifiedPachnerStep_iff_exactLabeledMove
    (K L : Triangulation) :
    CertifiedPachnerStep K L ↔
      (ClosedTriangulationCore K ∧
        ∃ s : Move23Site, s.LegalIn K ∧ L = s.replace K) ∨
      (ClosedTriangulationCore K ∧
        ∃ s : Move32Site, s.LegalIn K ∧ L = s.replace K) ∨
      (ClosedTriangulationCore K ∧
        ∃ s : Move41Site, s.LegalIn K ∧ L = s.replace K) ∨
      (∃ P : Triangulation, ClosedTriangulationCore P ∧
        ∃ s : Move41Site, s.LegalIn P ∧ K = s.replace P ∧ L = P) := by
  constructor
  · intro h
    cases h with
    | move23 hcore s hlegal =>
        exact Or.inl ⟨hcore, s, hlegal, rfl⟩
    | move32 hcore s hlegal =>
        exact Or.inr (Or.inl ⟨hcore, s, hlegal, rfl⟩)
    | move41 hcore s hlegal =>
        exact Or.inr (Or.inr (Or.inl ⟨hcore, s, hlegal, rfl⟩))
    | move14 hcore s hlegal =>
        exact Or.inr (Or.inr (Or.inr ⟨_, hcore, s, hlegal, rfl, rfl⟩))
  · intro h
    rcases h with h23 | h32 | h41 | h14
    · rcases h23 with ⟨hcore, s, hlegal, rfl⟩
      exact CertifiedPachnerStep.move23 hcore s hlegal
    · rcases h32 with ⟨hcore, s, hlegal, rfl⟩
      exact CertifiedPachnerStep.move32 hcore s hlegal
    · rcases h41 with ⟨hcore, s, hlegal, rfl⟩
      exact CertifiedPachnerStep.move41 hcore s hlegal
    · rcases h14 with ⟨P, hcore, s, hlegal, hK, hL⟩
      subst K
      subst L
      exact CertifiedPachnerStep.move14 hcore s hlegal


/-- An inverse of a legal 4→1 site is an exact certified 1→4 step.
The recovered center is fresh in the source triangulation.
This theorem does not construct such a site for every tetrahedron. -/
theorem CertifiedPachnerStep.move14_of_legal41_with_fresh_center
    {P : Triangulation}
    (s : Move41Site) (hlegal : s.LegalIn P) :
    CertifiedPachnerStep (s.replace P) P ∧
      ClosedTriangulationCore (s.replace P) ∧
      s.e ∉ vertexSupport (s.replace P) ∧
      (s.replace P).tets = s.targetTet :: s.unchangedTets P := by
  exact ⟨CertifiedPachnerStep.move14 hlegal.closedCore s hlegal,
    hlegal.closedCore.move41Site_replace_closedCore s hlegal,
    Move41Site.center_not_mem_vertexSupport_replace hlegal, rfl⟩

/-- Concatenate two independently certified finite Pachner histories.
Every move in the composite was already certified in one of the inputs;
no monotonicity or global descent hypothesis is required. -/
theorem CertifiedPachnerPath.trans
    {K L M : Triangulation}
    (hKL : CertifiedPachnerPath K L)
    (hLM : CertifiedPachnerPath L M) :
    CertifiedPachnerPath K M := by
  induction hLM with
  | refl => exact hKL
  | snoc hpath hstep ih =>
      exact CertifiedPachnerPath.snoc ih hstep


/-- Every certified elementary Pachner move has a closed-triangulation
target. The inverse 1→4 constructor uses its certified 4→1 predecessor. -/
theorem CertifiedPachnerStep.target_closedCore
    {K L : Triangulation} (h : CertifiedPachnerStep K L) :
    ClosedTriangulationCore L := by
  cases h with
  | move23 hcore s hlegal =>
      exact hcore.move23Site_replace_closedCore s hlegal
  | move32 hcore s hlegal =>
      exact hcore.move32Site_replace_closedCore s hlegal
  | move41 hcore s hlegal =>
      exact hcore.move41Site_replace_closedCore s hlegal
  | move14 hcore s hlegal =>
      exact hcore

/-- A certified finite path cannot leave the closed-core class when its
source is a closed core. This is an endpoint invariant, not descent. -/
theorem CertifiedPachnerPath.target_closedCore
    {K L : Triangulation} (h : CertifiedPachnerPath K L)
    (hcore : ClosedTriangulationCore K) :
    ClosedTriangulationCore L := by
  induction h with
  | refl => exact hcore
  | snoc hpath hstep ih =>
      exact hstep.target_closedCore



/-- Both endpoints of a non-reflexive certified step are closed cores.
For inverse 1→4, the source is the legal 4→1 target. -/
theorem CertifiedPachnerStep.source_closedCore
    {K L : Triangulation} (h : CertifiedPachnerStep K L) :
    ClosedTriangulationCore K := by
  cases h with
  | move23 hcore s hlegal => exact hcore
  | move32 hcore s hlegal => exact hcore
  | move41 hcore s hlegal => exact hcore
  | move14 hcore s hlegal =>
      exact hcore.move41Site_replace_closedCore s hlegal

/-- A certified path is either reflexive or both endpoints are closed cores.
No initial closed-core premise is required, and this asserts no descent. -/
theorem CertifiedPachnerPath.eq_or_closedCore_endpoints
    {K L : Triangulation} (h : CertifiedPachnerPath K L) :
    K = L ∨ (ClosedTriangulationCore K ∧ ClosedTriangulationCore L) := by
  induction h with
  | refl => exact Or.inl rfl
  | snoc hpath hstep ih =>
      right
      rcases ih with hEq | ⟨hcoreK, _⟩
      · subst K
        exact ⟨hstep.source_closedCore, hstep.target_closedCore⟩
      · exact ⟨hcoreK, hstep.target_closedCore⟩

end Poincare
