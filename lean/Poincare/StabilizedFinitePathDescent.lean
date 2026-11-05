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


/-- Renaming every tetrahedral vertex by a bijection preserves and reflects
the exact unordered vertex-set equivalence used in certified move sites.
This does not yet transport the legality or replacement of a Pachner site. -/
theorem sameTetVertices_relabel_iff
    (f : Nat ≃ Nat) (τ σ : Tet) :
    SameTetVertices
      ⟨f τ.v0, f τ.v1, f τ.v2, f τ.v3⟩
      ⟨f σ.v0, f σ.v1, f σ.v2, f σ.v3⟩
      ↔ SameTetVertices τ σ := by
  let r : Tet → Tet := fun t =>
    ⟨f t.v0, f t.v1, f t.v2, f t.v3⟩
  have verts_relabel (t : Tet) :
      (r t).verts = t.verts.map f := by
    rfl
  have mem_relabel (t : Tet) (v : Nat) :
      v ∈ (r t).verts ↔ f.symm v ∈ t.verts := by
    rw [verts_relabel t, List.mem_map]
    constructor
    · rintro ⟨u, hu, huv⟩
      have h : u = f.symm v := by
        apply f.injective
        simpa using huv
      exact h ▸ hu
    · intro hv
      exact ⟨f.symm v, hv, f.apply_symm_apply v⟩
  change SameTetVertices (r τ) (r σ) ↔ SameTetVertices τ σ
  constructor
  · intro h v
    have hv := h (f v)
    simpa only [mem_relabel, f.symm_apply_apply] using hv
  · intro h v
    have hv := h (f.symm v)
    simpa only [mem_relabel] using hv

end Poincare
