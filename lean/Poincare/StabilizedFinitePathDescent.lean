import Poincare.AscentBarrierInvariant

namespace Poincare

/-- The literal forward 1→4 replacement of any specified tetrahedron.
This is a combinatorial candidate, not a certified legal step: preservation
of the closed core and an inverse legal 4→1 certificate are still required. -/
def tetrahedronOneFourReplacement
    (K : Triangulation) (source : Tet) (e : Nat) : Triangulation :=
  { tets :=
      [⟨source.v0, source.v1, source.v2, e⟩,
       ⟨source.v0, source.v1, source.v3, e⟩,
       ⟨source.v0, source.v2, source.v3, e⟩,
       ⟨source.v1, source.v2, source.v3, e⟩] ++
      eraseFirstSameTet source K.tets }

/-- A fresh vertex inserted into a nondegenerate represented tetrahedron
produces only nondegenerate tetrahedra.  This is the first, not the complete,
closed-core preservation obligation. -/
theorem tetrahedronOneFourReplacement_nodup
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (source : Tet) (hsource : source ∈ K.tets)
    (e : Nat) (hfresh : e ∉ vertexSupport K) :
    ∀ τ ∈ (tetrahedronOneFourReplacement K source e).tets,
      τ.verts.Nodup := by
  have hs : source.verts.Nodup := hcore.1 source hsource
  have heSrc : e ∉ source.verts := by
    intro h
    apply hfresh
    apply (mem_vertexSupport_iff K e).2
    exact List.mem_flatMap.mpr ⟨source, hsource, h⟩
  intro τ hτ
  simp only [tetrahedronOneFourReplacement, List.mem_append] at hτ
  rcases hτ with hnew | hold
  · simp only [List.mem_cons, List.mem_singleton] at hnew
    rcases hnew with rfl | rfl | rfl | rfl <;>
      simp_all [Tet.verts, List.nodup_cons]
  · exact hcore.1 τ (mem_of_mem_eraseFirstSameTet hold)

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

/-- Concatenate two finite certified Pachner paths without changing their
endpoints or assuming monotonicity of the intermediate defect. -/
theorem CertifiedPachnerPath.trans
    {K L M : Triangulation}
    (hKL : CertifiedPachnerPath K L)
    (hLM : CertifiedPachnerPath L M) :
    CertifiedPachnerPath K M := by
  induction hLM with
  | refl => exact hKL
  | snoc _ hstep ih =>
      exact CertifiedPachnerPath.snoc ih hstep

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
