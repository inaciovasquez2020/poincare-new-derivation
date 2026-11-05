import Poincare.GlobalFanReentryModeFiniteRecurrence

namespace Poincare

/-- Under the fail-closed no-move/no-descent hypotheses, every initial mixed
fan/reentry mode lies on an infinite lineage-preserving trajectory with a
finite recurrent mode key.  The recurrent interval retains every certified
`FanReentryModeStep`.

This is still only a recurrence reduction: no impossibility of the recurrent
mixed-mode segment is claimed here. -/
theorem ClosedTriangulationCore.exists_recurrent_fanReentryModeKey_of_noMove23_noDescent
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hphi : 0 < PhiSupport K)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (start : FanReentryModeState K) :
    ∃ states : Nat → FanReentryModeState K,
      ∃ i j,
        states 0 = start ∧
        i < j ∧
        j ≤ Fintype.card (FanReentryModeKey K) ∧
        (states i).finiteKey hcore = (states j).finiteKey hcore ∧
        ∀ n,
          i ≤ n →
          n < j →
          FanReentryModeStep K (states n) (states (n + 1)) := by
  obtain ⟨states, hzero, hstep⟩ :=
    hcore.exists_perpetual_fanReentryMode_trajectory_of_noMove23_noDescent
      hM hphi hNoMove23 hNoDescent start

  obtain ⟨i, j, hij, hbound, hkey, hsegment⟩ :=
    exists_recurrent_fanReentryModeKey hcore states hstep

  exact
    ⟨states, i, j, hzero, hij, hbound, hkey, hsegment⟩


/-- Vertex-link connectivity propagates any coefficient assignment that is
constant across adjacent represented link triangles to the entire ambient
tetrahedron star of that vertex. This is the geometric transport step needed
in the proposed mod-two H₂ obstruction to witnessed reentry; no homology or
global descent is concluded here. -/
theorem ClosedTriangulationCore.vertexStar_weight_eq_of_linkAdjacent
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v : Nat} (hconnected : VertexLinkConnected K v)
    {α : Type} (weight : Tet → α)
    (hadj_eq :
      ∀ (σ ρ : LinkTriangle) (h : VertexLinkAdjacent K v σ ρ),
        weight (ambientTetOfVertexLinkTriangle K v ⟨σ, h.1⟩) =
        weight (ambientTetOfVertexLinkTriangle K v ⟨ρ, h.2.1⟩))
    {τ υ : Tet}
    (hτK : τ ∈ K.tets) (hυK : υ ∈ K.tets)
    (hvτ : v ∈ τ.verts) (hvυ : v ∈ υ.verts) :
    weight τ = weight υ := by
  obtain ⟨σ, hσ, hτ⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem K v τ hτK hvτ
  obtain ⟨ρ, hρ, hυ⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem K v υ hυK hvυ
  let C : LinkTriangle → Prop := fun q =>
    ∀ hq : q ∈ vertexLinkTriangles K v,
      weight (ambientTetOfVertexLinkTriangle K v ⟨σ, hσ⟩) =
        weight (ambientTetOfVertexLinkTriangle K v ⟨q, hq⟩)
  have hCσ : C σ := by
    intro hσ'
    have heq : (⟨σ, hσ'⟩ : {q // q ∈ vertexLinkTriangles K v}) =
        ⟨σ, hσ⟩ := Subtype.ext rfl
    rw [heq]
  have hclosed :
      ∀ q r, VertexLinkAdjacent K v q r → C q → C r := by
    intro q r hadj hCq hr
    have hq := hadj.1
    have hr' := hadj.2.1
    have hstep := hadj_eq q r hadj
    have heq : (⟨r, hr'⟩ : {q // q ∈ vertexLinkTriangles K v}) =
        ⟨r, hr⟩ := Subtype.ext rfl
    rw [heq] at hstep
    exact (hCq hq).trans hstep
  have hCρ :=
    hconnected.all_of_adjacent_closed C hσ hCσ hclosed ρ hρ
  have hweight := hCρ hρ
  rw [hcore.ambientTetOfVertexLinkTriangle_eq hσ hτK hτ,
    hcore.ambientTetOfVertexLinkTriangle_eq hρ hυK hυ] at hweight
  exact hweight

end Poincare
