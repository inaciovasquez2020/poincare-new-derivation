import Poincare.GlobalFanChordTransition
import Poincare.GlobalRepresentedEdgeIncidenceLowerBound
import Mathlib.Tactic

namespace Poincare

/-- A high-fan continuation anchored at the exact incoming witness.  The
incoming transition is retained as a whole; the selected adjacent pair is
based at the fan position representing its witness, and the common-face
third vertex and both ambient memberships are retained. -/
structure WitnessAnchoredFanStep
    (K : Triangulation) (v x : Nat)
    (T : FanChordTransition K v x) where
  fan : AmbientEdgeCyclicFan K T.z0 T.z1
  witnessPos :
    {s : LinkTriangle // s ∈ vertexLinkStarTriangles K T.z0 T.z1}
  witness_eq : fan.tetAt witnessPos = T.witness
  neighbor :
    {s : LinkTriangle // s ∈ vertexLinkStarTriangles K T.z0 T.z1}
  adjacent :
    (vertexLinkStarGraph K T.z0 T.z1).Adj witnessPos neighbor
  sharedThird : Nat
  sharedThird_ne : sharedThird ≠ T.z1
  sharedThird_mem_witness : sharedThird ∈ T.witness.verts
  sharedThird_mem_neighbor : sharedThird ∈ (fan.tetAt neighbor).verts
  outcome :
    (∃ m : Move23Site, m.LegalIn K) \/
    (K.tets.filter
      (fun t => T.z0 ∈ t.verts ∧ T.z1 ∈ t.verts)).length = 3 \/
    ∃ U : FanChordTransition K T.z0 T.z1, ∃ y : Nat,
      U.sigma = witnessPos ∧ U.rho = neighbor ∧ U.transverse = y ∧
      y ∈ (fan.tetAt witnessPos).verts ∧
      y ∈ (fan.tetAt neighbor).verts

/-- In the high-incidence branch, continue from a fan neighbor of the exact
incoming witness, rather than from an arbitrary adjacent pair.  The result
retains the incoming transition, witness identity, shared-face vertex, and
classification outcome. -/
theorem ClosedTriangulationCore.FanChordTransition.continue_high_anchored
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v x : Nat} (T : FanChordTransition K v x)
    (hhigh :
      4 ≤ (K.tets.filter
        (fun tau => T.z0 ∈ tau.verts ∧ T.z1 ∈ tau.verts)).length ∧
      Nonempty (AmbientEdgeCyclicFan K T.z0 T.z1)) :
    Nonempty (WitnessAnchoredFanStep K v x T) := by
  classical
  obtain ⟨F⟩ := hhigh.2
  have hpos :
      0 < (K.tets.filter
        (fun tau => T.z0 ∈ tau.verts ∧ T.z1 ∈ tau.verts)).length := by
    omega
  have hrep : VertexLinkVertexRepresented K T.z0 T.z1 :=
    hcore.vertexLinkVertexRepresented_of_edgeIncidence_pos
      T.z0 T.z1 T.endpoints_ne hpos
  have hdegree : VertexLinkStarDegreeTwo K T.z0 T.z1 :=
    hcore.vertexLinkStarDegreeTwo hrep
  obtain ⟨witnessPos, hwitness⟩ :=
    F.covers_ambient T.witness T.witness_mem T.z0_mem T.z1_mem
  obtain ⟨rho1, rho2, hne1, hne2, hne12, hadj1, hadj2, _⟩ :=
    hdegree witnessPos.1 witnessPos.2
  let neighbor :
      {s : LinkTriangle // s ∈ vertexLinkStarTriangles K T.z0 T.z1} :=
    ⟨rho1, hadj1.2.1⟩
  have hadj :
      (vertexLinkStarGraph K T.z0 T.z1).Adj witnessPos neighbor := by
    apply (vertexLinkStarGraph_adj K T.z0 T.z1 witnessPos.1 rho1).2
    exact ⟨Ne.symm hne1, hadj1⟩
  obtain ⟨y, hyx, hvw, hxw, hyw, hvn, hxn, hyn⟩ :=
    F.adjacent_tets_share_face hadj
  have hywitness : y ∈ T.witness.verts := by
    rw [← hwitness]
    exact hyw
  have houtcome :=
    hcore.ambientEdgeCyclicFan_adjacent_transition_lineage hM F hadj
  exact ⟨{
    fan := F
    witnessPos := witnessPos
    witness_eq := hwitness
    neighbor := neighbor
    adjacent := hadj
    sharedThird := y
    sharedThird_ne := hyx
    sharedThird_mem_witness := hywitness
    sharedThird_mem_neighbor := hyn
    outcome := houtcome
  }⟩

end Poincare
