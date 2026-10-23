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
  sharedThird_ne_center : sharedThird ≠ T.z0
  sharedThird_mem_witness : sharedThird ∈ T.witness.verts
  sharedThird_mem_neighbor : sharedThird ∈ (fan.tetAt neighbor).verts
  outcome :
    (∃ m : Move23Site, m.LegalIn K) \/
    (K.tets.filter
      (fun t => T.z0 ∈ t.verts ∧ T.z1 ∈ t.verts)).length = 3 \/
    ∃ y : Nat, ∃ U : FanChordTransition K T.z0 T.z1,
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
  have hneSub : neighbor ≠ witnessPos := by
    intro heq
    apply hne1
    exact congrArg Subtype.val heq
  have hadj :
      (vertexLinkStarGraph K T.z0 T.z1).Adj witnessPos neighbor := by
    apply (vertexLinkStarGraph_adj K T.z0 T.z1 witnessPos neighbor).2
    exact ⟨hneSub, hadj1⟩
  obtain ⟨y, hyNodup, hvw, hxw, hyw, hvn, hxn, hyn⟩ :=
    hcore.ambientEdgeCyclicFan_adjacent_tets_share_face F hadj
  have hyx : y ≠ T.z1 := by
    intro heq
    subst y
    exact (List.nodup_cons.mp (List.nodup_cons.mp hyNodup).2).1 (by simp)
  have hyv : y ≠ T.z0 := by
    intro heq
    subst y
    exact (List.nodup_cons.mp hyNodup).1 (by simp)
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
    sharedThird_ne_center := hyv
    sharedThird_mem_witness := hywitness
    sharedThird_mem_neighbor := hyn
    outcome := houtcome
  }⟩


/-- In the classifier branch, the classifier's transverse vertex is the
same common-face vertex already retained by the anchored step.  The proof is
local: both vertices belong to both adjacent link triangles, and three
distinct common vertices are forbidden by the closed-core link condition. -/
theorem WitnessAnchoredFanStep.classifier_transverse_eq_sharedThird
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v x : Nat} {T : FanChordTransition K v x}
    (S : WitnessAnchoredFanStep K v x T)
    {y : Nat} {U : FanChordTransition K T.z0 T.z1}
    (hσ : U.sigma = S.witnessPos)
    (hρ : U.rho = S.neighbor)
    (hy : U.transverse = y)
    (hyw : y ∈ (S.fan.tetAt S.witnessPos).verts)
    (hyn : y ∈ (S.fan.tetAt S.neighbor).verts) :
    y = S.sharedThird := by
  by_contra hne_y_shared
  have hσmem : S.witnessPos.1 ∈ vertexLinkTriangles K T.z0 :=
    ((mem_vertexLinkStarTriangles_iff K T.z0 T.z1
      S.witnessPos.1).1 S.witnessPos.2).1
  have hρmem : S.neighbor.1 ∈ vertexLinkTriangles K T.z0 :=
    ((mem_vertexLinkStarTriangles_iff K T.z0 T.z1
      S.neighbor.1).1 S.neighbor.2).1
  have hxσ : T.z1 ∈ S.witnessPos.1.verts :=
    ((mem_vertexLinkStarTriangles_iff K T.z0 T.z1
      S.witnessPos.1).1 S.witnessPos.2).2
  have hxρ : T.z1 ∈ S.neighbor.1.verts :=
    ((mem_vertexLinkStarTriangles_iff K T.z0 T.z1
      S.neighbor.1).1 S.neighbor.2).2
  have hsharedσ : S.sharedThird ∈ S.witnessPos.1.verts := by
    have htet : S.sharedThird ∈ (S.fan.tetAt S.witnessPos).verts := by
      rw [S.witness_eq]
      exact S.sharedThird_mem_witness
    exact (S.fan.tetAt S.witnessPos).mem_linkTriangleAt?_iff
      T.z0 S.sharedThird S.witnessPos.1 (S.fan.tetAt_link S.witnessPos)
      S.sharedThird_ne_center |>.2 htet
  have hsharedρ : S.sharedThird ∈ S.neighbor.1.verts :=
    (S.fan.tetAt S.neighbor).mem_linkTriangleAt?_iff
      T.z0 S.sharedThird S.neighbor.1 (S.fan.tetAt_link S.neighbor)
      S.sharedThird_ne_center |>.2 S.sharedThird_mem_neighbor
  have hyσ : y ∈ S.witnessPos.1.verts := by
    have hne : U.transverse ≠ T.z0 := by
      intro heq
      exact (List.nodup_cons.mp U.distinct).1 (by simp [heq])
    have hmem : U.transverse ∈ U.sigma.1.verts :=
      (U.leftTet.mem_linkTriangleAt?_iff T.z0 U.transverse U.sigma.1
        U.leftTet_link hne).2
        ((U.leftTet_match U.transverse).2 (by simp [Tet.verts]))
    rw [← congrArg Subtype.val hσ, ← hy]
    exact hmem
  have hyρ : y ∈ S.neighbor.1.verts := by
    have hne : U.transverse ≠ T.z0 := by
      intro heq
      exact (List.nodup_cons.mp U.distinct).1 (by simp [heq])
    have hmem : U.transverse ∈ U.rho.1.verts :=
      (U.rightTet.mem_linkTriangleAt?_iff T.z0 U.transverse U.rho.1
        U.rightTet_link hne).2
        ((U.rightTet_match U.transverse).2 (by simp [Tet.verts]))
    rw [← congrArg Subtype.val hρ, ← hy]
    exact hmem
  have hxy0 : T.z1 ≠ S.sharedThird := Ne.symm S.sharedThird_ne
  have hxy1 : T.z1 ≠ y := by
    intro heq
    have hne : U.transverse ≠ T.z1 := by
      intro heq'
      exact (List.nodup_cons.mp (List.nodup_cons.mp U.distinct).2).1
        (by simp [heq'])
    exact hne (by rw [hy, heq])
  exact linkTriangles_three_common_vertices_impossible hcore
    hσmem hρmem (by
      intro heq
      have hsub : S.witnessPos = S.neighbor := Subtype.ext heq
      exact S.adjacent.ne hsub)
    hxσ hxρ hsharedσ hsharedρ hyσ hyρ hxy0 hxy1
    (Ne.symm hne_y_shared)

end Poincare
