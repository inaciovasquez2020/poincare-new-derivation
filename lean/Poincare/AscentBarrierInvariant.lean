import Poincare.Move2332InitialEscapeSeed
import Poincare.TriangulationTopologicalNormalizedS3
import Poincare.Move41TopologyPreservingDescent
import Poincare.Move32TopologyPreservingDescent

namespace Poincare

open WellFounded

/-- A genuine three-move Pachner macro-step: one legal 2→3 move (which
temporarily increases the canonical degree-four defect), followed by two
legal 3→2 moves. The source must be a certified closed triangulation core.
This relation does not presume that such a seed exists for every source. -/
def CertifiedAscentBarrierStep (K L : Triangulation) : Prop :=
  ClosedTriangulationCore K ∧
  ∃ (m : Move23Site) (seed : Move2332InitialEscapeSeed K m),
    L =
      (move2332SecondMove32 m seed.y).replace
        ((move2332FirstMove32 m seed.x).replace (m.replace K))

/-- An actual certified ascent-first macro-block decreases the degree-four
defect by exactly four, despite its first individual move increasing it. -/
theorem CertifiedAscentBarrierStep.PhiSupport_add_four_eq
    {K L : Triangulation} (h : CertifiedAscentBarrierStep K L) :
    PhiSupport L + 4 = PhiSupport K := by
  rcases h with ⟨hcore, m, seed, rfl⟩
  let s₁ := move2332FirstMove32 m seed.x
  let s₂ := move2332SecondMove32 m seed.y
  have h23 : m.LegalIn K := seed.move23_legal
  have h32₁ : s₁.LegalIn (m.replace K) :=
    seed.firstMove32_legal
  have h32₂ : s₂.LegalIn (s₁.replace (m.replace K)) :=
    seed.move32s_legal.2.2
  have hcore1 : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m h23
  have hcore2 : ClosedTriangulationCore (s₁.replace (m.replace K)) :=
    hcore1.move32Site_replace_closedCore s₁ h32₁
  have hcore3 : ClosedTriangulationCore
      (s₂.replace (s₁.replace (m.replace K))) :=
    hcore2.move32Site_replace_closedCore s₂ h32₂
  exact move2332Block_PhiSupport_add_four_eq
    hcore m h23 s₁ h32₁ hcore1 s₂ h32₂ hcore2 hcore3

/-- Each certified ascent-first macro-block is strict at its endpoints. -/
theorem CertifiedAscentBarrierStep.PhiSupport_lt
    {K L : Triangulation} (h : CertifiedAscentBarrierStep K L) :
    PhiSupport L < PhiSupport K := by
  have hdrop := h.PhiSupport_add_four_eq
  omega

/-- The macro-relation has a natural-number ranking function.
Therefore no cycle of these certified ascent-first blocks is possible. -/
theorem certifiedAscentBarrierStep_wellFounded :
    WellFounded (fun L K : Triangulation => CertifiedAscentBarrierStep K L) := by
  refine Subrelation.wf ?_ (measure PhiSupport).wf
  intro L K h
  exact h.PhiSupport_lt

/-- The macro-block itself cannot return to its starting triangulation. -/
theorem certifiedAscentBarrierStep_irrefl (K : Triangulation) :
    ¬ CertifiedAscentBarrierStep K K := by
  intro h
  have hlt := h.PhiSupport_lt
  exact (lt_irrefl _ hlt)

/-- The geometric implication is verified for any certified macro-step. -/
theorem CertifiedAscentBarrierStep.homeomorphic
    {K L : Triangulation} (h : CertifiedAscentBarrierStep K L) :
    Nonempty
      (triangulationTopologicalGeometricCarrier K ≃ₜ
        triangulationTopologicalGeometricCarrier L) := by
  rcases h with ⟨hcore, m, seed, rfl⟩
  let s₁ := move2332FirstMove32 m seed.x
  let s₂ := move2332SecondMove32 m seed.y
  have h23 : m.LegalIn K := seed.move23_legal
  have h32₁ : s₁.LegalIn (m.replace K) :=
    seed.firstMove32_legal
  have h32₂ : s₂.LegalIn (s₁.replace (m.replace K)) :=
    seed.move32s_legal.2.2
  have hcore1 : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m h23
  have hcore2 : ClosedTriangulationCore (s₁.replace (m.replace K)) :=
    hcore1.move32Site_replace_closedCore s₁ h32₁
  exact ⟨(hcore.move23GeometricCarrierHomeomorph m h23).trans
    ((hcore1.move32GeometricCarrierHomeomorph s₁ h32₁).trans
      (hcore2.move32GeometricCarrierHomeomorph s₂ h32₂))⟩

/-- REFUTED external geometric coverage candidate (not a proved global lemma).
The three alternatives are a degree-certified 4→1 descent, a certified 3→2
descent, or an initial legal 2→3 followed by two legal 3→2 moves.

Dougherty--Faber--Murphy's unflippable 16-vertex simplicial 3-sphere is a
counterexample: every pair of its vertices is an edge (forbidding 2→3), every
edge has incidence at least four (forbidding 3→2), and every vertex belongs
to 26 tetrahedra (forbidding 4→1). Its degree-four PhiSupport is 352 > 0.
The source identifies this finite complex as a combinatorial 3-sphere:
Bagchi--Datta, arXiv:1208.1389v2, Example 3.1(b), PDF p.13;
original: Dougherty--Faber--Murphy, DCG 32 (2004), pp.309--315.

The existing conditional implication below is still logically valid.
The unrestricted coverage premise is false, so it cannot close the
independent Poincare proof. An admissible replacement must allow initial
1→4 stabilization and potentially longer nonmonotone flip sequences.
This comment records the mathematical/literature boundary; the external
S³ identification is not independently Lean-formalized here. -/
def SimplyConnectedBarrierCoverage : Prop :=
  ∀ K : Triangulation,
    ClosedTriangulationCore K →
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K →
    TriangulationRealizationSimplyConnected K →
    0 < PhiSupport K →
    (∃ s : Move41Site,
      s.LegalIn K ∧
      6 ≤ vertexDegree K s.a ∧
      6 ≤ vertexDegree K s.b ∧
      6 ≤ vertexDegree K s.c ∧
      6 ≤ vertexDegree K s.d) ∨
    (∃ s : Move32Site,
      s.LegalIn K ∧
      5 ≤ vertexDegree K s.d ∧
      5 ≤ vertexDegree K s.e ∧
      (6 ≤ vertexDegree K s.d ∨ 6 ≤ vertexDegree K s.e)) ∨
    ∃ m : Move23Site, Nonempty (Move2332InitialEscapeSeed K m)

/-- Conditional reduction: the three-way coverage would imply the
existing global topology-preserving defect descent, including states
that have no ascent-first seven-vertex escape seed. -/
theorem barrierCoverage_implies_globalDescent
    (hcoverage : SimplyConnectedBarrierCoverage) :
    SimplyConnectedGlobalPhiSupportDescent := by
  intro K hcore hM hSC hpos
  rcases hcoverage K hcore hM hSC hpos with h41 | hrest
  · rcases h41 with ⟨s, hlegal, ha, hb, hc, hd⟩
    exact exists_closedCore_homeomorphic_PhiSupport_lt_of_move41
      hcore s hlegal ⟨ha, hb, hc, hd⟩
  · rcases hrest with h32 | hseed
    · rcases h32 with ⟨s, hlegal, hd, he, hhigh⟩
      exact exists_closedCore_homeomorphic_PhiSupport_lt_of_move32
        hcore s hlegal ⟨hd, he, hhigh⟩
    · rcases hseed with ⟨m, ⟨seed⟩⟩
      exact exists_closedCore_homeomorphic_PhiSupport_lt_of_initial_escape_seed
        hcore m seed

end Poincare
