import Poincare.GlobalMove32PerpetualWitnessedReentryPredecessorFaceCrossing
import Poincare.GlobalMove32ReentryTwoSidedCarrierEscape
import Poincare.GlobalMove32WitnessedReentryFreshEndpoints
import Poincare.TriangulationTopologicalVertexStarNeighborhood
import Mathlib.Topology.Connected.PathConnected

namespace Poincare

/--
Finite recurrent witnessed-reentry data, together with an actual loop in the
whole geometric carrier.  The final fields record the combinatorial crossing
carried by the endpoints of `crossingPath`; they deliberately make no claim
that this crossing is invariant under homotopy.
-/
structure WitnessedReentryCrossingCertificate (K : Triangulation) where
  sites : Nat → Move32Site
  anchorIndex : Nat
  predecessorIndex : Nat
  tau : Tet
  rho : Tet
  sigma : Tet
  gap : anchorIndex + 1 < predecessorIndex + 1
  finiteBound : predecessorIndex + 1 ≤ Fintype.card (SupportedEdgeState K)
  tau_mem : tau ∈ K.tets
  rho_mem : rho ∈ K.tets
  sigma_mem : sigma ∈ K.tets
  tau_rho_ne : ¬ SameTetVertices tau rho
  predecessor_source_mem_tau :
    (sites predecessorIndex).a ∈ tau.verts ∧
    (sites predecessorIndex).b ∈ tau.verts ∧
    (sites predecessorIndex).c ∈ tau.verts
  predecessor_source_mem_rho :
    (sites predecessorIndex).a ∈ rho.verts ∧
    (sites predecessorIndex).b ∈ rho.verts ∧
    (sites predecessorIndex).c ∈ rho.verts
  return_endpoints_cross :
    (sites (predecessorIndex + 1)).d ∈ tau.verts ∧
    (sites (predecessorIndex + 1)).e ∈ rho.verts ∧
    (sites (predecessorIndex + 1)).e ∉ tau.verts ∧
    (sites (predecessorIndex + 1)).d ∉ rho.verts
  return_endpoints_mem_sigma :
    (sites (predecessorIndex + 1)).d ∈ sigma.verts ∧
    (sites (predecessorIndex + 1)).e ∈ sigma.verts
  sigma_ne : ¬ SameTetVertices sigma tau ∧ ¬ SameTetVertices sigma rho
  return_edge_eq_anchor :
    (((sites (predecessorIndex + 1)).d = (sites anchorIndex).d ∧
        (sites (predecessorIndex + 1)).e = (sites anchorIndex).e) ∨
      ((sites (predecessorIndex + 1)).d = (sites anchorIndex).e ∧
        (sites (predecessorIndex + 1)).e = (sites anchorIndex).d))
  sigma_in_anchor_target :
    SameTetVertices sigma (sites anchorIndex).targetTet₀ ∨
    SameTetVertices sigma (sites anchorIndex).targetTet₁ ∨
    SameTetVertices sigma (sites anchorIndex).targetTet₂
  predecessor_sourceFace_ne_anchor :
    ¬ (∀ z : Nat,
      z ∈ [(sites predecessorIndex).a, (sites predecessorIndex).b,
        (sites predecessorIndex).c] ↔
      z ∈ [(sites anchorIndex).a, (sites anchorIndex).b,
        (sites anchorIndex).c])
  twoSidedCarrierEscape :
    (∃ q ∈ [(sites (predecessorIndex + 1)).a,
        (sites (predecessorIndex + 1)).b,
        (sites (predecessorIndex + 1)).c],
      q ∉ [(sites anchorIndex).a, (sites anchorIndex).b,
        (sites anchorIndex).c, (sites anchorIndex).d, (sites anchorIndex).e]) ∨
    (∃ z ∈ [(sites predecessorIndex).a, (sites predecessorIndex).b,
        (sites predecessorIndex).c],
      z ∉ [(sites (predecessorIndex + 1)).a,
        (sites (predecessorIndex + 1)).b,
        (sites (predecessorIndex + 1)).c,
        (sites (predecessorIndex + 1)).d,
        (sites (predecessorIndex + 1)).e])
  freshEndpoints :
    List.Disjoint
      [(sites (predecessorIndex + 1)).d, (sites (predecessorIndex + 1)).e]
      [(sites predecessorIndex).a, (sites predecessorIndex).b,
        (sites predecessorIndex).c, (sites predecessorIndex).d,
        (sites predecessorIndex).e]
  predecessorPoint : triangulationTopologicalGeometricCarrier K
  returnPoint : triangulationTopologicalGeometricCarrier K
  crossingPath : Path predecessorPoint returnPoint
  wholeCarrierLoop : Path predecessorPoint predecessorPoint
  loop_eq_crossingPath_trans_symm :
    wholeCarrierLoop = crossingPath.trans crossingPath.symm

/--
The loop currently carried by a witnessed-reentry crossing certificate is
unconditionally null-homotopic: it traverses the chosen crossing path and
then immediately traverses the same path backwards.  Thus the combinatorial
crossing fields of the certificate cannot, by themselves, make this loop a
nonzero global fundamental-group class.
-/
theorem WitnessedReentryCrossingCertificate.wholeCarrierLoop_homotopic_refl
    {K : Triangulation} (c : WitnessedReentryCrossingCertificate K) :
    Path.Homotopic c.wholeCarrierLoop (Path.refl c.predecessorPoint) := by
  rw [c.loop_eq_crossingPath_trans_symm]
  exact Path.Homotopic.trans_symm c.crossingPath

/--
The ordered finite interval underlying a recurrent crossing certificate.

Unlike the `sites` field of `WitnessedReentryCrossingCertificate`, the index
of `trace` is finite and starts at the recurrent anchor.  Its final entry is
the returned site (one step after the predecessor).  Thus no ordering
information has to be reconstructed from the crossing certificate later.
-/
structure WitnessedReentryOrderedTraceCertificate (K : Triangulation) where
  crossing : WitnessedReentryCrossingCertificate K
  traceAt : (n : Nat) →
    crossing.anchorIndex ≤ n → n ≤ crossing.predecessorIndex + 1 → Move32Site
  traceAt_eq_site : ∀ n hn₀ hn₁, traceAt n hn₀ hn₁ = crossing.sites n
  first_eq_anchor :
    traceAt crossing.anchorIndex (by omega)
      (by have h := crossing.gap; omega) =
      crossing.sites crossing.anchorIndex
  last_eq_return :
    traceAt (crossing.predecessorIndex + 1)
      (by have h := crossing.gap; omega) (by omega) =
      crossing.sites (crossing.predecessorIndex + 1)
  realized : ∀ n hn₀ hn₁, (traceAt n hn₀ hn₁).RealizedIn K
  sharedEdgeExactlyThree : ∀ n hn₀ hn₁,
    (traceAt n hn₀ hn₁).SharedEdgeExactlyThree K
  consecutive_witnessed :
    ∀ (n : Nat) (hn₀ : crossing.anchorIndex ≤ n)
      (hn₁ : n < crossing.predecessorIndex + 1),
      Move32SourceFaceWitnessedReentry K
        (traceAt n hn₀ (by omega))
        (traceAt (n + 1) (by omega) (by omega))

/-- Package a crossing certificate together with the actual ordered recurrent
interval.  This theorem is deliberately geometric-claim-free: in particular,
it does not use the old backtracking `wholeCarrierLoop` as the desired cycle. -/
theorem WitnessedReentryCrossingCertificate.exists_ordered_trace
    {K : Triangulation} (c : WitnessedReentryCrossingCertificate K)
    (hrealized : ∀ n, (c.sites n).RealizedIn K)
    (hthree : ∀ n, (c.sites n).SharedEdgeExactlyThree K)
    (hwitnessed : ∀ n,
      Move32SourceFaceWitnessedReentry K (c.sites n) (c.sites (n + 1))) :
    Nonempty (WitnessedReentryOrderedTraceCertificate K) := by
  let tr : (n : Nat) → c.anchorIndex ≤ n →
      n ≤ c.predecessorIndex + 1 → Move32Site := fun n _ _ => c.sites n
  refine ⟨{
    crossing := c
    traceAt := tr
    traceAt_eq_site := ?_
    first_eq_anchor := ?_
    last_eq_return := ?_
    realized := ?_
    sharedEdgeExactlyThree := ?_
    consecutive_witnessed := ?_ }⟩
  · intro n hn₀ hn₁
    rfl
  · simp [tr]
  · simp [tr]
  · intro n hn₀ hn₁
    exact hrealized _
  · intro n hn₀ hn₁
    exact hthree _
  · intro n hn₀ hn₁
    exact hwitnessed n

/--
The actual relative null-homotopy data supplied by simple connectivity for a
loop in the whole carrier.  Keeping the homotopy itself (rather than only its
propositional truncation) makes all four sides of the parameter square
available to a later finite relative-approximation argument.

This structure is intentionally independent of
`WitnessedReentryCrossingCertificate.wholeCarrierLoop`: a later stage must
supply the new geometrically constrained recurrent loop.
-/
structure CarrierLoopNullHomotopyData (K : Triangulation)
    (x : triangulationTopologicalGeometricCarrier K) (loop : Path x x) where
  homotopy : Path.Homotopy loop (Path.refl x)
  loop_boundary : ∀ t : unitInterval, homotopy (0, t) = loop t
  constant_boundary : ∀ t : unitInterval, homotopy (1, t) = x
  source_boundary : ∀ s : unitInterval, homotopy (s, 0) = x
  target_boundary : ∀ s : unitInterval, homotopy (s, 1) = x

/-- Simple connectivity produces an actual relative homotopy square for every
genuinely supplied carrier loop. -/
theorem exists_carrierLoopNullHomotopyData
    {K : Triangulation}
    (hSC : TriangulationRealizationSimplyConnected K)
    {x : triangulationTopologicalGeometricCarrier K} (loop : Path x x) :
    Nonempty (CarrierLoopNullHomotopyData K x loop) := by
  letI : SimplyConnectedSpace
      (triangulationTopologicalGeometricCarrier K) := hSC
  let H : Path.Homotopy loop (Path.refl x) :=
    (SimplyConnectedSpace.paths_homotopic loop (Path.refl x)).some
  refine ⟨{
    homotopy := H
    loop_boundary := ?_
    constant_boundary := ?_
    source_boundary := ?_
    target_boundary := ?_ }⟩
  · intro t
    exact H.apply_zero t
  · intro t
    exact H.apply_one t
  · intro s
    simpa using H.eq_fst s
      (show (0 : unitInterval) ∈ ({0, 1} : Set unitInterval) by simp)
  · intro s
    simpa using H.eq_fst s
      (show (1 : unitInterval) ∈ ({0, 1} : Set unitInterval) by simp)

theorem ClosedTriangulationCore.exists_wholeCarrierLoop_of_witnessedReentry_recurrent_crossing
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hSC : TriangulationRealizationSimplyConnected K)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (sites : Nat → Move32Site)
    (hrealized : ∀ n, (sites n).RealizedIn K)
    (hthree : ∀ n, (sites n).SharedEdgeExactlyThree K)
    (hwitnessed : ∀ n,
      Move32SourceFaceWitnessedReentry K (sites n) (sites (n + 1))) :
    Nonempty (WitnessedReentryCrossingCertificate K) := by
  classical
  obtain ⟨i, k, hgap, hbound, hstate, hstep, _⟩ :=
    hcore.exists_recurrent_returnSigma_target_of_perpetual_witnessedReentry
      sites hrealized hthree hwitnessed
  obtain ⟨tau, rho, sigma, hconfig⟩ :=
    hcore.exists_witnessedReentry_return_crossing_anchor_target_of_sharedSupportedEdgeState_eq
      (sites i) (sites k) (sites (k + 1))
      (hrealized i) (hthree i) (hrealized k) (hrealized (k + 1))
      hstep hstate
  rcases hconfig with
    ⟨htau, hrho, hsigma, htaurho, haTau, hbTau, hcTau,
      haRho, hbRho, hcRho, hdTau, heRho, hdSigma, heSigma,
      heNotTau, hdNotRho, hSigmaTau, hSigmaRho, hreturn, htarget⟩
  have hpredNe :=
    hcore.not_predecessor_sourceFace_support_eq_anchor_of_witnessedReentry_return_edge_of_no_degree_four
      hlinks hconn hNoFour (sites i) (sites k) (sites (k + 1))
      (hrealized i) hstep hreturn
  have hescape :=
    hcore.exists_return_sourceFace_vertex_outside_anchor_carrier_or_predecessor_sourceFace_vertex_outside_return_carrier_of_witnessedReentry_return_state_of_no_degree_four
      hlinks hconn hNoFour (sites i) (sites k) (sites (k + 1))
      (hrealized i) (hthree i) (hrealized k) (hrealized (k + 1))
      (hthree (k + 1)) hstep hstate
  have hfresh :=
    hcore.witnessedReentry_next_sharedEdge_disjoint_previous_carrier_of_no_degree_four
      hlinks hNoFour (sites k) (sites (k + 1)) (hrealized k) hstep
  have haSupport : (sites k).a ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htau, haTau⟩
  have hdSupport : (sites (k + 1)).d ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htau, hdTau⟩
  let p0 := triangulationTopologicalCarrierVertex K (sites k).a haSupport
  let p1 := triangulationTopologicalCarrierVertex K (sites (k + 1)).d hdSupport
  letI : SimplyConnectedSpace (triangulationTopologicalGeometricCarrier K) := hSC
  let crossing : Path p0 p1 := (PathConnectedSpace.joined p0 p1).somePath
  let loop : Path p0 p0 := crossing.trans crossing.symm
  exact ⟨{
    sites := sites
    anchorIndex := i
    predecessorIndex := k
    tau := tau
    rho := rho
    sigma := sigma
    gap := hgap
    finiteBound := hbound
    tau_mem := htau
    rho_mem := hrho
    sigma_mem := hsigma
    tau_rho_ne := htaurho
    predecessor_source_mem_tau := ⟨haTau, hbTau, hcTau⟩
    predecessor_source_mem_rho := ⟨haRho, hbRho, hcRho⟩
    return_endpoints_cross := ⟨hdTau, heRho, heNotTau, hdNotRho⟩
    return_endpoints_mem_sigma := ⟨hdSigma, heSigma⟩
    sigma_ne := ⟨hSigmaTau, hSigmaRho⟩
    return_edge_eq_anchor := hreturn
    sigma_in_anchor_target := htarget
    predecessor_sourceFace_ne_anchor := hpredNe
    twoSidedCarrierEscape := hescape
    freshEndpoints := hfresh
    predecessorPoint := p0
    returnPoint := p1
    crossingPath := crossing
    wholeCarrierLoop := loop
    loop_eq_crossingPath_trans_symm := rfl }⟩

end Poincare
