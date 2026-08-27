import Poincare.GlobalMove32ReentryWholeCarrierLoop
import Poincare.CarrierPolygonalPath

open Set

namespace Poincare

/-- The canonical geometric midpoint of the shared edge of a realized
Move32 site, bundled in the carrier. -/
noncomputable def move32SharedEdgeMidpoint
    {K : Triangulation} (s : Move32Site) (h : s.RealizedIn K) :
    triangulationTopologicalGeometricCarrier K := by
  let tau := h.1.choose
  have htau := h.1.choose_spec.1
  have hverts := h.1.choose_spec.2
  refine ⟨triangulationTopologicalGeometricEdgeMidpoint s.d s.e, ?_⟩
  apply triangulationTopologicalTetBody_subset_carrier K htau
  apply triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody
  · exact (hverts s.d).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  · exact (hverts s.e).2 (by simp [Move32Site.targetTet₀, Tet.verts])

theorem move32SharedEdgeMidpoint_eq_of_endpoints
    {K : Triangulation} {s t : Move32Site}
    (hs : s.RealizedIn K) (ht : t.RealizedIn K)
    (h : (s.d = t.d ∧ s.e = t.e) ∨ (s.d = t.e ∧ s.e = t.d)) :
    move32SharedEdgeMidpoint s hs = move32SharedEdgeMidpoint t ht := by
  apply Subtype.ext
  change triangulationTopologicalGeometricEdgeMidpoint s.d s.e =
    triangulationTopologicalGeometricEdgeMidpoint t.d t.e
  rcases h with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2]
    simp only [move32SharedEdgeMidpoint,
      triangulationTopologicalGeometricEdgeMidpoint]
    ac_rfl

/-- A witnessed reentry step realized as the canonical three-segment trace
through precisely a represented target tetrahedron, the witnessed source
tetrahedron, and the witnessed reentry tetrahedron.  The initial quarter of
the parameter interval is certified to remain in the realized target
tetrahedron of the source site. -/
structure WitnessedReentryTransitionArc (K : Triangulation)
    (s t : Move32Site) (hs : s.RealizedIn K) where
  targetRealized : t.RealizedIn K
  path : Path (move32SharedEdgeMidpoint s hs)
    (move32SharedEdgeMidpoint t targetRealized)
  initialTarget : Tet
  initialTarget_mem : initialTarget ∈ K.tets
  initialTarget_same : SameTetVertices initialTarget s.targetTet₀
  initial_quarter_supported :
    ∀ u : unitInterval,
      (u : ℝ) ≤ 1 / 4 →
      (path u).1 ∈ triangulationTopologicalTetBody initialTarget
  supportingTets : List Tet
  supportingTets_mem : ∀ tau ∈ supportingTets, tau ∈ K.tets
  range_supported : Set.range path ⊆
    ⋃ tau ∈ supportingTets,
      Subtype.val ⁻¹' triangulationTopologicalTetBody tau

theorem witnessedReentry_transitionArc
    {K : Triangulation} (s t : Move32Site) (hs : s.RealizedIn K)
    (hstep : Move32SourceFaceWitnessedReentry K s t) :
    Nonempty (WitnessedReentryTransitionArc K s t hs) := by
  classical
  obtain ⟨target, htarget, htargetVerts⟩ := hs.1
  rcases hstep with
    ⟨tau, rho, x, y, sigma, htau, hrho, htrne,
      haTau, hbTau, hcTau, haRho, hbRho, hcRho,
      hxTau, hxabc, hyRho, hyabc, hxy, hsigma, hxSigma, hySigma,
      hnonself, htd, hte, ht, hthree, hobstruction⟩
  have haTarget : s.a ∈ target.verts :=
    (htargetVerts s.a).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  have hdTarget : s.d ∈ target.verts :=
    (htargetVerts s.d).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  have heTarget : s.e ∈ target.verts :=
    (htargetVerts s.e).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  have haSupport : s.a ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨target, htarget, haTarget⟩
  have hxSupport : x ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htau, hxTau⟩
  let pa := triangulationTopologicalCarrierVertex K s.a haSupport
  let px := triangulationTopologicalCarrierVertex K x hxSupport
  have hm0 : (move32SharedEdgeMidpoint s hs).1 ∈
      triangulationTopologicalTetBody target :=
    triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody hdTarget heTarget
  have hpa0 : pa.1 ∈ triangulationTopologicalTetBody target :=
    triangulationTopologicalGeometricVertex_mem_tetBody haTarget
  have hpa1 : pa.1 ∈ triangulationTopologicalTetBody tau :=
    triangulationTopologicalGeometricVertex_mem_tetBody haTau
  have hpx1 : px.1 ∈ triangulationTopologicalTetBody tau :=
    triangulationTopologicalGeometricVertex_mem_tetBody hxTau
  have hmt : (move32SharedEdgeMidpoint t ht).1 ∈
      triangulationTopologicalTetBody sigma := by
    apply triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody
    · simpa [htd] using hxSigma
    · simpa [hte] using hySigma
  have hpx2 : px.1 ∈ triangulationTopologicalTetBody sigma :=
    triangulationTopologicalGeometricVertex_mem_tetBody hxSigma
  let a0 := carrierSegmentInTet K target htarget _ _ hm0 hpa0
  let a1 := carrierSegmentInTet K tau htau _ _ hpa1 hpx1
  let a2 := carrierSegmentInTet K sigma hsigma _ _ hpx2 hmt
  refine ⟨{
    targetRealized := ht
    path := (a0.trans a1).trans a2
    initialTarget := target
    initialTarget_mem := htarget
    initialTarget_same := htargetVerts
    initial_quarter_supported := ?_
    supportingTets := [target, tau, sigma]
    supportingTets_mem := ?_
    range_supported := ?_ }⟩
  · intro u hu
    have huHalf : (u : ℝ) ≤ 1 / 2 := by
      linarith
    have htwo : 2 * (u : ℝ) ≤ 1 / 2 := by
      linarith
    rw [Path.trans_apply]
    split_ifs with houter
    · rw [Path.trans_apply]
      split_ifs with hinner
      · exact carrierSegmentInTet_mem K target htarget _ _ hm0 hpa0 _
      · exact (hinner (by simpa using htwo)).elim
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  · rw [Path.trans_range, Path.trans_range]
    rintro z ((⟨u, rfl⟩ | ⟨u, rfl⟩) | ⟨u, rfl⟩)
    · apply Set.mem_iUnion_of_mem target
      apply Set.mem_iUnion_of_mem (by simp)
      exact carrierSegmentInTet_mem K target htarget _ _ hm0 hpa0 u
    · apply Set.mem_iUnion_of_mem tau
      apply Set.mem_iUnion_of_mem (by simp)
      exact carrierSegmentInTet_mem K tau htau _ _ hpa1 hpx1 u
    · apply Set.mem_iUnion_of_mem sigma
      apply Set.mem_iUnion_of_mem (by simp)
      exact carrierSegmentInTet_mem K sigma hsigma _ _ hpx2 hmt u

/-- Concatenate an indexed sequence of transition arcs in its actual order,
without inserting an initial constant half-segment before the first arc. -/
noncomputable def orderedTransitionPath
    {X : Type*} [TopologicalSpace X] (p : Nat → X)
    (arc : ∀ n, Path (p n) (p (n + 1))) : ∀ m, Path (p 0) (p m)
  | 0 => Path.refl _
  | 1 => arc 0
  | Nat.succ (Nat.succ m) =>
      (orderedTransitionPath p arc (Nat.succ m)).trans (arc (Nat.succ m))

/-- The exact ordered recurrent loop determined by the crossing, realized
sites, and witnessed transition arcs, transported to the chosen basepoint. -/
noncomputable def witnessedReentryOrderedLoop
    {K : Triangulation}
    (crossing : WitnessedReentryCrossingCertificate K)
    (realized : ∀ n, (crossing.sites n).RealizedIn K)
    (steps : ∀ n, WitnessedReentryTransitionArc K
      (crossing.sites n) (crossing.sites (n + 1)) (realized n))
    (basepoint : triangulationTopologicalGeometricCarrier K)
    (hbase : basepoint =
      move32SharedEdgeMidpoint (crossing.sites crossing.anchorIndex)
        (realized crossing.anchorIndex)) :
    Path basepoint basepoint := by
  subst basepoint
  let p : Nat → triangulationTopologicalGeometricCarrier K := fun n =>
    move32SharedEdgeMidpoint (crossing.sites (crossing.anchorIndex + n))
      (realized (crossing.anchorIndex + n))
  let arcs : ∀ n, Path (p n) (p (n + 1)) := fun n => by
    let a := steps (crossing.anchorIndex + n)
    exact a.path.cast rfl (by apply Subtype.ext; rfl)
  have hle : crossing.anchorIndex ≤ crossing.predecessorIndex + 1 := by
    have := crossing.gap
    omega
  let m := crossing.predecessorIndex + 1 - crossing.anchorIndex
  have hendIndex : crossing.anchorIndex + m = crossing.predecessorIndex + 1 := by
    simp [m, Nat.add_sub_of_le hle]
  have hend : p m = p 0 := by
    dsimp [p]
    rw [hendIndex]
    simpa using move32SharedEdgeMidpoint_eq_of_endpoints
      (realized (crossing.predecessorIndex + 1))
      (realized crossing.anchorIndex) crossing.return_edge_eq_anchor
  let raw : Path (p 0) (p m) := orderedTransitionPath p arcs m
  exact raw.cast rfl hend.symm

/-- A recurrence-driven polygonal loop.  Its construction uses every
transition in the ordered recurrent interval and never uses the old
`crossingPath` or its reverse. -/
structure WitnessedReentryPolygonalLoopCertificate (K : Triangulation) where
  crossing : WitnessedReentryCrossingCertificate K
  ordered : WitnessedReentryOrderedTraceCertificate K
  ordered_crossing : ordered.crossing = crossing
  realized : ∀ n, (crossing.sites n).RealizedIn K
  steps : ∀ n, WitnessedReentryTransitionArc K
    (crossing.sites n) (crossing.sites (n + 1)) (realized n)
  basepoint : triangulationTopologicalGeometricCarrier K
  basepoint_eq : basepoint =
    move32SharedEdgeMidpoint (crossing.sites crossing.anchorIndex)
      (realized crossing.anchorIndex)
  polygonalLoop : Path basepoint basepoint
  anchor_return_midpoint :
    move32SharedEdgeMidpoint
      (crossing.sites (crossing.predecessorIndex + 1))
        (realized (crossing.predecessorIndex + 1)) =
      move32SharedEdgeMidpoint (crossing.sites crossing.anchorIndex)
        (realized crossing.anchorIndex)
  polygonalLoop_eq_ordered :
    polygonalLoop =
      witnessedReentryOrderedLoop crossing realized steps basepoint basepoint_eq
  predecessor_sourceFace_crossing :
    ¬ (∀ z : Nat,
      z ∈ [(crossing.sites crossing.predecessorIndex).a,
        (crossing.sites crossing.predecessorIndex).b,
        (crossing.sites crossing.predecessorIndex).c] ↔
      z ∈ [(crossing.sites crossing.anchorIndex).a,
        (crossing.sites crossing.anchorIndex).b,
        (crossing.sites crossing.anchorIndex).c])
  two_sided_carrier_escape :
    (∃ q ∈ [(crossing.sites (crossing.predecessorIndex + 1)).a,
        (crossing.sites (crossing.predecessorIndex + 1)).b,
        (crossing.sites (crossing.predecessorIndex + 1)).c],
      q ∉ [(crossing.sites crossing.anchorIndex).a,
        (crossing.sites crossing.anchorIndex).b,
        (crossing.sites crossing.anchorIndex).c,
        (crossing.sites crossing.anchorIndex).d,
        (crossing.sites crossing.anchorIndex).e]) ∨
    (∃ z ∈ [(crossing.sites crossing.predecessorIndex).a,
        (crossing.sites crossing.predecessorIndex).b,
        (crossing.sites crossing.predecessorIndex).c],
      z ∉ [(crossing.sites (crossing.predecessorIndex + 1)).a,
        (crossing.sites (crossing.predecessorIndex + 1)).b,
        (crossing.sites (crossing.predecessorIndex + 1)).c,
        (crossing.sites (crossing.predecessorIndex + 1)).d,
        (crossing.sites (crossing.predecessorIndex + 1)).e])

/-- The certified recurrent interval gives a genuinely ordered polygonal
loop based at its shared-edge midpoint. -/
theorem ClosedTriangulationCore.exists_polygonalLoopCertificate_of_witnessedReentry_recurrent_crossing
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (c : WitnessedReentryCrossingCertificate K)
    (hrealized : ∀ n, (c.sites n).RealizedIn K)
    (hthree : ∀ n, (c.sites n).SharedEdgeExactlyThree K)
    (hwitnessed : ∀ n,
      Move32SourceFaceWitnessedReentry K (c.sites n) (c.sites (n + 1))) :
    Nonempty (WitnessedReentryPolygonalLoopCertificate K) := by
  classical
  let ordered : WitnessedReentryOrderedTraceCertificate K := {
    crossing := c
    traceAt := fun n _ _ => c.sites n
    traceAt_eq_site := by intros; rfl
    first_eq_anchor := rfl
    last_eq_return := rfl
    realized := by intro n _ _; exact hrealized n
    sharedEdgeExactlyThree := by intro n _ _; exact hthree n
    consecutive_witnessed := by intro n _ _; exact hwitnessed n }
  let stepArc : ∀ n, WitnessedReentryTransitionArc K
      (c.sites n) (c.sites (n + 1)) (hrealized n) := fun n =>
    (witnessedReentry_transitionArc (c.sites n) (c.sites (n + 1))
      (hrealized n) (hwitnessed n)).some
  let basepoint :=
    move32SharedEdgeMidpoint (c.sites c.anchorIndex)
      (hrealized c.anchorIndex)
  let loop : Path basepoint basepoint :=
    witnessedReentryOrderedLoop c hrealized stepArc basepoint rfl
  refine ⟨{
    crossing := c
    ordered := ordered
    ordered_crossing := rfl
    realized := hrealized
    steps := stepArc
    basepoint := basepoint
    basepoint_eq := rfl
    polygonalLoop := loop
    anchor_return_midpoint := move32SharedEdgeMidpoint_eq_of_endpoints
      (hrealized (c.predecessorIndex + 1))
      (hrealized c.anchorIndex) c.return_edge_eq_anchor
    polygonalLoop_eq_ordered := rfl
    predecessor_sourceFace_crossing := c.predecessor_sourceFace_ne_anchor
    two_sided_carrier_escape := c.twoSidedCarrierEscape }⟩

end Poincare
