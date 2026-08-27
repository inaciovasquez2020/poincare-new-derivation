import Poincare.GlobalMove32ReentryDyadicGridVertices
import Poincare.GlobalMove32SharedEdgeThreeTetSaturation

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
Every label on the constant source boundary of a finite square-grid filling
shares a represented tetrahedron with one fixed represented vertex at the
basepoint.  This is the first boundary-cone reduction available from the
finite positive-coordinate filling; it does not yet assert a legal Pachner
move.
-/
theorem finite_squareGrid_sourceBoundary_commonApex_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (D : Nat)
    (hD : 0 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) :
    ∃ apex : Nat,
      apex ∈ vertexSupport K ∧
      0 < x.1 apex ∧
      ∀ i : Fin D,
        ∃ tau : Tet,
          tau ∈ K.tets ∧
          label i ⟨0, hD⟩ ∈ tau.verts ∧
          apex ∈ tau.verts := by
  obtain ⟨apex, hapexSupport, hapexPositive⟩ :=
    carrier_exists_vertexSupport_coordinate_pos x

  refine ⟨apex, hapexSupport, hapexPositive, ?_⟩
  intro i

  let j0 : Fin D := ⟨0, hD⟩
  let z : unitInterval × unitInterval :=
    squareGridCellSource D hD i j0

  have hzCell : z ∈ squareGridCell D hD i j0 := by
    exact squareGridCellSource_mem_probe D hD i j0

  have hzSecond : z.2 = (0 : unitInterval) := by
    dsimp [z, squareGridCellSource]
    simpa [j0] using squareGridParameter_zero_probe D hD

  have hzSource : H.homotopy z = x := by
    have hzEq : z = (z.1, (0 : unitInterval)) := by
      apply Prod.ext
      · rfl
      · exact hzSecond
    rw [hzEq]
    exact H.source_boundary z.1

  have hlabelPositive : 0 < x.1 (label i j0) := by
    have h := hpositive i j0 z hzCell
    rw [hzSource] at h
    exact h

  exact carrier_two_positive_coordinates_common_tet_probe
    x hlabelPositive hapexPositive

/--
The finite filling is synchronized with the genuine loop boundary at the
recurrent anchor: a label on the left boundary at loop parameter zero occurs
in one represented tetrahedron together with the first endpoint of the
anchor shared edge.

This is deliberately weaker than a Pachner-ear statement.  It repairs the
boundary orientation first: `homotopy (0,t)` is the polygonal-loop boundary,
whereas `homotopy (s,0)` is constant.
-/
theorem finite_squareGrid_loopBoundary_anchor_endpoint_tet_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (D : Nat)
    (hD : 0 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) :
    ∃ j : Fin D,
      ∃ tau : Tet,
        tau ∈ K.tets ∧
        label ⟨0, hD⟩ j ∈ tau.verts ∧
        (p.crossing.sites p.crossing.anchorIndex).d ∈ tau.verts := by
  let s : Move32Site :=
    p.crossing.sites p.crossing.anchorIndex

  have hsRealized : s.RealizedIn K := by
    exact p.realized p.crossing.anchorIndex

  have hde : s.d ≠ s.e :=
    (hcore.move32_sharedEdge_supported s hsRealized).2.2

  obtain ⟨j, hcell, hloop⟩ :=
    H.exists_squareGrid_loopBoundary_cell_probe
      D hD (0 : unitInterval)

  have hlabelPositive :
      0 < p.basepoint.1 (label ⟨0, hD⟩ j) := by
    have h :=
      hpositive ⟨0, hD⟩ j
        ((0 : unitInterval), (0 : unitInterval)) hcell
    rw [hloop] at h
    simpa using h

  have hdPositive : 0 < p.basepoint.1 s.d := by
    rw [p.basepoint_eq]
    change
      0 <
        triangulationTopologicalGeometricEdgeMidpoint
          s.d s.e s.d
    simp [triangulationTopologicalGeometricEdgeMidpoint_apply, hde.symm]

  obtain ⟨tau, htau, hlabelTau, hdTau⟩ :=
    carrier_two_positive_coordinates_common_tet_probe
      p.basepoint hlabelPositive hdPositive

  exact ⟨j, tau, htau, hlabelTau, hdTau⟩

/--
At the recurrent anchor, one genuine loop-boundary filling label and both
endpoints of the represented anchor shared edge occur in a single represented
tetrahedron.  This is still only a boundary synchronization statement; it
does not assert `Move32Site.LegalIn`.
-/
theorem finite_squareGrid_loopBoundary_anchor_sharedEdge_tet_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (D : Nat)
    (hD : 0 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) :
    ∃ j : Fin D,
      ∃ tau : Tet,
        tau ∈ K.tets ∧
        label ⟨0, hD⟩ j ∈ tau.verts ∧
        (p.crossing.sites p.crossing.anchorIndex).d ∈ tau.verts ∧
        (p.crossing.sites p.crossing.anchorIndex).e ∈ tau.verts := by
  let s : Move32Site :=
    p.crossing.sites p.crossing.anchorIndex

  have hsRealized : s.RealizedIn K := by
    exact p.realized p.crossing.anchorIndex

  have hde : s.d ≠ s.e :=
    (hcore.move32_sharedEdge_supported s hsRealized).2.2

  obtain ⟨j, hcell, hloop⟩ :=
    H.exists_squareGrid_loopBoundary_cell_probe
      D hD (0 : unitInterval)

  have hlabelPositive :
      0 < p.basepoint.1 (label ⟨0, hD⟩ j) := by
    have h :=
      hpositive ⟨0, hD⟩ j
        ((0 : unitInterval), (0 : unitInterval)) hcell
    rw [hloop] at h
    simpa using h

  have hdPositive : 0 < p.basepoint.1 s.d := by
    rw [p.basepoint_eq]
    change
      0 <
        triangulationTopologicalGeometricEdgeMidpoint
          s.d s.e s.d
    simp [triangulationTopologicalGeometricEdgeMidpoint_apply, hde.symm]

  have hePositive : 0 < p.basepoint.1 s.e := by
    rw [p.basepoint_eq]
    change
      0 <
        triangulationTopologicalGeometricEdgeMidpoint
          s.d s.e s.e
    simp [triangulationTopologicalGeometricEdgeMidpoint_apply, hde]

  obtain ⟨F, _, tau, htau, hFtau, a, _, _, hap⟩ :=
    carrier_exists_finite_barycentric_support p.basepoint

  have hlabelF : label ⟨0, hD⟩ j ∈ F := by
    by_contra hlabelF
    have hz : p.basepoint.1 (label ⟨0, hD⟩ j) = 0 := by
      rw [geometricVertex_weighted_sum_coordinate
        F a p.basepoint.1 hap (label ⟨0, hD⟩ j)]
      simp [hlabelF]
    linarith

  have hdF : s.d ∈ F := by
    by_contra hdF
    have hz : p.basepoint.1 s.d = 0 := by
      rw [geometricVertex_weighted_sum_coordinate F a p.basepoint.1 hap s.d]
      simp [hdF]
    linarith

  have heF : s.e ∈ F := by
    by_contra heF
    have hz : p.basepoint.1 s.e = 0 := by
      rw [geometricVertex_weighted_sum_coordinate F a p.basepoint.1 hap s.e]
      simp [heF]
    linarith

  exact ⟨
    j,
    tau,
    htau,
    List.mem_toFinset.mp (hFtau hlabelF),
    List.mem_toFinset.mp (hFtau hdF),
    List.mem_toFinset.mp (hFtau heF)
  ⟩

/--
The first boundary-ear/source-face synchronization step.  The represented
tetrahedron containing the loop-boundary filling label and the recurrent
anchor shared edge is one of the anchor's three realized target tetrahedra.
Consequently it contains the corresponding source-face edge `ab`, `ac`, or
`bc`.  No source-face absence or Move32 legality is asserted here.
-/
theorem finite_squareGrid_loopBoundary_anchor_target_sourceEdge_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (D : Nat)
    (hD : 0 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) :
    ∃ j : Fin D,
      ∃ tau : Tet,
        tau ∈ K.tets ∧
        label ⟨0, hD⟩ j ∈ tau.verts ∧
        ((SameTetVertices tau
              (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∧
            (p.crossing.sites p.crossing.anchorIndex).a ∈ tau.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).b ∈ tau.verts) ∨
          (SameTetVertices tau
              (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
            (p.crossing.sites p.crossing.anchorIndex).a ∈ tau.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).c ∈ tau.verts) ∨
          (SameTetVertices tau
              (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
            (p.crossing.sites p.crossing.anchorIndex).b ∈ tau.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).c ∈ tau.verts)) := by
  let s : Move32Site :=
    p.crossing.sites p.crossing.anchorIndex

  have hsRealized : s.RealizedIn K := by
    exact p.realized p.crossing.anchorIndex

  have hanchorThree : s.SharedEdgeExactlyThree K := by
    have h :=
      p.ordered.sharedEdgeExactlyThree
        p.ordered.crossing.anchorIndex
        (by omega)
        (by
          have hg := p.ordered.crossing.gap
          omega)
    rw [p.ordered.traceAt_eq_site] at h
    rw [p.ordered_crossing] at h
    exact h

  obtain ⟨j, tau, htau, hlabelTau, hdTau, heTau⟩ :=
    H.finite_squareGrid_loopBoundary_anchor_sharedEdge_tet_probe
      hcore p D hD label hpositive

  change s.d ∈ tau.verts at hdTau
  change s.e ∈ tau.verts at heTau

  have htarget :=
    hcore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
      s hsRealized hanchorThree htau hdTau heTau

  refine ⟨j, tau, htau, hlabelTau, ?_⟩
  rcases htarget with h0 | h1 | h2

  · have ha : s.a ∈ tau.verts := by
      apply (h0 s.a).2
      simp [Move32Site.targetTet₀, Tet.verts]
    have hb : s.b ∈ tau.verts := by
      apply (h0 s.b).2
      simp [Move32Site.targetTet₀, Tet.verts]
    exact Or.inl ⟨h0, ha, hb⟩

  · have ha : s.a ∈ tau.verts := by
      apply (h1 s.a).2
      simp [Move32Site.targetTet₁, Tet.verts]
    have hc : s.c ∈ tau.verts := by
      apply (h1 s.c).2
      simp [Move32Site.targetTet₁, Tet.verts]
    exact Or.inr (Or.inl ⟨h1, ha, hc⟩)

  · have hb : s.b ∈ tau.verts := by
      apply (h2 s.b).2
      simp [Move32Site.targetTet₂, Tet.verts]
    have hc : s.c ∈ tau.verts := by
      apply (h2 s.c).2
      simp [Move32Site.targetTet₂, Tet.verts]
    exact Or.inr (Or.inr ⟨h2, hb, hc⟩)

/--
First explicit boundary ear/cancellation fork.  On a grid with at least two
rows, take the southwest loop-boundary cell and the boundary cell immediately
above it.  The southwest label lies in one of the recurrent anchor's three
target tetrahedra.  Either the adjacent label already lies in that same target
tetrahedron (the cancellation branch), or overlap compatibility supplies a
distinct represented tetrahedron containing both adjacent labels (the first
ear-escape branch).

This is only a finite-filling combinatorial fork.  It does not yet assert a
legal Pachner move.
-/
theorem finite_squareGrid_loopBoundary_anchor_firstEarCancellationFork_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (D : Nat)
    (hD : 0 < D)
    (hDtwo : 1 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) :
    ∃ tau : Tet,
      tau ∈ K.tets ∧
      label ⟨0, hD⟩ ⟨0, hD⟩ ∈ tau.verts ∧
      (((SameTetVertices tau
              (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∧
            (p.crossing.sites p.crossing.anchorIndex).a ∈ tau.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).b ∈ tau.verts) ∨
          (SameTetVertices tau
              (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
            (p.crossing.sites p.crossing.anchorIndex).a ∈ tau.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).c ∈ tau.verts) ∨
          (SameTetVertices tau
              (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
            (p.crossing.sites p.crossing.anchorIndex).b ∈ tau.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).c ∈ tau.verts)) ∧
        (label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈ tau.verts ∨
          ∃ rho : Tet,
            rho ∈ K.tets ∧
            rho ≠ tau ∧
            label ⟨0, hD⟩ ⟨0, hD⟩ ∈ rho.verts ∧
            label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈ rho.verts)) := by
  let s : Move32Site :=
    p.crossing.sites p.crossing.anchorIndex
  let i0 : Fin D := ⟨0, hD⟩
  let j0 : Fin D := ⟨0, hD⟩
  let j1 : Fin D := ⟨1, hDtwo⟩

  have hsRealized : s.RealizedIn K := by
    exact p.realized p.crossing.anchorIndex

  have hde : s.d ≠ s.e :=
    (hcore.move32_sharedEdge_supported s hsRealized).2.2

  have hanchorThree : s.SharedEdgeExactlyThree K := by
    have h :=
      p.ordered.sharedEdgeExactlyThree
        p.ordered.crossing.anchorIndex
        (by omega)
        (by
          have hg := p.ordered.crossing.gap
          omega)
    rw [p.ordered.traceAt_eq_site] at h
    rw [p.ordered_crossing] at h
    exact h

  let z0 : unitInterval × unitInterval :=
    squareGridCellSource D hD i0 j0

  have hz0Cell : z0 ∈ squareGridCell D hD i0 j0 := by
    exact squareGridCellSource_mem_probe D hD i0 j0

  have hz0Second : z0.2 = (0 : unitInterval) := by
    dsimp [z0, squareGridCellSource]
    simpa [j0] using squareGridParameter_zero_probe D hD

  have hz0Source : H.homotopy z0 = p.basepoint := by
    have hzEq : z0 = (z0.1, (0 : unitInterval)) := by
      apply Prod.ext
      · rfl
      · exact hz0Second
    rw [hzEq]
    exact H.source_boundary z0.1

  have hlabel0Positive :
      0 < p.basepoint.1 (label i0 j0) := by
    have h := hpositive i0 j0 z0 hz0Cell
    rw [hz0Source] at h
    exact h

  have hdPositive : 0 < p.basepoint.1 s.d := by
    rw [p.basepoint_eq]
    change
      0 <
        triangulationTopologicalGeometricEdgeMidpoint
          s.d s.e s.d
    simp [triangulationTopologicalGeometricEdgeMidpoint_apply, hde.symm]

  have hePositive : 0 < p.basepoint.1 s.e := by
    rw [p.basepoint_eq]
    change
      0 <
        triangulationTopologicalGeometricEdgeMidpoint
          s.d s.e s.e
    simp [triangulationTopologicalGeometricEdgeMidpoint_apply, hde]

  obtain ⟨F, _, tau, htau, hFtau, a, _, _, hap⟩ :=
    carrier_exists_finite_barycentric_support p.basepoint

  have hlabel0F : label i0 j0 ∈ F := by
    by_contra hlabel0F
    have hz : p.basepoint.1 (label i0 j0) = 0 := by
      rw [geometricVertex_weighted_sum_coordinate
        F a p.basepoint.1 hap (label i0 j0)]
      simp [hlabel0F]
    linarith

  have hdF : s.d ∈ F := by
    by_contra hdF
    have hz : p.basepoint.1 s.d = 0 := by
      rw [geometricVertex_weighted_sum_coordinate F a p.basepoint.1 hap s.d]
      simp [hdF]
    linarith

  have heF : s.e ∈ F := by
    by_contra heF
    have hz : p.basepoint.1 s.e = 0 := by
      rw [geometricVertex_weighted_sum_coordinate F a p.basepoint.1 hap s.e]
      simp [heF]
    linarith

  have hlabel0Tau : label i0 j0 ∈ tau.verts :=
    List.mem_toFinset.mp (hFtau hlabel0F)
  have hdTau : s.d ∈ tau.verts :=
    List.mem_toFinset.mp (hFtau hdF)
  have heTau : s.e ∈ tau.verts :=
    List.mem_toFinset.mp (hFtau heF)

  have htarget :=
    hcore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
      s hsRealized hanchorThree htau hdTau heTau

  have hclass :
      (SameTetVertices tau s.targetTet₀ ∧
          s.a ∈ tau.verts ∧ s.b ∈ tau.verts) ∨
        (SameTetVertices tau s.targetTet₁ ∧
          s.a ∈ tau.verts ∧ s.c ∈ tau.verts) ∨
        (SameTetVertices tau s.targetTet₂ ∧
          s.b ∈ tau.verts ∧ s.c ∈ tau.verts) := by
    rcases htarget with h0 | h1 | h2
    · have ha : s.a ∈ tau.verts := by
        apply (h0 s.a).2
        simp [Move32Site.targetTet₀, Tet.verts]
      have hb : s.b ∈ tau.verts := by
        apply (h0 s.b).2
        simp [Move32Site.targetTet₀, Tet.verts]
      exact Or.inl ⟨h0, ha, hb⟩
    · have ha : s.a ∈ tau.verts := by
        apply (h1 s.a).2
        simp [Move32Site.targetTet₁, Tet.verts]
      have hc : s.c ∈ tau.verts := by
        apply (h1 s.c).2
        simp [Move32Site.targetTet₁, Tet.verts]
      exact Or.inr (Or.inl ⟨h1, ha, hc⟩)
    · have hb : s.b ∈ tau.verts := by
        apply (h2 s.b).2
        simp [Move32Site.targetTet₂, Tet.verts]
      have hc : s.c ∈ tau.verts := by
        apply (h2 s.c).2
        simp [Move32Site.targetTet₂, Tet.verts]
      exact Or.inr (Or.inr ⟨h2, hb, hc⟩)

  have hj : (j0 : Nat) + 1 = (j1 : Nat) := by
    rfl

  obtain ⟨z, hz0, hz1⟩ :=
    (squareGridCell_neighbor_overlap_probe D hD).2 i0 j0 j1 hj

  obtain ⟨rho, hrho, hlabel0Rho, hlabel1Rho⟩ :=
    carrier_two_positive_coordinates_common_tet_probe
      (H.homotopy z)
      (hpositive i0 j0 z hz0)
      (hpositive i0 j1 z hz1)

  refine ⟨tau, htau, ?_, ?_, ?_⟩
  · simpa [i0, j0] using hlabel0Tau
  · simpa [s] using hclass
  · by_cases hcancel : label i0 j1 ∈ tau.verts
    · left
      simpa [i0, j1] using hcancel
    · right
      refine ⟨rho, hrho, ?_, ?_, ?_⟩
      · intro hrhoEq
        subst rho
        exact hcancel hlabel1Rho
      · simpa [i0, j0] using hlabel0Rho
      · simpa [i0, j1] using hlabel1Rho

end CarrierLoopNullHomotopyData
end Poincare
