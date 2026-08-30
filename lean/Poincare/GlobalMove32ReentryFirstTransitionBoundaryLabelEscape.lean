import Poincare.GlobalMove32ReentryPolygonalFirstTransitionFresh
import Poincare.GlobalMove32ReentryDyadicGridVertices

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
At the dyadic refinement already used by the first-nonzero filling argument,
the exact endpoint of the first witnessed-reentry transition lies on a genuine
left-boundary grid cell.  The positive-coordinate label of that cell cannot be
any of the five vertices of the recurrent anchor Move32 carrier.

This converts the geometric freshness certificate into a finite combinatorial
escape witness.  It does not yet select a least escape index or assert a
non-cancelling ear.
-/
theorem finite_squareGrid_first_transition_boundary_label_outside_anchorCarrier_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (N : Nat) (hN : 0 < N) :
    let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
    let D := N * 2 ^ (m + 1)
    ∀ (hD : 0 < D)
      (label : Fin D → Fin D → Nat),
      (∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) →
      ∃ j : Fin D,
        (squareGridParameter D hD j.castSucc : ℝ) =
          1 / (2 : ℝ) ^ (m - 1) ∧
        label ⟨0, hD⟩ j ∉
          [(p.crossing.sites p.crossing.anchorIndex).a,
            (p.crossing.sites p.crossing.anchorIndex).b,
            (p.crossing.sites p.crossing.anchorIndex).c,
            (p.crossing.sites p.crossing.anchorIndex).d,
            (p.crossing.sites p.crossing.anchorIndex).e] := by
  dsimp only

  let s : Move32Site := p.crossing.sites p.crossing.anchorIndex
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)

  intro hD label hpositive

  have hm2 : 2 ≤ m := by
    dsimp [m]
    have hg := p.crossing.gap
    omega

  have hk : m - 1 ≤ m + 1 := by
    omega

  have hsub : (m + 1) - (m - 1) = 2 := by
    omega

  have hpowlt : 2 ^ ((m + 1) - (m - 1)) < 2 ^ (m + 1) := by
    apply Nat.pow_lt_pow_right
    · omega
    · omega

  have hjLt :
      N * 2 ^ ((m + 1) - (m - 1)) < D := by
    dsimp [D]
    exact Nat.mul_lt_mul_of_pos_left hpowlt hN

  let j : Fin D :=
    ⟨N * 2 ^ ((m + 1) - (m - 1)), hjLt⟩

  have hjParam :
      (squareGridParameter D hD j.castSucc : ℝ) =
        1 / (2 : ℝ) ^ (m - 1) := by
    have hgrid :=
      orderedTransition_dyadic_breakpoint_on_refined_grid_probe
        N (m + 1) (m - 1) hN hk
    change
      (((N * 2 ^ ((m + 1) - (m - 1)) : Nat) : ℝ) /
          ((N * 2 ^ (m + 1) : Nat) : ℝ)) =
        1 / (2 : ℝ) ^ (m - 1)
    simpa using hgrid

  obtain ⟨u, hu, _hloop, hzero⟩ :=
    p.first_transition_dyadic_anchorCarrier_coordinates_zero_of_no_degree_four
      hcore hlinks hNoFour

  let i0 : Fin D := ⟨0, hD⟩
  let z : unitInterval × unitInterval :=
    squareGridCellSource D hD i0 j

  have hzCell : z ∈ squareGridCell D hD i0 j := by
    exact squareGridCellSource_mem_probe D hD i0 j

  have hzFirst : z.1 = (0 : unitInterval) := by
    apply Subtype.ext
    dsimp [z, squareGridCellSource, i0, squareGridParameter]
    simp

  have hzSecond : z.2 = u := by
    apply Subtype.ext
    change
      (squareGridParameter D hD j.castSucc : ℝ) = (u : ℝ)
    rw [hjParam, hu]

  have hz : z = ((0 : unitInterval), u) := by
    apply Prod.ext
    · exact hzFirst
    · exact hzSecond

  have hlabelPositive :
      0 < (p.polygonalLoop u).1 (label i0 j) := by
    have h := hpositive i0 j z hzCell
    rw [hz, H.loop_boundary] at h
    exact h

  have hlabelOutside :
      label i0 j ∉ [s.a, s.b, s.c, s.d, s.e] := by
    intro hmem
    have hcoord : (p.polygonalLoop u).1 (label i0 j) = 0 := by
      exact hzero (label i0 j) (by simpa [s, i0] using hmem)
    linarith

  refine ⟨j, hjParam, ?_⟩
  simpa [s, i0] using hlabelOutside

end CarrierLoopNullHomotopyData
end Poincare
