import Poincare.GlobalMove32ReentryLeastBoundaryEscapeIncidenceSplit

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
Under the fail-closed high-incidence exclusion, the least left-boundary escape
edge cannot have tetrahedron incidence at least four.  Its escaping endpoint is
outside all five anchor vertices, so the edge is automatically distinct from
the anchor shared edge `d-e`.  Therefore the general closed-core incidence
split collapses to exact incidence three.

This closes only the high-incidence half of the least-boundary first-exit
split.  It does not yet classify the remaining exact-incidence-three edge as a
Move32 source obstruction, legal Move23, descent, or witnessed reentry.
-/
theorem finite_squareGrid_least_boundary_escape_edge_incidence_eq_three_of_noHigh_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ x y sigma,
          x ≠ y ∧
          sigma ∈ K.tets ∧
          x ∈ sigma.verts ∧
          y ∈ sigma.verts ∧
          ¬ ((x = s.d ∧ y = s.e) ∨
             (x = s.e ∧ y = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (x ∈ gamma.verts ∧
                   y ∈ gamma.verts))).length)
    (N : Nat) (hN : 0 < N) :
    let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
    let D := N * 2 ^ (m + 1)
    ∀ (hD : 0 < D)
      (label : Fin D → Fin D → Nat),
      (∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) →
      ∃ j k : Fin D, ∃ rho : Tet,
        0 < (j : Nat) ∧
        (k : Nat) + 1 = (j : Nat) ∧
        label ⟨0, hD⟩ k ∈
          [(p.crossing.sites p.crossing.anchorIndex).a,
            (p.crossing.sites p.crossing.anchorIndex).b,
            (p.crossing.sites p.crossing.anchorIndex).c,
            (p.crossing.sites p.crossing.anchorIndex).d,
            (p.crossing.sites p.crossing.anchorIndex).e] ∧
        label ⟨0, hD⟩ j ∉
          [(p.crossing.sites p.crossing.anchorIndex).a,
            (p.crossing.sites p.crossing.anchorIndex).b,
            (p.crossing.sites p.crossing.anchorIndex).c,
            (p.crossing.sites p.crossing.anchorIndex).d,
            (p.crossing.sites p.crossing.anchorIndex).e] ∧
        rho ∈ K.tets ∧
        label ⟨0, hD⟩ k ∈ rho.verts ∧
        label ⟨0, hD⟩ j ∈ rho.verts ∧
        ¬ SameTetVertices rho
            (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∧
        ¬ SameTetVertices rho
            (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
        ¬ SameTetVertices rho
            (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
        (K.tets.filter
          (fun tau =>
            label ⟨0, hD⟩ k ∈ tau.verts ∧
            label ⟨0, hD⟩ j ∈ tau.verts)).length = 3 := by
  classical
  dsimp only

  let s : Move32Site := p.crossing.sites p.crossing.anchorIndex
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨j, k, rho, hjPos, hkSucc, hkInside, hjOutside,
      hrho, hkRho, hjRho, hnot0, hnot1, hnot2, hinc⟩ :=
    finite_squareGrid_least_boundary_escape_edge_incidenceSplit_probe
      hcore hlinks hNoFour p H N hN hD label hpositive

  let i0 : Fin D := ⟨0, hD⟩
  let v : Nat := label i0 k
  let x : Nat := label i0 j

  have hkInside' : v ∈ [s.a, s.b, s.c, s.d, s.e] := by
    simpa [v, i0, s] using hkInside

  have hjOutside' : x ∉ [s.a, s.b, s.c, s.d, s.e] := by
    simpa [x, i0, s] using hjOutside

  have hvx : v ≠ x := by
    intro hvxEq
    apply hjOutside'
    rw [← hvxEq]
    exact hkInside'

  have hsRealized : s.RealizedIn K := by
    simpa [s] using p.realized p.crossing.anchorIndex

  have hsource :
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts := by
    simpa [s] using p.anchor_sourceFace_obstruction

  have hnonself :
      ¬ ((v = s.d ∧ x = s.e) ∨
         (v = s.e ∧ x = s.d)) := by
    intro hself
    apply hjOutside'
    rcases hself with hde | hed
    · rw [hde.2]
      simp
    · rw [hed.2]
      simp

  have hkRho' : v ∈ rho.verts := by
    simpa [v, i0] using hkRho

  have hjRho' : x ∈ rho.verts := by
    simpa [x, i0] using hjRho

  have hthree :
      (K.tets.filter
        (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length = 3 := by
    rcases hinc with hthree | hhigh
    · simpa [v, x, i0] using hthree
    · exfalso
      have hhighDecide :
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide (v ∈ gamma.verts ∧ x ∈ gamma.verts))).length := by
        simpa [v, x, i0] using hhigh
      exact
        (hNoHigh s hsRealized hsource)
          ⟨v, x, rho, hvx, hrho, hkRho', hjRho', hnonself, hhighDecide⟩

  refine ⟨j, k, rho, hjPos, hkSucc, hkInside, hjOutside,
    hrho, hkRho, hjRho, hnot0, hnot1, hnot2, ?_⟩
  simpa [v, x, i0] using hthree

end CarrierLoopNullHomotopyData
end Poincare
