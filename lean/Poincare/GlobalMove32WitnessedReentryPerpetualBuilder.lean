import Poincare.GlobalMove32WitnessedSourceFaceReentry

namespace Poincare

/-- Fail-closed continuation for witnessed source-face reentry.

If, at every realized source-face-obstructed Move32 site, the other outputs of
the certified one-step classification are excluded (matching legal Move23,
strict topological `PhiSupport` descent, and a nonself complementary edge of
incidence at least four), then any realized exact-three obstructed starting
site extends to a perpetual sequence of witnessed source-face reentries.

This theorem does not prove any of those excluded outcomes impossible. -/
theorem ClosedTriangulationCore.exists_perpetual_witnessedReentry_of_no_other_sourceFace_outcome
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
    (hNoMove23 :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ m : Move23Site,
          m.a = s.a ∧
          m.b = s.b ∧
          m.c = s.c ∧
          m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
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
    (start : Move32Site)
    (hstartRealized : start.RealizedIn K)
    (hstartThree : start.SharedEdgeExactlyThree K)
    (hstartObstruction :
      ∃ tau ∈ K.tets,
        start.a ∈ tau.verts ∧
        start.b ∈ tau.verts ∧
        start.c ∈ tau.verts) :
    ∃ sites : Nat → Move32Site,
      sites 0 = start ∧
      (∀ n, (sites n).RealizedIn K) ∧
      (∀ n, (sites n).SharedEdgeExactlyThree K) ∧
      (∀ n, ∃ tau ∈ K.tets,
        (sites n).a ∈ tau.verts ∧
        (sites n).b ∈ tau.verts ∧
        (sites n).c ∈ tau.verts) ∧
      ∀ n,
        Move32SourceFaceWitnessedReentry
          K (sites n) (sites (n + 1)) := by
  classical

  let Good : Move32Site → Prop := fun s =>
    s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts

  have hstartGood : Good start := by
    exact ⟨hstartRealized, hstartThree, hstartObstruction⟩

  have hnext :
      ∀ q : {s : Move32Site // Good s},
        ∃ q' : {s : Move32Site // Good s},
          Move32SourceFaceWitnessedReentry K q.1 q'.1 := by
    intro q
    have hq := q.property
    change q.1.RealizedIn K ∧
      q.1.SharedEdgeExactlyThree K ∧
      (∃ tau ∈ K.tets,
        q.1.a ∈ tau.verts ∧
        q.1.b ∈ tau.verts ∧
        q.1.c ∈ tau.verts) at hq

    rcases
        hcore.exists_legal_move23_or_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
          hlinks hconn hNoFour q.1 hq.1 hq.2.2 with
      hmove23 | hdesc | hhigh | hreentry

    · exact (hNoMove23 q.1 hq.1 hq.2.2 hmove23).elim
    · exact (hNoDescent hdesc).elim
    · exact (hNoHigh q.1 hq.1 hq.2.2 hhigh).elim
    · rcases hreentry with ⟨s', hrel⟩
      have hplain := hrel.toSourceFaceReentry
      refine ⟨⟨s', ?_⟩, hrel⟩
      change s'.RealizedIn K ∧
        s'.SharedEdgeExactlyThree K ∧
        ∃ tau ∈ K.tets,
          s'.a ∈ tau.verts ∧
          s'.b ∈ tau.verts ∧
          s'.c ∈ tau.verts
      exact ⟨hplain.1, hplain.2.1, hplain.2.2.1⟩

  let step :
      {s : Move32Site // Good s} →
        {s : Move32Site // Good s} :=
    fun q => Classical.choose (hnext q)

  have hstep :
      ∀ q : {s : Move32Site // Good s},
        Move32SourceFaceWitnessedReentry K q.1 (step q).1 := by
    intro q
    exact Classical.choose_spec (hnext q)

  let q0 : {s : Move32Site // Good s} :=
    ⟨start, hstartGood⟩

  let seq : Nat → {s : Move32Site // Good s} :=
    fun n => Nat.rec q0 (fun _ q => step q) n

  refine ⟨fun n => (seq n).1, ?_, ?_, ?_, ?_, ?_⟩

  · simp [seq, q0]

  · intro n
    have hg := (seq n).property
    change (seq n).1.RealizedIn K ∧
      (seq n).1.SharedEdgeExactlyThree K ∧
      (∃ tau ∈ K.tets,
        (seq n).1.a ∈ tau.verts ∧
        (seq n).1.b ∈ tau.verts ∧
        (seq n).1.c ∈ tau.verts) at hg
    exact hg.1

  · intro n
    have hg := (seq n).property
    change (seq n).1.RealizedIn K ∧
      (seq n).1.SharedEdgeExactlyThree K ∧
      (∃ tau ∈ K.tets,
        (seq n).1.a ∈ tau.verts ∧
        (seq n).1.b ∈ tau.verts ∧
        (seq n).1.c ∈ tau.verts) at hg
    exact hg.2.1

  · intro n
    have hg := (seq n).property
    change (seq n).1.RealizedIn K ∧
      (seq n).1.SharedEdgeExactlyThree K ∧
      (∃ tau ∈ K.tets,
        (seq n).1.a ∈ tau.verts ∧
        (seq n).1.b ∈ tau.verts ∧
        (seq n).1.c ∈ tau.verts) at hg
    exact hg.2.2

  · intro n
    change Move32SourceFaceWitnessedReentry
      K (seq n).1 (seq (n + 1)).1
    have hr := hstep (seq n)
    simpa [seq] using hr

end Poincare
