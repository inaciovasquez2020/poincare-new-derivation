import Poincare.GlobalMove32ReentryFiniteRecurrence
import Poincare.GlobalMove32SourceFaceNonselfIncidenceSplit
import Poincare.GlobalMove32IncidenceThreeComposition

namespace Poincare

/--
A source-face reentry step retaining the actual complementary-edge geometry
from which the next incidence-three Move32 site was constructed.

Unlike `Move32SourceFaceReentry`, this relation remembers the two represented
tetrahedra across the obstructing old source face, their complementary
vertices `x,y`, and a represented tetrahedron containing the new shared edge.

No termination or acyclicity statement is built into this relation.
-/
def Move32SourceFaceWitnessedReentry
    (K : Triangulation)
    (s s' : Move32Site) : Prop :=
  ∃ tau rho x y sigma,
    tau ∈ K.tets ∧
    rho ∈ K.tets ∧
    ¬ SameTetVertices tau rho ∧
    s.a ∈ tau.verts ∧
    s.b ∈ tau.verts ∧
    s.c ∈ tau.verts ∧
    s.a ∈ rho.verts ∧
    s.b ∈ rho.verts ∧
    s.c ∈ rho.verts ∧
    x ∈ tau.verts ∧
    x ∉ [s.a, s.b, s.c] ∧
    y ∈ rho.verts ∧
    y ∉ [s.a, s.b, s.c] ∧
    x ≠ y ∧
    sigma ∈ K.tets ∧
    x ∈ sigma.verts ∧
    y ∈ sigma.verts ∧
    ¬ (
      (x = s.d ∧ y = s.e) ∨
      (x = s.e ∧ y = s.d)
    ) ∧
    s'.d = x ∧
    s'.e = y ∧
    s'.RealizedIn K ∧
    s'.SharedEdgeExactlyThree K ∧
    ∃ gamma ∈ K.tets,
      s'.a ∈ gamma.verts ∧
      s'.b ∈ gamma.verts ∧
      s'.c ∈ gamma.verts

/--
A witnessed reentry step forgets to the previously certified source-face
reentry relation.
-/
theorem Move32SourceFaceWitnessedReentry.toSourceFaceReentry
    {K : Triangulation}
    {s s' : Move32Site}
    (h :
      Move32SourceFaceWitnessedReentry K s s') :
    Move32SourceFaceReentry K s s' := by

  rcases h with
    ⟨tau, rho, x, y, sigma,
      htauK,
      hrhoK,
      hne,
      haTau,
      hbTau,
      hcTau,
      haRho,
      hbRho,
      hcRho,
      hxTau,
      hxABC,
      hyRho,
      hyABC,
      hxy,
      hsigmaK,
      hxSigma,
      hySigma,
      hnonself,
      hsd,
      hse,
      hrealized',
      hthree',
      hobstruction'⟩

  refine
    ⟨hrealized',
      hthree',
      hobstruction',
      ?_⟩

  intro hself
  apply hnonself

  rcases hself with
    hdirect | hreverse

  · exact
      Or.inl
        ⟨hsd.symm.trans hdirect.1,
          hse.symm.trans hdirect.2⟩

  · exact
      Or.inr
        ⟨hsd.symm.trans hreverse.1,
          hse.symm.trans hreverse.2⟩

/--
The source-face obstruction admits the same four-way classification as before,
but the incidence-three reentry alternative now retains the complementary-edge
tetrahedral witnesses.

This theorem makes no claim that witnessed reentry terminates.
-/
theorem
    ClosedTriangulationCore.exists_legal_move23_or_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn :
      TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hobstruction :
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts) :
    (∃ m : Move23Site,
      m.a = s.a ∧
      m.b = s.b ∧
      m.c = s.c ∧
      m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∃ x y sigma,
      x ≠ y ∧
      sigma ∈ K.tets ∧
      x ∈ sigma.verts ∧
      y ∈ sigma.verts ∧
      ¬ (
        (x = s.d ∧ y = s.e) ∨
        (x = s.e ∧ y = s.d)
      ) ∧
      4 ≤
        (K.tets.filter
          (fun gamma =>
            decide
              (x ∈ gamma.verts ∧
               y ∈ gamma.verts))).length) ∨
    ∃ s' : Move32Site,
      Move32SourceFaceWitnessedReentry K s s' := by

  classical

  rcases
      hcore.exists_legal_move23_or_nonself_complementEdge_incidence_split_of_move32_sourceFace_obstruction
        hlinks
        hconn
        hNoFour
        s
        hrealized
        hobstruction with
    hmove23 | hedge

  · exact Or.inl hmove23

  · rcases hedge with
      ⟨tau, rho, x, y, sigma,
        htauK,
        hrhoK,
        hne,
        haTau,
        hbTau,
        hcTau,
        haRho,
        hbRho,
        hcRho,
        hxTau,
        hxABC,
        hyRho,
        hyABC,
        hxy,
        hsigmaK,
        hxSigma,
        hySigma,
        hnonself,
        hthree | hhigh⟩

    · rcases
          hcore.exists_descent_or_realized_sourceFace_obstruction_of_edgeIncidence_three
            hNoFour
            x
            y
            hxy
            hthree with
        hdesc | hreentry

      · exact
          Or.inr
            (Or.inl hdesc)

      · rcases hreentry with
          ⟨s',
            hsd,
            hse,
            hrealized',
            hthree',
            hobstruction'⟩

        exact
          Or.inr
            (Or.inr
              (Or.inr
                ⟨s',
                  tau,
                  rho,
                  x,
                  y,
                  sigma,
                  htauK,
                  hrhoK,
                  hne,
                  haTau,
                  hbTau,
                  hcTau,
                  haRho,
                  hbRho,
                  hcRho,
                  hxTau,
                  hxABC,
                  hyRho,
                  hyABC,
                  hxy,
                  hsigmaK,
                  hxSigma,
                  hySigma,
                  hnonself,
                  hsd,
                  hse,
                  hrealized',
                  hthree',
                  hobstruction'⟩))

    · exact
        Or.inr
          (Or.inr
            (Or.inl
              ⟨x,
                y,
                sigma,
                hxy,
                hsigmaK,
                hxSigma,
                hySigma,
                hnonself,
                hhigh⟩))

end Poincare
