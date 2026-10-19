import Poincare.GlobalMove32SourceFaceAllSourceEdgesHigh
import Mathlib.Tactic

namespace Poincare

/--
A represented source-face obstruction is incompatible with the fail-closed
exclusion of every nonself high-incidence edge other than the Move32 shared
edge.  The all-source-edges-high theorem gives incidence at least four on
edge a-b; realized-site distinctness makes a-b nonself and different from d-e.
-/
theorem move32_sourceFace_obstruction_false_of_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hsourceFace :
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts)
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
                   y ∈ gamma.verts))).length) :
    False := by
  classical
  obtain ⟨theta, htheta, haTheta, hbTheta, hcTheta⟩ := hsourceFace
  have habHigh :=
    hcore.move32_all_sourceEdges_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
      hlinks hNoFour s hrealized hsourceFace
  have hfive := hcore.move32Site_distinct s hrealized
  have hab : s.a ≠ s.b := by
    intro habEq
    simp [habEq] at hfive
  have hnonself :
      ¬ ((s.a = s.d ∧ s.b = s.e) ∨
         (s.a = s.e ∧ s.b = s.d)) := by
    intro h
    rcases h with hde | hed
    · rcases hde with ⟨had, hbe⟩
      simp_all
    · rcases hed with ⟨hae, hbd⟩
      simp_all
  have hhighDecide :
      4 ≤
        (K.tets.filter
          (fun gamma =>
            decide
              (s.a ∈ gamma.verts ∧
               s.b ∈ gamma.verts))).length := by
    simpa only [decide_eq_true_eq] using habHigh.1
  exact
    (hNoHigh s hrealized hsourceFace)
      ⟨s.a, s.b, theta, hab, htheta, haTheta, hbTheta,
        hnonself, hhighDecide⟩

end Poincare
