import Poincare.GlobalMove32SourceFaceAllSourceEdgesHigh
import Poincare.GlobalMove32SupportedEdgeState
import Mathlib.Tactic

namespace Poincare

/-- An obstructed realized `Move32Site` in the no-degree-four branch has a
high source-face edge whose canonical unordered-edge key differs from any
prescribed distinct old edge.

Only two of the three certified high source edges are needed: `a-b` and
`a-c` have different canonical keys because the realized site has five
distinct vertices.  Hence at least one avoids the prescribed old key. -/
theorem
    ClosedTriangulationCore.exists_high_sourceEdge_away_from_edge_of_move32_sourceFace_obstruction_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hobstruction :
      ∃ theta ∈ K.tets,
        s.a ∈ theta.verts ∧
        s.b ∈ theta.verts ∧
        s.c ∈ theta.verts)
    (v x : Nat)
    (hvx : v ≠ x) :
    ∃ p q theta,
      p ≠ q ∧
      theta ∈ K.tets ∧
      p ∈ theta.verts ∧
      q ∈ theta.verts ∧
      canonicalEdgeKey p q ≠ canonicalEdgeKey v x ∧
      4 ≤
        (K.tets.filter
          (fun gamma =>
            p ∈ gamma.verts ∧
            q ∈ gamma.verts)).length := by
  classical

  have hfive :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hrealized

  have hab : s.a ≠ s.b := by
    have h := hfive
    simp at h
    aesop

  have hac : s.a ≠ s.c := by
    have h := hfive
    simp at h
    aesop

  have hbc : s.b ≠ s.c := by
    have h := hfive
    simp at h
    aesop

  have hab_ne_hac :
      canonicalEdgeKey s.a s.b ≠
        canonicalEdgeKey s.a s.c := by
    intro hkey
    rcases
        (canonicalEdgeKey_eq_iff
          s.a s.b s.a s.c hab hac).1 hkey with
      hdirect | hreverse
    · exact hbc hdirect.2
    · exact hab hreverse.2.symm

  obtain ⟨theta, htheta, haTheta, hbTheta, hcTheta⟩ := hobstruction

  have hhigh :=
    hcore.move32_all_sourceEdges_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
      hlinks hNoFour s hrealized
      ⟨theta, htheta, haTheta, hbTheta, hcTheta⟩

  by_cases habOld :
      canonicalEdgeKey s.a s.b = canonicalEdgeKey v x

  · refine
      ⟨s.a, s.c, theta,
        hac,
        htheta,
        haTheta,
        hcTheta,
        ?_,
        hhigh.2.1⟩
    intro hacOld
    apply hab_ne_hac
    exact habOld.trans hacOld.symm

  · exact
      ⟨s.a, s.b, theta,
        hab,
        htheta,
        haTheta,
        hbTheta,
        habOld,
        hhigh.1⟩

end Poincare
