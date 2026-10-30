import Poincare.Move2332LocalEscapeCriterion
import Poincare.Move41DegreeSupportBalance

namespace Poincare

/-- For the canonical target-degree-four `PhiSupport`, every legal
2→3 move on a closed triangulation core increases the defect by exactly four.
In particular, a first `2→3` move cannot itself be a strict descent. -/
theorem ClosedTriangulationCore.move23_PhiSupport_eq_add_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (m : Move23Site) (hlegal : m.LegalIn K) :
    PhiSupport (m.replace K) = PhiSupport K + 4 := by
  obtain ⟨⟨tauD, hTauD, hDMatch⟩, ⟨tauE, hTauE, hEMatch⟩⟩ := hlegal.1
  have hdSupport : m.d ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tauD, hTauD, (hDMatch m.d).2 (by
      simp [Move23Site.leftTet, Tet.verts])⟩
  have heSupport : m.e ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tauE, hTauE, (hEMatch m.e).2 (by
      simp [Move23Site.rightTet, Tet.verts])⟩
  have hd0 : 4 ≤ vertexDegree K m.d :=
    hcore.vertexDegree_ge_four_of_mem_vertexSupport hdSupport
  have he0 : 4 ≤ vertexDegree K m.e :=
    hcore.vertexDegree_ge_four_of_mem_vertexSupport heSupport
  rcases m.replace_vertexDegree_site K hlegal with
    ⟨_, _, _, hd23, he23⟩
  have hdDef :
      vertexDefect (m.replace K) m.d = vertexDefect K m.d + 2 :=
    (vertexDefect_of_degree_add_two K (m.replace K) m.d hd23).2.2 hd0
  have heDef :
      vertexDefect (m.replace K) m.e = vertexDefect K m.e + 2 :=
    (vertexDefect_of_degree_add_two K (m.replace K) m.e he23).2.2 he0
  have hbalance := m.replace_PhiSupport_balance K hlegal
  omega

theorem crossPolytopeBoundary4_no_strict_move23 :
    ¬ ∃ m : Move23Site,
      m.LegalIn crossPolytopeBoundary4 ∧
      PhiSupport (m.replace crossPolytopeBoundary4) <
        PhiSupport crossPolytopeBoundary4 := by
  rintro ⟨m, hlegal, hlt⟩
  have hplus :=
    crossPolytopeBoundary4_closedCore.move23_PhiSupport_eq_add_four m hlegal
  omega

theorem crossPolytopeBoundary4_no_legal_move41 :
    ¬ ∃ s : Move41Site, s.LegalIn crossPolytopeBoundary4 := by
  rintro ⟨s, hlegal⟩
  have hfour :=
    crossPolytopeBoundary4_closedCore.move41Site_center_vertexDegree_eq_four
      s hlegal
  have hpos : 0 < vertexDegree crossPolytopeBoundary4 s.e := by
    omega
  have hsupport : s.e ∈ vertexSupport crossPolytopeBoundary4 := by
    rw [mem_vertexSupport_iff]
    change s.e ∈ allVerts crossPolytopeBoundary4
    change 0 < (allVerts crossPolytopeBoundary4).count s.e at hpos
    simpa using hpos
  have hv : s.e < 8 := by
    rw [crossPolytopeBoundary4_vertexSupport] at hsupport
    simp at hsupport
    omega
  have height :=
    crossPolytopeBoundary4_vertexDegree s.e hv
  omega

/-- A strictly decreasing single step cannot be a legal 2→3, 3→2, or
4→1 move on the cross-polytope boundary. The repository currently has
no canonical legal Move14Site interface, so the 1→4 case is excluded from
this precise formal statement, not silently assumed. -/
theorem crossPolytopeBoundary4_no_strict_represented_move23_move32_move41 :
    (¬ ∃ m : Move23Site,
      m.LegalIn crossPolytopeBoundary4 ∧
      PhiSupport (m.replace crossPolytopeBoundary4) <
        PhiSupport crossPolytopeBoundary4) ∧
    (¬ ∃ s : Move32Site,
      s.LegalIn crossPolytopeBoundary4 ∧
      PhiSupport (s.replace crossPolytopeBoundary4) <
        PhiSupport crossPolytopeBoundary4) ∧
    (¬ ∃ s : Move41Site, s.LegalIn crossPolytopeBoundary4) := by
  exact ⟨crossPolytopeBoundary4_no_strict_move23,
    crossPolytopeBoundary4_no_strict_move32,
    crossPolytopeBoundary4_no_legal_move41⟩

end Poincare
