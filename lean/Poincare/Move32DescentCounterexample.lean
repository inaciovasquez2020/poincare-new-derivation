import Poincare.Move32DegreeSupportBalance
import Poincare.VertexLinkConnectednessCounterexample

namespace Poincare

theorem twoBoundaryVertexWedge_PhiSupport_pos :
    0 < PhiSupport twoBoundaryVertexWedge := by native_decide

set_option maxHeartbeats 800000 in
private theorem twoBoundaryVertexWedge_eq_zero_of_degree_ge_five
    {v : Nat} (hv : 5 ≤ vertexDegree twoBoundaryVertexWedge v) : v = 0 := by
  have hcount : 0 < vertexDegree twoBoundaryVertexWedge v := by omega
  have hmem : v ∈ allVerts twoBoundaryVertexWedge :=
    List.count_pos_iff.mp (by simpa [vertexDegree] using hcount)
  simp [allVerts, twoBoundaryVertexWedge, Tet.verts,
    wedgeA0, wedgeA1, wedgeA2, wedgeA3, wedgeA4,
    wedgeB0, wedgeB1, wedgeB2, wedgeB3, wedgeB4] at hmem
  have hvle : v ≤ 8 := by omega
  interval_cases v
  all_goals try rfl
  all_goals norm_num [vertexDegree, allVerts, twoBoundaryVertexWedge, Tet.verts,
    wedgeA0, wedgeA1, wedgeA2, wedgeA3, wedgeA4,
    wedgeB0, wedgeB1, wedgeB2, wedgeB3, wedgeB4] at hv

theorem twoBoundaryVertexWedge_no_strict_move32 :
    ¬ ∃ s : Move32Site, s.LegalIn twoBoundaryVertexWedge ∧
      PhiSupport (s.replace twoBoundaryVertexWedge) < PhiSupport twoBoundaryVertexWedge := by
  rintro ⟨s, hlegal, hlt⟩
  have hc := (twoBoundaryVertexWedge_closedCore.move32Site_replace_PhiSupport_lt_iff
    s hlegal).1 hlt
  have hd : s.d = 0 := twoBoundaryVertexWedge_eq_zero_of_degree_ge_five hc.1
  have he : s.e = 0 := twoBoundaryVertexWedge_eq_zero_of_degree_ge_five hc.2.1
  have hn := twoBoundaryVertexWedge_closedCore.move32Site_distinct s hlegal.1
  rw [hd, he] at hn
  simp at hn

theorem exists_closedCore_positive_PhiSupport_without_strict_move32 :
    ∃ K : Triangulation, ClosedTriangulationCore K ∧ 0 < PhiSupport K ∧
      ¬ ∃ s : Move32Site, s.LegalIn K ∧
        PhiSupport (s.replace K) < PhiSupport K := by
  exact ⟨twoBoundaryVertexWedge, twoBoundaryVertexWedge_closedCore,
    twoBoundaryVertexWedge_PhiSupport_pos, twoBoundaryVertexWedge_no_strict_move32⟩

end Poincare
