import Poincare.GlobalMove32CarrierPairRepresented
import Poincare.Move32IndividualSourceNoDegreeFour

namespace Poincare

/-- A legal `2 → 3` move relative to a realized `3 → 2` carrier has an
honest represented tetrahedron containing the shared face and an endpoint
outside the five-label carrier. -/
theorem Move23Site.exists_represented_neighbor_containing_outside_endpoint
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hrealized : s.RealizedIn K) (hlegal : m.LegalIn K) :
    (∃ tau ∈ K.tets,
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts ∧ m.c ∈ tau.verts ∧
        m.d ∈ tau.verts ∧
        m.d ∉ [s.a, s.b, s.c, s.d, s.e]) ∨
      (∃ tau ∈ K.tets,
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts ∧ m.c ∈ tau.verts ∧
        m.e ∈ tau.verts ∧
        m.e ∉ [s.a, s.b, s.c, s.d, s.e]) := by
  rcases hlegal.1 with ⟨⟨tau, htau, hleft⟩, ⟨rho, hrho, hright⟩⟩
  rcases m.legalIn_implies_endpoint_outside_move32_carrier
      s hrealized hlegal with hd | he
  · left
    refine ⟨tau, htau, ?_, ?_, ?_, ?_, hd⟩
    · exact (hleft m.a).2 (by simp [Move23Site.leftTet, Tet.verts])
    · exact (hleft m.b).2 (by simp [Move23Site.leftTet, Tet.verts])
    · exact (hleft m.c).2 (by simp [Move23Site.leftTet, Tet.verts])
    · exact (hleft m.d).2 (by simp [Move23Site.leftTet, Tet.verts])
  · right
    refine ⟨rho, hrho, ?_, ?_, ?_, ?_, he⟩
    · exact (hright m.a).2 (by simp [Move23Site.rightTet, Tet.verts])
    · exact (hright m.b).2 (by simp [Move23Site.rightTet, Tet.verts])
    · exact (hright m.c).2 (by simp [Move23Site.rightTet, Tet.verts])
    · exact (hright m.e).2 (by simp [Move23Site.rightTet, Tet.verts])

/-- If both endpoints of the escaping edge lie outside a realized Move32
carrier, the five carrier labels followed by those endpoints are seven
distinct labels. -/
theorem Move23Site.seven_labels_nodup_of_both_endpoints_outside_move32_carrier
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hrealized : s.RealizedIn K)
    (hd : m.d ∉ [s.a, s.b, s.c, s.d, s.e])
    (he : m.e ∉ [s.a, s.b, s.c, s.d, s.e]) :
    [s.a, s.b, s.c, s.d, s.e, m.d, m.e].Nodup := by
  have hs := hcore.move32Site_distinct s hrealized
  have hm := m.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false] at hs hm ⊢
  aesop

end Poincare
