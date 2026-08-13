import Poincare.Move41FourSourceConnectedLinkDegree
import Poincare.Move32CombinatorialFoundation

namespace Poincare

theorem ClosedTriangulationCore.move32_sourceTet0_represented_vertexDegree_d_eq_four_of_connectedLink
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hsource0 : ∃ tau ∈ K.tets, SameTetVertices tau s.sourceTet₀)
    (hconnected : VertexLinkConnected K s.d) :
    vertexDegree K s.d = 4 := by
  have hfive := hcore.move32Site_distinct s hrealized
  let m : Move41Site :=
    { a := s.a, b := s.b, c := s.c, d := s.e, e := s.d, distinct := by
        simp at hfive ⊢
        aesop }
  rcases hsource0 with ⟨tau₀, htau₀K, htau₀⟩
  rcases hrealized with ⟨⟨tau₁, htau₁K, htau₁⟩,
    ⟨tau₂, htau₂K, htau₂⟩, ⟨tau₃, htau₃K, htau₃⟩⟩
  apply hcore.move41Site_center_vertexDegree_eq_four_of_represented_sources_connectedLink
    m htau₀K (by
      simpa [m, Move41Site.sourceTet₀, Move32Site.sourceTet₀, Tet.verts] using htau₀)
    htau₁K (by
      intro x
      rw [htau₁ x]
      simp [m, Move41Site.sourceTet₁, Move32Site.targetTet₀, Tet.verts]
      aesop)
    htau₂K (by
      intro x
      rw [htau₂ x]
      simp [m, Move41Site.sourceTet₂, Move32Site.targetTet₁, Tet.verts]
      aesop)
    htau₃K (by
      intro x
      rw [htau₃ x]
      simp [m, Move41Site.sourceTet₃, Move32Site.targetTet₂, Tet.verts]
      aesop)
  simpa [m] using hconnected

theorem ClosedTriangulationCore.move32_sourceTet1_represented_vertexDegree_e_eq_four_of_connectedLink
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hsource1 : ∃ tau ∈ K.tets, SameTetVertices tau s.sourceTet₁)
    (hconnected : VertexLinkConnected K s.e) :
    vertexDegree K s.e = 4 := by
  have hfive := hcore.move32Site_distinct s hrealized
  let m : Move41Site :=
    { a := s.a, b := s.b, c := s.c, d := s.d, e := s.e, distinct := hfive }
  rcases hsource1 with ⟨tau₀, htau₀K, htau₀⟩
  rcases hrealized with ⟨⟨tau₁, htau₁K, htau₁⟩,
    ⟨tau₂, htau₂K, htau₂⟩, ⟨tau₃, htau₃K, htau₃⟩⟩
  apply hcore.move41Site_center_vertexDegree_eq_four_of_represented_sources_connectedLink
    m htau₀K (by
      simpa [m, Move41Site.sourceTet₀, Move32Site.sourceTet₁, Tet.verts] using htau₀)
    htau₁K (by
      simpa [m, Move41Site.sourceTet₁, Move32Site.targetTet₀, Tet.verts] using htau₁)
    htau₂K (by
      simpa [m, Move41Site.sourceTet₂, Move32Site.targetTet₁, Tet.verts] using htau₂)
    htau₃K (by
      simpa [m, Move41Site.sourceTet₃, Move32Site.targetTet₂, Tet.verts] using htau₃)
  simpa [m] using hconnected

end Poincare
