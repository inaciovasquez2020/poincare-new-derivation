import Poincare.VertexLink

namespace Poincare

/--
A tetrahedron incident to a represented vertex contributes its opposite
triangle to that vertex link.  The other three vertices are retained as
link vertices.  This is an occurrence-level statement: it does not claim
that the displayed triangle exhausts the full vertex link.
-/
theorem exists_link_triangle_with_other_vertices_of_tet_mem
    {K : Triangulation}
    (v p q r : Nat)
    (τ : Tet)
    (hτ : τ ∈ K.tets)
    (hv : v ∈ τ.verts)
    (hp : p ∈ τ.verts)
    (hq : q ∈ τ.verts)
    (hr : r ∈ τ.verts)
    (hpv : p ≠ v)
    (hqv : q ≠ v)
    (hrv : r ≠ v) :
    ∃ σ : LinkTriangle,
      σ ∈ vertexLinkTriangles K v ∧
      p ∈ σ.verts ∧
      q ∈ σ.verts ∧
      r ∈ σ.verts := by
  obtain ⟨σ, hσ, hExtract⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
      K v τ hτ hv
  refine ⟨σ, hσ, ?_, ?_, ?_⟩
  · exact (τ.mem_linkTriangleAt?_iff v p σ hExtract hpv).2 hp
  · exact (τ.mem_linkTriangleAt?_iff v q σ hExtract hqv).2 hq
  · exact (τ.mem_linkTriangleAt?_iff v r σ hExtract hrv).2 hr

/--
The two tetrahedra incident to an obstructing face supply two link-triangle
occurrences at each of its vertices.  Only the specified occurrences are
asserted; other triangles in these vertex links are unrestricted.
-/
theorem obstructing_face_two_link_contributions
    {K : Triangulation}
    (a b c x y : Nat)
    (τ ρ : Tet)
    (hτ : τ ∈ K.tets)
    (hρ : ρ ∈ K.tets)
    (haτ : a ∈ τ.verts)
    (hbτ : b ∈ τ.verts)
    (hcτ : c ∈ τ.verts)
    (hxτ : x ∈ τ.verts)
    (haρ : a ∈ ρ.verts)
    (hbρ : b ∈ ρ.verts)
    (hcρ : c ∈ ρ.verts)
    (hyρ : y ∈ ρ.verts)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hax : a ≠ x)
    (hay : a ≠ y)
    (hbc : b ≠ c)
    (hbx : b ≠ x)
    (hby : b ≠ y)
    (hcx : c ≠ x)
    (hcy : c ≠ y) :
    (∃ σx : LinkTriangle,
      σx ∈ vertexLinkTriangles K a ∧
      b ∈ σx.verts ∧ c ∈ σx.verts ∧ x ∈ σx.verts) ∧
    (∃ σy : LinkTriangle,
      σy ∈ vertexLinkTriangles K a ∧
      b ∈ σy.verts ∧ c ∈ σy.verts ∧ y ∈ σy.verts) ∧
    (∃ τx : LinkTriangle,
      τx ∈ vertexLinkTriangles K b ∧
      a ∈ τx.verts ∧ c ∈ τx.verts ∧ x ∈ τx.verts) ∧
    (∃ τy : LinkTriangle,
      τy ∈ vertexLinkTriangles K b ∧
      a ∈ τy.verts ∧ c ∈ τy.verts ∧ y ∈ τy.verts) ∧
    (∃ υx : LinkTriangle,
      υx ∈ vertexLinkTriangles K c ∧
      a ∈ υx.verts ∧ b ∈ υx.verts ∧ x ∈ υx.verts) ∧
    (∃ υy : LinkTriangle,
      υy ∈ vertexLinkTriangles K c ∧
      a ∈ υy.verts ∧ b ∈ υy.verts ∧ y ∈ υy.verts) := by
  constructor
  · exact exists_link_triangle_with_other_vertices_of_tet_mem
      a b c x τ hτ haτ hbτ hcτ hxτ hab.symm hac.symm hax.symm
  constructor
  · exact exists_link_triangle_with_other_vertices_of_tet_mem
      a b c y ρ hρ haρ hbρ hcρ hyρ hab.symm hac.symm hay.symm
  constructor
  · exact exists_link_triangle_with_other_vertices_of_tet_mem
      b a c x τ hτ hbτ haτ hcτ hxτ hab hbc.symm hbx.symm
  constructor
  · exact exists_link_triangle_with_other_vertices_of_tet_mem
      b a c y ρ hρ hbρ haρ hcρ hyρ hab hbc.symm hby.symm
  constructor
  · exact exists_link_triangle_with_other_vertices_of_tet_mem
      c a b x τ hτ hcτ haτ hbτ hxτ hac hbc hcx.symm
  · exact exists_link_triangle_with_other_vertices_of_tet_mem
      c a b y ρ hρ hcρ haρ hbρ hyρ hac hbc hcy.symm

end Poincare
