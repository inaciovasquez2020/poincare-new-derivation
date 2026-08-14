import Poincare.Move32CombinatorialFoundation

namespace Poincare

/-- Every two distinct labels in the five-vertex carrier of a realized
`3 → 2` site already occur together in a tetrahedron of the triangulation. -/
theorem Move32Site.exists_represented_pair_of_realized_of_mem_carrier
    {K : Triangulation} (s : Move32Site) (hrealized : s.RealizedIn K)
    {x y : Nat}
    (hx : x ∈ [s.a, s.b, s.c, s.d, s.e])
    (hy : y ∈ [s.a, s.b, s.c, s.d, s.e]) :
    ∃ tau ∈ K.tets, x ∈ tau.verts ∧ y ∈ tau.verts := by
  rcases hrealized with
    ⟨⟨tau0, htau0, hsame0⟩, ⟨tau1, htau1, hsame1⟩,
      ⟨tau2, htau2, hsame2⟩⟩
  have h0a : s.a ∈ tau0.verts :=
    (hsame0 s.a).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  have h0b : s.b ∈ tau0.verts :=
    (hsame0 s.b).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  have h0d : s.d ∈ tau0.verts :=
    (hsame0 s.d).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  have h0e : s.e ∈ tau0.verts :=
    (hsame0 s.e).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  have h1a : s.a ∈ tau1.verts :=
    (hsame1 s.a).2 (by simp [Move32Site.targetTet₁, Tet.verts])
  have h1c : s.c ∈ tau1.verts :=
    (hsame1 s.c).2 (by simp [Move32Site.targetTet₁, Tet.verts])
  have h1d : s.d ∈ tau1.verts :=
    (hsame1 s.d).2 (by simp [Move32Site.targetTet₁, Tet.verts])
  have h1e : s.e ∈ tau1.verts :=
    (hsame1 s.e).2 (by simp [Move32Site.targetTet₁, Tet.verts])
  have h2b : s.b ∈ tau2.verts :=
    (hsame2 s.b).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  have h2c : s.c ∈ tau2.verts :=
    (hsame2 s.c).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  have h2d : s.d ∈ tau2.verts :=
    (hsame2 s.d).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  have h2e : s.e ∈ tau2.verts :=
    (hsame2 s.e).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl
  all_goals aesop

/-- A legal `2 → 3` move cannot propose a new edge wholly inside the
five-label carrier of an already realized `3 → 2` site. -/
theorem Move23Site.not_newEdgeAbsent_of_endpoints_mem_move32_carrier
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hd : m.d ∈ [s.a, s.b, s.c, s.d, s.e])
    (he : m.e ∈ [s.a, s.b, s.c, s.d, s.e]) :
    ¬ m.NewEdgeAbsent K := by
  intro habsent
  obtain ⟨tau, htau, hdTau, heTau⟩ :=
    s.exists_represented_pair_of_realized_of_mem_carrier
      hrealized hd he
  exact habsent tau htau ⟨hdTau, heTau⟩

/-- Consequently, a `2 → 3` candidate whose new edge is absent must
genuinely escape the five-label carrier of every realized `3 → 2` site at
one of its endpoints.  This is the exact finite case split left after the
internal-carrier candidates have been eliminated. -/
theorem Move23Site.newEdgeAbsent_implies_endpoint_outside_move32_carrier
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hrealized : s.RealizedIn K) (habsent : m.NewEdgeAbsent K) :
    m.d ∉ [s.a, s.b, s.c, s.d, s.e] ∨
      m.e ∉ [s.a, s.b, s.c, s.d, s.e] := by
  by_cases hd : m.d ∈ [s.a, s.b, s.c, s.d, s.e]
  · right
    intro he
    exact m.not_newEdgeAbsent_of_endpoints_mem_move32_carrier
      s hrealized hd he habsent
  · exact Or.inl hd

/-- Legal `2 → 3` sites satisfy the same honest carrier-escape split. -/
theorem Move23Site.legalIn_implies_endpoint_outside_move32_carrier
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hrealized : s.RealizedIn K) (hlegal : m.LegalIn K) :
    m.d ∉ [s.a, s.b, s.c, s.d, s.e] ∨
      m.e ∉ [s.a, s.b, s.c, s.d, s.e] := by
  exact m.newEdgeAbsent_implies_endpoint_outside_move32_carrier
    s hrealized hlegal.2.2

end Poincare
