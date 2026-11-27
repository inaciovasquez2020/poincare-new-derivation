import Poincare.StellarSlideFirstLegal

namespace Poincare

/-- Exact ordered tetrahedron list after the first 2→3 step in a
canonical adjacent stellar star. The exterior list is arbitrary. This
is a combinatorial identity, not a legality or closed-core claim. -/
theorem Move41Site.slideFirst23_replace_canonical
    (s : Move41Site) (f : Nat) (rest : List Tet)
    (hfive : [s.a, s.b, s.c, s.e, f].Nodup)
    (hf : f ∉ [s.a, s.b, s.c, s.d, s.e]) :
    ((s.slideFirst23 f hfive).replace
      (s.headStellar ((⟨s.a, s.b, s.c, f⟩ : Tet) :: rest))).tets =
      [⟨s.a, s.b, s.e, f⟩,
       ⟨s.a, s.c, s.e, f⟩,
       ⟨s.b, s.c, s.e, f⟩,
       ⟨s.a, s.b, s.d, s.e⟩,
       ⟨s.a, s.c, s.d, s.e⟩,
       ⟨s.b, s.c, s.d, s.e⟩] ++ rest := by
  have hs := s.distinct
  have hm := hfive
  simp at hs hm
  simp_all [Move23Site.replace, Move23Site.unchangedTets,
    Move41Site.slideFirst23, Move41Site.headStellar,
    eraseFirstSameTet, sameTetVerticesBool, Tet.verts,
    Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂,
    Move41Site.sourceTet₀, Move41Site.sourceTet₁,
    Move41Site.sourceTet₂, Move41Site.sourceTet₃]

end Poincare
