import Poincare.StellarSlideSecondLegal

namespace Poincare

/-- Exact ordered list after the canonical stellar slide. The second 3→2
step removes precisely the three tetrahedra incident to the old opposite
vertex and inserts the two new source tetrahedra. -/
theorem Move41Site.slideSecond32_replace_canonical
    (s : Move41Site) (f : Nat) (rest : List Tet)
    (hfive : [s.a, s.b, s.c, s.e, f].Nodup)
    (hf : f ∉ [s.a, s.b, s.c, s.d, s.e]) :
    ((s.slideSecond32).replace
      ((s.slideFirst23 f hfive).replace
        (s.headStellar ((⟨s.a, s.b, s.c, f⟩ : Tet) :: rest)))).tets =
      [⟨s.a, s.b, s.c, s.d⟩,
       ⟨s.a, s.b, s.c, s.e⟩,
       ⟨s.a, s.b, s.e, f⟩,
       ⟨s.a, s.c, s.e, f⟩,
       ⟨s.b, s.c, s.e, f⟩] ++ rest := by
  rw [show ((s.slideFirst23 f hfive).replace
    (s.headStellar ((⟨s.a, s.b, s.c, f⟩ : Tet) :: rest))).tets =
      [⟨s.a, s.b, s.e, f⟩,
       ⟨s.a, s.c, s.e, f⟩,
       ⟨s.b, s.c, s.e, f⟩,
       ⟨s.a, s.b, s.d, s.e⟩,
       ⟨s.a, s.c, s.d, s.e⟩,
       ⟨s.b, s.c, s.d, s.e⟩] ++ rest from
        s.slideFirst23_replace_canonical f rest hfive hf]
  have hd := s.distinct
  have hm := hfive
  have hff := hf
  simp at hd hm hff
  simp_all [Move32Site.replace, Move32Site.unchangedTets,
    Move41Site.slideSecond32, eraseFirstSameTet, sameTetVerticesBool,
    Move32Site.sourceTet₀, Move32Site.sourceTet₁,
    Move32Site.targetTet₀, Move32Site.targetTet₁, Move32Site.targetTet₂,
    Tet.verts]

end Poincare
