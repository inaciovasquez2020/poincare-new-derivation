import Poincare.StellarSlideEndpoint

namespace Poincare

/-- A local stellar vertex slide across an adjacent face is realized by
two certified Pachner moves. The full original closed core and freshness
hypotheses are explicit; this theorem does not establish a universal
global descent or the Poincaré conjecture. -/
theorem Move41Site.stellarSlide_twoMove_certified
    (s : Move41Site) (f : Nat) (rest : List Tet)
    (hfive : [s.a, s.b, s.c, s.e, f].Nodup)
    (hf : f ∉ [s.a, s.b, s.c, s.d, s.e])
    (hcore : ClosedTriangulationCore
      ({ tets := s.targetTet :: (⟨s.a, s.b, s.c, f⟩ : Tet) :: rest } :
        Triangulation))
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    PermutationCertifiedPachnerPath
      (s.headStellar ((⟨s.a, s.b, s.c, f⟩ : Tet) :: rest))
      ({ tets := [⟨s.a, s.b, s.c, s.d⟩,
                  ⟨s.a, s.b, s.c, s.e⟩,
                  ⟨s.a, s.b, s.e, f⟩,
                  ⟨s.a, s.c, s.e, f⟩,
                  ⟨s.b, s.c, s.e, f⟩] ++ rest } : Triangulation) := by
  let neighbor : Tet := ⟨s.a, s.b, s.c, f⟩
  let K := s.headStellar (neighbor :: rest)
  let m23 := s.slideFirst23 f hfive
  let m32 := s.slideSecond32
  have hfresh' : ∀ τ ∈ neighbor :: rest, s.e ∉ τ.verts := by
    intro τ hτ
    rcases List.mem_cons.mp hτ with rfl | hr
    · have hn := hfive
      simp [neighbor, Tet.verts] at hn ⊢
      aesop
    · exact hfresh τ hr
  have hfirst : m23.LegalIn K := by
    exact s.slideFirst23_legal (neighbor :: rest) f hfive hf
      hcore hfresh' (by simp [neighbor])
  have hstar : ClosedTriangulationCore K := by
    exact s.headStellar_closedCore (neighbor :: rest) hcore hfresh'
  have hsecond : m32.LegalIn (m23.replace K) := by
    exact s.slideSecond32_legal f rest hfive hf hcore hfresh
  have hperm :
      (m32.replace (m23.replace K)).tets.Perm
        ([⟨s.a, s.b, s.c, s.d⟩,
          ⟨s.a, s.b, s.c, s.e⟩,
          ⟨s.a, s.b, s.e, f⟩,
          ⟨s.a, s.c, s.e, f⟩,
          ⟨s.b, s.c, s.e, f⟩] ++ rest) := by
    rw [show (m32.replace (m23.replace K)).tets =
      [⟨s.a, s.b, s.c, s.d⟩,
       ⟨s.a, s.b, s.c, s.e⟩,
       ⟨s.a, s.b, s.e, f⟩,
       ⟨s.a, s.c, s.e, f⟩,
       ⟨s.b, s.c, s.e, f⟩] ++ rest from
        s.slideSecond32_replace_canonical f rest hfive hf]
  exact permutationCertifiedTwoMovePath_of_legal23_legal32
    K _ hstar m23 hfirst m32 hsecond hperm

end Poincare
