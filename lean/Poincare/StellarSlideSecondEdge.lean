import Poincare.StellarSlideSecondSourceFace

namespace Poincare

/-- After the first 2→3 replacement, the new center and the original
opposite vertex belong together to exactly three tetrahedra. This
uses freshness in the exterior and the exact first-replacement list. -/
theorem Move41Site.slideSecond32_sharedEdgeExactlyThree
    (s : Move41Site) (f : Nat) (rest : List Tet)
    (hfive : [s.a, s.b, s.c, s.e, f].Nodup)
    (hf : f ∉ [s.a, s.b, s.c, s.d, s.e])
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    (s.slideSecond32).SharedEdgeExactlyThree
      ((s.slideFirst23 f hfive).replace
        (s.headStellar ((⟨s.a, s.b, s.c, f⟩ : Tet) :: rest))) := by
  let p : Tet → Bool := fun τ => decide (s.d ∈ τ.verts ∧ s.e ∈ τ.verts)
  have hrest : rest.filter p = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro τ hτ hp
    have hpair : s.d ∈ τ.verts ∧ s.e ∈ τ.verts :=
      of_decide_eq_true hp
    exact (hfresh τ hτ) hpair.2
  have hlocal :
      (([⟨s.a, s.b, s.e, f⟩,
        ⟨s.a, s.c, s.e, f⟩,
        ⟨s.b, s.c, s.e, f⟩,
        ⟨s.a, s.b, s.d, s.e⟩,
        ⟨s.a, s.c, s.d, s.e⟩,
        ⟨s.b, s.c, s.d, s.e⟩] : List Tet).filter p).length = 3 := by
    have hd := s.distinct
    have hm := hfive
    have hff := hf
    simp at hd hm hff
    simp [p, Tet.verts] <;> aesop
  change (((s.slideFirst23 f hfive).replace
      (s.headStellar ((⟨s.a, s.b, s.c, f⟩ : Tet) :: rest))).tets.filter p).length = 3
  rw [s.slideFirst23_replace_canonical f rest hfive hf,
    List.filter_append, List.length_append, hrest, hlocal]
  rfl

end Poincare
