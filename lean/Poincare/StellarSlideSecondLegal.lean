import Poincare.StellarSlideSecondEdge

namespace Poincare

/-- The second move of the local stellar slide is an actual legal 3→2
site. Every component of legality is established from the explicit
intermediate list and the original closed-core and freshness assumptions. -/
theorem Move41Site.slideSecond32_legal
    (s : Move41Site) (f : Nat) (rest : List Tet)
    (hfive : [s.a, s.b, s.c, s.e, f].Nodup)
    (hf : f ∉ [s.a, s.b, s.c, s.d, s.e])
    (hcore : ClosedTriangulationCore
      ({ tets := s.targetTet :: (⟨s.a, s.b, s.c, f⟩ : Tet) :: rest } :
        Triangulation))
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    (s.slideSecond32).LegalIn
      ((s.slideFirst23 f hfive).replace
        (s.headStellar ((⟨s.a, s.b, s.c, f⟩ : Tet) :: rest))) := by
  let K := (s.slideFirst23 f hfive).replace
    (s.headStellar ((⟨s.a, s.b, s.c, f⟩ : Tet) :: rest))
  have hcanon := s.slideFirst23_replace_canonical f rest hfive hf
  have hreal : (s.slideSecond32).RealizedIn K := by
    change
      (∃ τ ∈ K.tets, SameTetVertices τ (⟨s.a, s.b, s.d, s.e⟩ : Tet)) ∧
      (∃ τ ∈ K.tets, SameTetVertices τ (⟨s.a, s.c, s.d, s.e⟩ : Tet)) ∧
      (∃ τ ∈ K.tets, SameTetVertices τ (⟨s.b, s.c, s.d, s.e⟩ : Tet))
    refine ⟨⟨_, ?_, fun _ => Iff.rfl⟩,
      ⟨_, ?_, fun _ => Iff.rfl⟩,
      ⟨_, ?_, fun _ => Iff.rfl⟩⟩
    all_goals
      rw [show K.tets = _ from hcanon]
      simp
  exact ⟨hreal,
    s.slideSecond32_sharedEdgeExactlyThree f rest hfive hf hfresh,
    s.slideSecond32_sourceFaceAbsent f rest hfive hf hcore⟩

end Poincare
