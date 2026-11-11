import Poincare.PositionalStellarPhiCost
import Poincare.Move32CombinatorialFoundation

namespace Poincare

/-- The four candidate 3→2 sites supported on the newly introduced
center-to-old-vertex spokes of a 1→4 stellar subdivision. -/
def Move41Site.spoke32AtA (s : Move41Site) : Move32Site :=
  ⟨s.b, s.c, s.d, s.a, s.e⟩

def Move41Site.spoke32AtB (s : Move41Site) : Move32Site :=
  ⟨s.a, s.c, s.d, s.b, s.e⟩

def Move41Site.spoke32AtC (s : Move41Site) : Move32Site :=
  ⟨s.a, s.b, s.d, s.c, s.e⟩

def Move41Site.spoke32AtD (s : Move41Site) : Move32Site :=
  ⟨s.a, s.b, s.c, s.d, s.e⟩

private theorem Move32Site.not_legal_of_sourceFace_present
    (m : Move32Site) (K : Triangulation) (τ : Tet)
    (hτ : τ ∈ K.tets)
    (hface : m.a ∈ τ.verts ∧ m.b ∈ τ.verts ∧ m.c ∈ τ.verts) :
    ¬ m.LegalIn K := by
  intro hlegal
  exact hlegal.2.2 τ hτ hface

/-- Every one of the four newly inserted spokes is blocked from immediate
legal 3→2 removal: its complementary outer face is already represented
in the opposite stellar tetrahedron. This holds independently of closed-core
or freshness assumptions, for every ordered-list insertion position. -/
theorem Move41Site.insertFreshAt_all_four_spokes_not_legal32
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hfresh : s.e ∉ vertexSupport K) :
    ¬ (s.spoke32AtA).LegalIn (s.insertFreshAt K before after hsource hfresh) ∧
    ¬ (s.spoke32AtB).LegalIn (s.insertFreshAt K before after hsource hfresh) ∧
    ¬ (s.spoke32AtC).LegalIn (s.insertFreshAt K before after hsource hfresh) ∧
    ¬ (s.spoke32AtD).LegalIn (s.insertFreshAt K before after hsource hfresh) := by
  have hmem (τ : Tet) (hτ : τ ∈ s.sourceTets) :
      τ ∈ (s.insertFreshAt K before after hsource hfresh).tets := by
    change τ ∈ before ++ s.sourceTets ++ after
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hτ)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Move32Site.not_legal_of_sourceFace_present
      (s.spoke32AtA) _ s.sourceTet₃
      (hmem s.sourceTet₃ (by simp [Move41Site.sourceTets]))
    simp [Move41Site.spoke32AtA, Move41Site.sourceTet₃,
      Tet.verts]
  · apply Move32Site.not_legal_of_sourceFace_present
      (s.spoke32AtB) _ s.sourceTet₂
      (hmem s.sourceTet₂ (by simp [Move41Site.sourceTets]))
    simp [Move41Site.spoke32AtB, Move41Site.sourceTet₂,
      Tet.verts]
  · apply Move32Site.not_legal_of_sourceFace_present
      (s.spoke32AtC) _ s.sourceTet₁
      (hmem s.sourceTet₁ (by simp [Move41Site.sourceTets]))
    simp [Move41Site.spoke32AtC, Move41Site.sourceTet₁,
      Tet.verts]
  · apply Move32Site.not_legal_of_sourceFace_present
      (s.spoke32AtD) _ s.sourceTet₀
      (hmem s.sourceTet₀ (by simp [Move41Site.sourceTets]))
    simp [Move41Site.spoke32AtD, Move41Site.sourceTet₀,
      Tet.verts]

end Poincare
