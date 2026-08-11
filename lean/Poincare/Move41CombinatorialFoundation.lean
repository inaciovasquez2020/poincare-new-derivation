import Poincare.Validity

namespace Poincare

/-- The combinatorial data of a genuine `4 → 1` bistellar move.  The vertex
`e` is the center of the four source tetrahedra. -/
structure Move41Site where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  distinct : [a, b, c, d, e].Nodup

def Move41Site.sourceTet₀ (s : Move41Site) : Tet := ⟨s.a, s.b, s.c, s.e⟩
def Move41Site.sourceTet₁ (s : Move41Site) : Tet := ⟨s.a, s.b, s.d, s.e⟩
def Move41Site.sourceTet₂ (s : Move41Site) : Tet := ⟨s.a, s.c, s.d, s.e⟩
def Move41Site.sourceTet₃ (s : Move41Site) : Tet := ⟨s.b, s.c, s.d, s.e⟩
def Move41Site.targetTet (s : Move41Site) : Tet := ⟨s.a, s.b, s.c, s.d⟩

def Move41Site.sourceTets (s : Move41Site) : List Tet :=
  [s.sourceTet₀, s.sourceTet₁, s.sourceTet₂, s.sourceTet₃]

/-- Exact local bistellar data.  `closedCore` supplies every face-incidence
condition, while the remaining fields identify the saturated center star and
exclude the target tetrahedron. -/
structure Move41Site.LegalIn (s : Move41Site) (K : Triangulation) : Prop where
  closedCore : ClosedTriangulationCore K
  sourceOccursExactlyOnce :
    ∀ source ∈ s.sourceTets,
      (K.tets.filter (fun τ => sameTetVerticesBool τ source)).length = 1
  sourcePairwiseDistinct :
    s.sourceTets.Pairwise (fun τ σ => ¬ SameTetVertices τ σ)
  centerSaturated :
    ∀ τ ∈ K.tets, s.e ∈ τ.verts →
      ∃ source ∈ s.sourceTets, SameTetVertices τ source
  targetAbsent :
    ∀ τ ∈ K.tets, ¬ SameTetVertices τ s.targetTet

/-- In a legal `4 → 1` move, the tetrahedra incident to the center are
exactly the four declared source tetrahedra, up to vertex ordering. -/
theorem Move41Site.mem_source_iff_of_center_mem
    {s : Move41Site} {K : Triangulation} (h : s.LegalIn K) {τ : Tet}
    (hτ : τ ∈ K.tets) :
    s.e ∈ τ.verts ↔ ∃ source ∈ s.sourceTets, SameTetVertices τ source := by
  constructor
  · exact h.centerSaturated τ hτ
  · rintro ⟨source, hsource, hsame⟩
    have heSource : s.e ∈ source.verts := by
      simp [Move41Site.sourceTets] at hsource
      rcases hsource with rfl | rfl | rfl | rfl <;>
        simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
          Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]
    exact (hsame s.e).2 heSource

end Poincare
