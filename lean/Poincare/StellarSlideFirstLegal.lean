import Poincare.StellarSlideCertifiedPath

namespace Poincare

/-- The first 2-to-3 site for moving a fresh stellar vertex across the
face (a,b,c) from tetrahedron (a,b,c,d) to (a,b,c,f). -/
def Move41Site.slideFirst23 (s : Move41Site) (f : Nat)
    (hfive : [s.a, s.b, s.c, s.e, f].Nodup) : Move23Site :=
  { a := s.a, b := s.b, c := s.c, d := s.e, e := f, distinct := hfive }

/-- Freshness excludes the new edge between the stellar center and the
opposite vertex of the neighboring tetrahedron. -/
theorem Move41Site.slideFirst23_newEdgeAbsent
    (s : Move41Site) (rest : List Tet) (f : Nat)
    (hfive : [s.a, s.b, s.c, s.e, f].Nodup)
    (hf : f ∉ [s.a, s.b, s.c, s.d, s.e])
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    (s.slideFirst23 f hfive).NewEdgeAbsent (s.headStellar rest) := by
  intro τ hτ hpair
  have hx : s.e ∈ τ.verts := hpair.1
  have hft : f ∈ τ.verts := hpair.2
  obtain ⟨ρ, hρ, hsame⟩ :=
    s.headStellar_center_saturated rest hfresh τ hτ hx
  have hfo : f ∉ ρ.verts := by
    simp only [Move41Site.sourceTets, List.mem_cons,
      List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl <;>
      simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
        Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]
  exact hfo ((hsame f).1 hft)

/-- The first slide step is actually legal in the closed-core stellar
subdivision; its shared face has exactly two incident tetrahedra. -/
theorem Move41Site.slideFirst23_legal
    (s : Move41Site) (rest : List Tet) (f : Nat)
    (hfive : [s.a, s.b, s.c, s.e, f].Nodup)
    (hf : f ∉ [s.a, s.b, s.c, s.d, s.e])
    (hcore : ClosedTriangulationCore
      ({ tets := s.targetTet :: rest } : Triangulation))
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts)
    (hneighbor : (⟨s.a, s.b, s.c, f⟩ : Tet) ∈ rest) :
    (s.slideFirst23 f hfive).LegalIn (s.headStellar rest) := by
  let m := s.slideFirst23 f hfive
  have hfirst : m.leftTet = s.sourceTet₀ := rfl
  have hsecond : m.rightTet = (⟨s.a, s.b, s.c, f⟩ : Tet) := rfl
  have hmemfirst : s.sourceTet₀ ∈ (s.headStellar rest).tets := by
    simp [Move41Site.headStellar]
  have hmemsecond :
      (⟨s.a, s.b, s.c, f⟩ : Tet) ∈ (s.headStellar rest).tets := by
    simp [Move41Site.headStellar, hneighbor]
  have hcore' := s.headStellar_closedCore rest hcore hfresh
  have habc : [s.a, s.b, s.c].Nodup := by
    have hd := s.distinct
    simp at hd ⊢
    aesop
  have hface :
      m.SharedFaceExactlyTwo (s.headStellar rest) := by
    change ((s.headStellar rest).tets.filter
      (fun τ => s.a ∈ τ.verts ∧ s.b ∈ τ.verts ∧ s.c ∈ τ.verts)).length = 2
    exact hcore'.2.2 s.a s.b s.c habc
      ⟨s.sourceTet₀, hmemfirst, by simp [Move41Site.sourceTet₀, Tet.verts]⟩
  refine ⟨?_, hface, s.slideFirst23_newEdgeAbsent rest f hfive hf hfresh⟩
  exact ⟨⟨s.sourceTet₀, hmemfirst, by rw [hfirst]; exact fun _ => Iff.rfl⟩,
    ⟨⟨s.a, s.b, s.c, f⟩, hmemsecond,
      by rw [hsecond]; exact fun _ => Iff.rfl⟩⟩

end Poincare
