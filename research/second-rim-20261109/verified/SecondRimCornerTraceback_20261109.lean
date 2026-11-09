import Poincare.Triangulation

/-!
  Standalone proof candidate in the genuine repository Tet/Triangulation types.
  No import from Moves, geometry or topology. The support relation is
  definitionally identical to Poincare.SameTetVertices, but the latter is not
  imported. No second Move32Site legality is assumed.

  STATUS: NOT_RUN until compiled on the user's Mac at pinned revision.
-/

namespace Poincare
namespace SecondRimCornerTraceback

def SameTetSupport (τ σ : Tet) : Prop :=
  ∀ v : Nat, v ∈ τ.verts ↔ v ∈ σ.verts

/-- Recover an order-invariant target tetrahedron from the retained portion
of a list replacement, given a vertex absent from every inserted tetrahedron. -/
theorem retained_witness_one_step
    (K' : Triangulation) (inserted retained : List Tet)
    (target : Tet) (marker : Nat)
    (hK' : K'.tets = inserted ++ retained)
    (hmarker : marker ∈ target.verts)
    (havoids : ∀ τ ∈ inserted, marker ∉ τ.verts)
    (hwitness : ∃ τ ∈ K'.tets, SameTetSupport τ target) :
    ∃ τ ∈ retained, SameTetSupport τ target := by
  obtain ⟨τ, hτ, hsame⟩ := hwitness
  have hmarkτ : marker ∈ τ.verts := (hsame marker).2 hmarker
  rw [hK'] at hτ
  rcases List.mem_append.mp hτ with hnew | hret
  · exact ((havoids τ hnew) hmarkτ).elim
  · exact ⟨τ, hret, hsame⟩

/-- Two-stage survivor: the first marker rules out the original 2-to-3
insertions, while the second marker rules out the first 3-to-2 insertions.
The actual eraseFirstSameTet definitions supply the retention maps later. -/
theorem retained_witness_two_steps
    (K K₂ : Triangulation)
    (new23 new32 R23 R32 : List Tet)
    (target : Tet) (marker23 marker32 : Nat)
    (hPrefix : K₂.tets = new32 ++ R32)
    (hRet32 : ∀ τ ∈ R32, τ ∈ new23 ++ R23)
    (hRet23 : ∀ τ ∈ R23, τ ∈ K.tets)
    (hmarker23 : marker23 ∈ target.verts)
    (hmarker32 : marker32 ∈ target.verts)
    (hNoNew23 : ∀ τ ∈ new23, marker23 ∉ τ.verts)
    (hNoNew32 : ∀ τ ∈ new32, marker32 ∉ τ.verts)
    (hwitness : ∃ τ ∈ K₂.tets, SameTetSupport τ target) :
    ∃ τ ∈ K.tets, SameTetSupport τ target := by
  obtain ⟨τ, hτ, hsame⟩ := hwitness
  have h23 : marker23 ∈ τ.verts := (hsame marker23).2 hmarker23
  have h32 : marker32 ∈ τ.verts := (hsame marker32).2 hmarker32
  rw [hPrefix] at hτ
  rcases List.mem_append.mp hτ with hnew32 | hret32
  · exact ((hNoNew32 τ hnew32) h32).elim
  have hprev : τ ∈ new23 ++ R23 := hRet32 τ hret32
  rcases List.mem_append.mp hprev with hnew23 | hret23
  · exact ((hNoNew23 τ hnew23) h23).elim
  · exact ⟨τ, hRet23 τ hret23, hsame⟩

/-- The first candidate's external corner {a,b,d,z} is in the original K,
not among the three 2-to-3 insertions, provided z is fresh. -/
theorem first_corner_original
    (K K₁ : Triangulation) (R23 : List Tet)
    (a b c d e z : Nat)
    (hPrefix : K₁.tets =
      [(⟨a,b,d,e⟩ : Tet), (⟨a,c,d,e⟩ : Tet), (⟨b,c,d,e⟩ : Tet)] ++ R23)
    (hRet23 : ∀ τ ∈ R23, τ ∈ K.tets)
    (hzFresh : z ∉ [a,b,c,d,e])
    (hwitness : ∃ τ ∈ K₁.tets,
       SameTetSupport τ (⟨a,b,d,z⟩ : Tet)) :
    ∃ τ ∈ K.tets, SameTetSupport τ (⟨a,b,d,z⟩ : Tet) := by
  have hza : z ≠ a := by intro h; exact hzFresh (by simp [h])
  have hzb : z ≠ b := by intro h; exact hzFresh (by simp [h])
  have hzc : z ≠ c := by intro h; exact hzFresh (by simp [h])
  have hzd : z ≠ d := by intro h; exact hzFresh (by simp [h])
  have hze : z ≠ e := by intro h; exact hzFresh (by simp [h])
  have hNoNew : ∀ τ ∈
       [(⟨a,b,d,e⟩ : Tet), (⟨a,c,d,e⟩ : Tet), (⟨b,c,d,e⟩ : Tet)],
       z ∉ τ.verts := by
    intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl | rfl
    · simp [Tet.verts, hza, hzb, hzd, hze]
    · simp [Tet.verts, hza, hzc, hzd, hze]
    · simp [Tet.verts, hzb, hzc, hzd, hze]
  obtain ⟨τ, hτ, hsame⟩ :=
    retained_witness_one_step K₁
      [(⟨a,b,d,e⟩ : Tet), (⟨a,c,d,e⟩ : Tet), (⟨b,c,d,e⟩ : Tet)]
      R23 (⟨a,b,d,z⟩ : Tet) z hPrefix
      (by simp [Tet.verts]) hNoNew hwitness
  exact ⟨τ, hRet23 τ hτ, hsame⟩

/-- The second candidate's external corner {a,c,d,y} is in original K.
No y != z condition is needed. The only first-move-side conditions are that
c is absent from the two freshly inserted 3-to-2 source tetrahedra. -/
theorem second_corner_original
    (K K₂ : Triangulation) (R23 R32 : List Tet)
    (a b c d e z y : Nat)
    (hPrefix : K₂.tets =
      [(⟨d,e,z,a⟩ : Tet), (⟨d,e,z,b⟩ : Tet)] ++ R32)
    (hRet32 : ∀ τ ∈ R32,
      τ ∈ [(⟨a,b,d,e⟩ : Tet), (⟨a,c,d,e⟩ : Tet), (⟨b,c,d,e⟩ : Tet)] ++ R23)
    (hRet23 : ∀ τ ∈ R23, τ ∈ K.tets)
    (hNoC₀ : c ∉ (⟨d,e,z,a⟩ : Tet).verts)
    (hNoC₁ : c ∉ (⟨d,e,z,b⟩ : Tet).verts)
    (hyFresh : y ∉ [a,b,c,d,e])
    (hwitness : ∃ τ ∈ K₂.tets,
      SameTetSupport τ (⟨a,c,d,y⟩ : Tet)) :
    ∃ τ ∈ K.tets, SameTetSupport τ (⟨a,c,d,y⟩ : Tet) := by
  have hya : y ≠ a := by intro h; exact hyFresh (by simp [h])
  have hyb : y ≠ b := by intro h; exact hyFresh (by simp [h])
  have hyc : y ≠ c := by intro h; exact hyFresh (by simp [h])
  have hyd : y ≠ d := by intro h; exact hyFresh (by simp [h])
  have hye : y ≠ e := by intro h; exact hyFresh (by simp [h])
  have hNoNew23 : ∀ τ ∈
       [(⟨a,b,d,e⟩ : Tet), (⟨a,c,d,e⟩ : Tet), (⟨b,c,d,e⟩ : Tet)],
       y ∉ τ.verts := by
    intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl | rfl
    · simp [Tet.verts, hya, hyb, hyd, hye]
    · simp [Tet.verts, hya, hyc, hyd, hye]
    · simp [Tet.verts, hyb, hyc, hyd, hye]
  have hNoNew32 : ∀ τ ∈
       [(⟨d,e,z,a⟩ : Tet), (⟨d,e,z,b⟩ : Tet)],
       c ∉ τ.verts := by
    intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl
    · exact hNoC₀
    · exact hNoC₁
  exact retained_witness_two_steps K K₂
    [(⟨a,b,d,e⟩ : Tet), (⟨a,c,d,e⟩ : Tet), (⟨b,c,d,e⟩ : Tet)]
    [(⟨d,e,z,a⟩ : Tet), (⟨d,e,z,b⟩ : Tet)]
    R23 R32 (⟨a,c,d,y⟩ : Tet) y c hPrefix hRet32 hRet23
    (by simp [Tet.verts]) (by simp [Tet.verts])
    hNoNew23 hNoNew32 hwitness

end SecondRimCornerTraceback
end Poincare

#check Poincare.SecondRimCornerTraceback.retained_witness_one_step
#check Poincare.SecondRimCornerTraceback.retained_witness_two_steps
#check Poincare.SecondRimCornerTraceback.first_corner_original
#check Poincare.SecondRimCornerTraceback.second_corner_original
#print axioms Poincare.SecondRimCornerTraceback.retained_witness_one_step
#print axioms Poincare.SecondRimCornerTraceback.retained_witness_two_steps
#print axioms Poincare.SecondRimCornerTraceback.first_corner_original
#print axioms Poincare.SecondRimCornerTraceback.second_corner_original