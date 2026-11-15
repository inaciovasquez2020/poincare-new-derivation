import Mathlib

/-!
A pure finite mod-two dual-adjacency certificate, independent of Poincare.
Proof scope: algebraic nonboundary in the two-incident-facets model.
It does NOT construct the incidence map for an actual Triangulation and does
NOT prove that simple connectedness implies H₂ = 0.
Compilation status: NOT_RUN in the available environment.
-/

namespace Poincare
namespace DualPathParity

universe u v
variable {Face : Type u} {Tet : Type v}

/-- In a closed simplicial 3-manifold every triangular face has exactly
    two incident tetrahedra. This abstract map records their ordered pair. -/
def boundary3 (incident : Face → Tet × Tet)
    (B : Tet → Bool) (f : Face) : Bool :=
  (B (incident f).1).xor (B (incident f).2)

/-- A dual adjacency that does not cross a face in the prescribed 2-chain. -/
def Avoiding (incident : Face → Tet × Tet)
    (sphere : Face → Bool) (t u : Tet) : Prop :=
  ∃ f : Face,
    sphere f = false ∧
    (((incident f).1 = t ∧ (incident f).2 = u) ∨
      ((incident f).1 = u ∧ (incident f).2 = t))

private theorem xor_false_eq {x y : Bool} (h : x.xor y = false) : x = y := by
  cases x <;> cases y <;> simp_all

/-- Boundary coefficients agree along any dual path avoiding the 2-chain. -/
theorem equal_on_avoiding_path
    (incident : Face → Tet × Tet)
    (sphere : Face → Bool)
    (B : Tet → Bool)
    (hB : ∀ f, boundary3 incident B f = sphere f)
    {t u : Tet}
    (hpath : Relation.ReflTransGen (Avoiding incident sphere) t u) :
    B t = B u := by
  apply Relation.ReflTransGen.trans_induction_on
    (motive := fun {t u} _ => B t = B u) hpath
  · intro _
    rfl
  · intro a b hab
    obtain ⟨f, hzero, hforward | hreverse⟩ := hab
    · have hx : (B a).xor (B b) = false := by
        simpa [boundary3, hforward.1, hforward.2] using
          (hB f).trans hzero
      exact xor_false_eq hx
    · have hx : (B b).xor (B a) = false := by
        simpa [boundary3, hreverse.1, hreverse.2] using
          (hB f).trans hzero
      exact (xor_false_eq hx).symm
  · intro _ _ hleft hright
    exact hleft.trans hright

/-- A dual path avoiding the sphere cannot join two tetrahedra across a
    face belonging to the sphere if the sphere is a mod-two boundary. -/
theorem nonboundary_of_avoiding_return
    (incident : Face → Tet × Tet)
    (sphere : Face → Bool)
    {t u : Tet}
    (hpath : Relation.ReflTransGen (Avoiding incident sphere) t u)
    (f : Face)
    (hface : sphere f = true)
    (hends : incident f = (t, u)) :
    ¬ ∃ B : Tet → Bool, ∀ g, boundary3 incident B g = sphere g := by
  rintro ⟨B, hB⟩
  have heq : B t = B u := equal_on_avoiding_path incident sphere B hB hpath
  have hodd : (B t).xor (B u) = true := by
    simpa [boundary3, hends] using (hB f).trans hface
  rw [heq] at hodd
  cases hval : B u <;> simp [hval] at hodd

end DualPathParity
end Poincare