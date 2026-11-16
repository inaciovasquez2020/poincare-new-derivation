import Mathlib

namespace Poincare.DualPathParity

universe u v
variable {Face : Type u} {Tet : Type v}

def boundary3 (incident : Face → Tet × Tet)
    (B : Tet → Bool) (f : Face) : Bool :=
  (B (incident f).1).xor (B (incident f).2)

def Avoiding (incident : Face → Tet × Tet)
    (sphere : Face → Bool) (t u : Tet) : Prop :=
  ∃ f : Face, sphere f = false ∧
    (((incident f).1 = t ∧ (incident f).2 = u) ∨
      ((incident f).1 = u ∧ (incident f).2 = t))

private theorem xor_false_eq {x y : Bool} (h : x.xor y = false) : x = y := by
  cases x <;> cases y <;> simp_all

private theorem adjacent_equal
    (incident : Face → Tet × Tet)
    (sphere : Face → Bool)
    (B : Tet → Bool)
    (hB : ∀ f, boundary3 incident B f = sphere f)
    {t u : Tet} (h : Avoiding incident sphere t u) :
    B t = B u := by
  obtain ⟨f, hzero, hforward | hreverse⟩ := h
  · have hx : (B t).xor (B u) = false := by
      simpa [boundary3, hforward.1, hforward.2] using (hB f).trans hzero
    exact xor_false_eq hx
  · have hx : (B u).xor (B t) = false := by
      simpa [boundary3, hreverse.1, hreverse.2] using (hB f).trans hzero
    exact (xor_false_eq hx).symm

theorem equal_on_avoiding_path
    (incident : Face → Tet × Tet)
    (sphere : Face → Bool)
    (B : Tet → Bool)
    (hB : ∀ f, boundary3 incident B f = sphere f)
    {t u : Tet}
    (hpath : Relation.ReflTransGen (Avoiding incident sphere) t u) :
    B t = B u := by
  exact Relation.ReflTransGen.trans_induction_on
    (motive := fun {a b} _ => B a = B b)
    hpath
    (fun _ => rfl)
    (fun hab => adjacent_equal incident sphere B hB hab)
    (fun _ _ ih₁ ih₂ => ih₁.trans ih₂)

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
  have heq : B t = B u :=
    equal_on_avoiding_path incident sphere B hB hpath
  have hodd : (B t).xor (B u) = true := by
    simpa [boundary3, hends] using (hB f).trans hface
  rw [heq] at hodd
  cases hval : B u <;> simp [hval] at hodd

#print axioms equal_on_avoiding_path
#print axioms nonboundary_of_avoiding_return

end Poincare.DualPathParity
