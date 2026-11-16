import Mathlib

namespace Poincare.DualPotentialCandidate

universe u v
variable {Face : Type u} {Tet : Type v}

def Step (incident : Face → Tet × Tet)
    (w : Face → Bool) :
    (Tet × Bool) → (Tet × Bool) → Prop :=
  fun x y => ∃ f : Face,
    (((incident f).1 = x.1 ∧
      (incident f).2 = y.1) ∨
     ((incident f).2 = x.1 ∧
      (incident f).1 = y.1)) ∧
    y.2 = x.2.xor (w f)

def Reach (incident : Face → Tet × Tet)
    (w : Face → Bool)
    (x y : Tet × Bool) : Prop :=
  Relation.ReflTransGen (Step incident w) x y

theorem potential_of_unique_lifted_paths
    (incident : Face → Tet × Tet)
    (w : Face → Bool)
    (root : Tet)
    (hpath : ∀ t : Tet, ∃ q : Bool,
      Reach incident w (root, false) (t, q))
    (hunique : ∀ (t : Tet) (p q : Bool),
      Reach incident w (root, false) (t, p) →
      Reach incident w (root, false) (t, q) →
      p = q) :
    ∃ B : Tet → Bool, ∀ f : Face,
      (B (incident f).1).xor
      (B (incident f).2) = w f := by
  classical
  let B : Tet → Bool :=
    fun t => Classical.choose (hpath t)
  have hB (t : Tet) :
      Reach incident w (root, false)
        (t, B t) := by
    exact Classical.choose_spec (hpath t)
  refine ⟨B, ?_⟩
  intro f
  let t := (incident f).1
  let s := (incident f).2
  have hstep :
      Step incident w
        (t, B t)
        (s, (B t).xor (w f)) := by
    refine ⟨f, Or.inl ⟨rfl, rfl⟩, rfl⟩
  have htail :
      Reach incident w
        (root, false)
        (s, (B t).xor (w f)) := by
    exact (hB t).trans
      (Relation.ReflTransGen.single hstep)
  have hcoh :
      (B t).xor (w f) = B s :=
    hunique s _ _ htail (hB s)
  change (B t).xor (B s) = w f
  rw [← hcoh]
  cases hb : B t <;>
    cases hw : w f <;>
    simp [hb, hw]


/-- Reversing a lifted dual edge preserves legality. -/
theorem step_symmetric
    (incident : Face → Tet × Tet) (w : Face → Bool)
    {x y : Tet × Bool}
    (h : Step incident w x y) :
    Step incident w y x := by
  obtain ⟨f, hend, hbit⟩ := h
  refine ⟨f, ?_, ?_⟩
  · rcases hend with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  · cases x with
    | mk t p =>
      cases y with
      | mk u q =>
        cases p <;> cases q <;>
          cases hw : w f <;>
          simp_all [Bool.xor]

/-- Every lifted path can be traversed backwards. -/
theorem reach_symmetric
    (incident : Face → Tet × Tet) (w : Face → Bool)
    {x y : Tet × Bool}
    (h : Reach incident w x y) :
    Reach incident w y x := by
  exact Relation.ReflTransGen.trans_induction_on
    (motive := fun {a b} _ => Reach incident w b a)
    h
    (fun _ => Relation.ReflTransGen.refl)
    (fun hab =>
      Relation.ReflTransGen.single
        (step_symmetric incident w hab))
    (fun _ _ ih₁ ih₂ => ih₂.trans ih₁)

/-- XOR-translation preserves a lifted dual edge. -/
theorem step_shift
    (incident : Face → Tet × Tet) (w : Face → Bool)
    {x y : Tet × Bool}
    (h : Step incident w x y) (c : Bool) :
    Step incident w
      (x.1, x.2.xor c)
      (y.1, y.2.xor c) := by
  obtain ⟨f, hend, hbit⟩ := h
  refine ⟨f, hend, ?_⟩
  cases x with
  | mk t p =>
    cases y with
    | mk u q =>
      cases p <;> cases q <;>
        cases c <;> cases hw : w f <;>
        simp_all [Bool.xor]

/-- XOR-translation preserves every lifted path. -/
theorem reach_shift
    (incident : Face → Tet × Tet) (w : Face → Bool)
    {x y : Tet × Bool}
    (h : Reach incident w x y) (c : Bool) :
    Reach incident w
      (x.1, x.2.xor c)
      (y.1, y.2.xor c) := by
  induction h using Relation.ReflTransGen.trans_induction_on
    with
  | refl a =>
      exact Relation.ReflTransGen.refl
  | single hab =>
      exact Relation.ReflTransGen.single
        (step_shift incident w hab c)
  | trans hab hbc ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- A root with no odd lifted return has unique
    accumulated parity at every reachable tetrahedron. -/
theorem unique_parity_of_no_odd_return
    (incident : Face → Tet × Tet) (w : Face → Bool)
    (root : Tet)
    (hzero :
      ¬ Reach incident w (root, false) (root, true))
    (t : Tet) (p q : Bool)
    (hp : Reach incident w (root, false) (t, p))
    (hq : Reach incident w (root, false) (t, q)) :
    p = q := by
  have hrev :
      Reach incident w (t, p) (root, false) :=
    reach_symmetric incident w hp
  have hshift :=
    reach_shift incident w hrev (p.xor q)
  have hback :
      Reach incident w (t, q) (root, p.xor q) := by
    cases p <;> cases q <;>
      simpa [Bool.xor] using hshift
  have hclosed :
      Reach incident w
        (root, false) (root, p.xor q) :=
    hq.trans hback
  cases p <;> cases q <;>
    simp_all [Bool.xor]

/-- Closed-return parity suffices for global finite
    tetrahedron-potential reconstruction. -/
theorem potential_of_no_odd_return
    (incident : Face → Tet × Tet)
    (w : Face → Bool)
    (root : Tet)
    (hpath : ∀ t : Tet, ∃ q : Bool,
      Reach incident w (root, false) (t, q))
    (hzero :
      ¬ Reach incident w (root, false) (root, true)) :
    ∃ B : Tet → Bool, ∀ f : Face,
      (B (incident f).1).xor
      (B (incident f).2) = w f := by
  apply potential_of_unique_lifted_paths
    incident w root hpath
  intro t p q hp hq
  exact unique_parity_of_no_odd_return
    incident w root hzero t p q hp hq

#print axioms step_symmetric
#print axioms reach_symmetric
#print axioms step_shift
#print axioms reach_shift
#print axioms unique_parity_of_no_odd_return
#print axioms potential_of_no_odd_return

end Poincare.DualPotentialCandidate
