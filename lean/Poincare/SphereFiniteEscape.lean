import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Poincare

open scoped RealInnerProductSpace

/-- A finite family of proper real linear subspaces admits a common avoiding unit vector. -/
theorem exists_unit_forall_notMem_submodule
    {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (p : ι → Submodule ℝ E) (hp : ∀ i, p i ≠ ⊤) :
    ∃ a : E, ‖a‖ = 1 ∧ ∀ i, a ∉ p i := by
  let q : Option ι → Submodule ℝ E
    | none => ⊥
    | some i => p i
  have hq : ∀ j, q j ≠ ⊤ := by
    rintro (_ | i)
    · exact bot_ne_top
    · exact hp i
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top q hq
  have hx0 : x ≠ 0 := by
    simpa [q] using hx none
  refine ⟨‖x‖⁻¹ • x, ?_, fun i hi => ?_⟩
  · simp [norm_smul, hx0]
  · apply hx (some i)
    have := (p i).smul_mem ‖x‖ hi
    simpa [q, smul_smul, hx0] using this

/-- A finite collection of planes spanned by pairs in Euclidean three-space admits a common
avoiding unit vector. -/
theorem exists_unit_not_mem_finset_pairSpans
    {ι : Type*} (s : Finset ι)
    (u v : ι → EuclideanSpace ℝ (Fin 3)) :
    ∃ a : EuclideanSpace ℝ (Fin 3), ‖a‖ = 1 ∧
      ∀ i ∈ s, a ∉ Submodule.span ℝ ({u i, v i} : Set (EuclideanSpace ℝ (Fin 3))) := by
  let p : s → Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := fun i =>
    Submodule.span ℝ ({u i, v i} : Set (EuclideanSpace ℝ (Fin 3)))
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i
    apply ne_of_lt
    apply span_lt_top_of_card_lt_finrank
    rw [finrank_euclideanSpace]
    exact lt_of_le_of_lt (by simpa using Finset.card_le_two (a := u i) (b := v i)) (by norm_num)
  obtain ⟨a, ha, havoid⟩ := exists_unit_forall_notMem_submodule p hp
  exact ⟨a, ha, fun i hi => havoid ⟨i, hi⟩⟩

end Poincare
