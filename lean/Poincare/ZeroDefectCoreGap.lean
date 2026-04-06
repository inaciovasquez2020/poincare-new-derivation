import Mathlib
import Poincare.Triangulation
import Poincare.NatZeroSplit
import Poincare.NatZeroRight

namespace Poincare

lemma foldl_add_fn_eq_zero_supportwise {α : Type} (f : α → Nat) :
  ∀ (l : List α) (acc : Nat),
    l.foldl (fun s x => s + f x) acc = 0 →
    acc = 0 ∧ ∀ x ∈ l, f x = 0 := by
  intro l
  induction l with
  | nil =>
      intro acc h
      constructor
      · simpa using h
      · intro x hx
        cases hx
  | cons a t ih =>
      intro acc h
      have h' : t.foldl (fun s x => s + f x) (acc + f a) = 0 := by
        simpa using h
      rcases ih (acc + f a) h' with ⟨haccfa, ht⟩
      have hsplit : acc = 0 ∧ f a = 0 := nat_add_eq_zero_split acc (f a) haccfa
      rcases hsplit with ⟨hacc, ha⟩
      constructor
      · exact hacc
      · intro x hx
        have hx' : x = a ∨ x ∈ t := by
          simpa [List.mem_cons] using hx
        rcases hx' with rfl | hx_t
        · exact ha
        · exact ht x hx_t

theorem phi_sum_zero_implies_supportwise_zero :
  ∀ K : Triangulation,
    Phi K = 0 →
    ∀ v ∈ allVerts K, vertexDefect K v = 0 := by
  intro K hPhi v hv
  have hmain :=
    foldl_add_fn_eq_zero_supportwise
      (f := fun x => vertexDefect K x)
      (l := allVerts K)
      (acc := 0)
      (by simpa [Phi] using hPhi)
  exact hmain.2 v hv

end Poincare
