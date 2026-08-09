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


theorem phiSupport_zero_iff_phi_zero
    (K : Triangulation) :
    PhiSupport K = 0 ↔ Phi K = 0 := by
  have hfold_zero :
      ∀ vs : List Nat,
        (∀ v ∈ vs, vertexDefect K v = 0) →
        vs.foldl (fun acc v => acc + vertexDefect K v) 0 = 0 := by
    intro vs hvs
    induction vs with
    | nil =>
        simp
    | cons a t ih =>
        have ha : vertexDefect K a = 0 := hvs a (by simp)
        have ht : ∀ v ∈ t, vertexDefect K v = 0 := by
          intro v hv
          exact hvs v (by simp [hv])
        simp [ha, ih ht]

  constructor
  · intro hSupport
    have hsupport_zero :
        ∀ v ∈ vertexSupport K, vertexDefect K v = 0 := by
      have hmain :=
        foldl_add_fn_eq_zero_supportwise
          (f := fun x => vertexDefect K x)
          (l := vertexSupport K)
          (acc := 0)
          (by simpa [PhiSupport] using hSupport)
      exact hmain.2

    have hall_zero :
        ∀ v ∈ allVerts K, vertexDefect K v = 0 := by
      intro v hv
      exact hsupport_zero v ((mem_vertexSupport_iff K v).2 hv)

    simpa [Phi] using hfold_zero (allVerts K) hall_zero

  · intro hPhi
    have hall_zero :
        ∀ v ∈ allVerts K, vertexDefect K v = 0 :=
      phi_sum_zero_implies_supportwise_zero K hPhi

    have hsupport_zero :
        ∀ v ∈ vertexSupport K, vertexDefect K v = 0 := by
      intro v hv
      exact hall_zero v ((mem_vertexSupport_iff K v).1 hv)

    simpa [PhiSupport] using hfold_zero (vertexSupport K) hsupport_zero

end Poincare
