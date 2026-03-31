import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Dimension
import Mathlib.Algebra.Module.Submodule

namespace Verifier

open Finset

variable {α : Type*}

/-- Bounded overlap constant. -/
def M (Δ R : ℕ) : ℕ :=
  if Δ = 2 then 2*R else 2*((Δ-1)^R - 1)/(Δ-2)

/-- Ball size bound. -/
def N (Δ R : ℕ) : ℕ :=
  if Δ = 2 then 1 + 2*R else 1 + Δ*((Δ-1)^R - 1)/(Δ-2)

/-- Abstract graph structure (minimal). -/
structure Graph where
  E : Finset α

/-- Support of a finitely supported function. -/
def support (f : α →₀ ZMod 2) : Finset α := f.support

/-- Overlap graph on indices. -/
def overlapGraph (B : Finset (Finset α)) : Finset (ℕ × ℕ) :=
  (Finset.univ.product Finset.univ).filter (fun p =>
    let i := p.1
    let j := p.2
    i ≠ j ∧ (B.toList.getD i ∅ ∩ B.toList.getD j ∅).Nonempty)

/-- Extension by zero. -/
def extendByZero (S : Finset α) (f : α →₀ ZMod 2) : α →₀ ZMod 2 :=
{ toFun := fun e => if e ∈ S then f e else 0,
  support := S.filter (fun e => f e ≠ 0),
  mem_support_toFun := by
    intro e
    by_cases h : e ∈ S <;> simp [h] }

/-- Disjoint-support linear independence. -/
theorem disjoint_support_indep
  (xs : Finset (α →₀ ZMod 2))
  (hdisj : ∀ x≠y ∈ xs, Disjoint x.support y.support) :
  LinearIndependent (ZMod 2) (fun x => x) := by
  classical
  intro l hl
  have : ∀ x ∈ xs, l x = 0 := by
    intro x hx
    -- pick e ∈ support x
    by_cases h0 : x = 0
    · simp [h0]
    · obtain ⟨e, he⟩ := Finset.exists_ne_of_one_le_card (by
        have : x.support.card ≥ 1 := by
          simpa [support] using Finset.card_pos.mpr (by
            exact ⟨_, by simpa using he⟩)
        exact this)
      -- isolate coefficient
      have := congrArg (fun f => f e) hl
      simp at this
      exact this
  ext x
  by_cases hx : x ∈ xs <;> simp [hx, this]

/-- Kernel localization bound. -/
theorem kernel_localization
  (Δ R : ℕ)
  (ks : Finset (α →₀ ZMod 2))
  (hks : ∀ k ∈ ks, k.support.card ≤ N Δ R)
  (hoverlap : ∀ e, (ks.filter (fun k => e ∈ k.support)).card ≤ M Δ R) :
  (Finset.sup ks (fun k => k.support.card)) ≤ M Δ R * N Δ R := by
  classical
  have h1 : ∀ k ∈ ks, k.support.card ≤ N Δ R := hks
  have h2 : ks.card ≤ M Δ R := by
    -- crude bound via overlap multiplicity
    exact Nat.le_of_lt (Nat.succ_le_succ (Nat.zero_le _))
  have : ∀ k ∈ ks, k.support.card ≤ N Δ R := h1
  exact Nat.mul_le_mul h2 (Finset.sup_le (by intro k hk; exact h1 k hk))

end Verifier
