import Mathlib

open scoped BigOperators

namespace Poincare

section OrderedRing

variable {R ι : Type*}
variable [LinearOrderedRing R]

theorem abs_add_lt_abs_imp_mul_neg {a b : R} (h : |a + b| < |a|) : a * b < 0 := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · have ha : 0 < a := by
      by_contra hna
      have h1 : |a + b| = -(a + b) := by
        apply abs_of_nonpos
        linarith
      have h2 : |a| = -a := by
        exact abs_of_nonpos hna
      have : -(a + b) < -a := by simpa [h1, h2] using h
      linarith
    exact mul_neg_of_pos_of_neg ha hb
  · simpa using h
  · have ha : a < 0 := by
      by_contra hna
      have h1 : |a + b| = a + b := by
        apply abs_of_nonneg
        linarith
      have h2 : |a| = a := by
        exact abs_of_nonneg hna
      have : a + b < a := by simpa [h1, h2] using h
      linarith
    exact mul_neg_of_neg_of_pos ha hb

end OrderedRing

section FinsetLemmas

variable {R ι : Type*}
variable [LinearOrderedRing R]
variable [DecidableEq ι]

theorem exists_lt_of_sum_lt {s : Finset ι} {f g : ι → R}
    (h : (∑ i in s, f i) < ∑ i in s, g i) :
    ∃ i ∈ s, f i < g i := by
  by_contra hno
  have hge : ∀ i ∈ s, g i ≤ f i := by
    intro i hi
    by_contra hlt
    exact hno ⟨i, hi, hlt⟩
  have hsum : (∑ i in s, g i) ≤ ∑ i in s, f i := by
    exact Finset.sum_le_sum (fun i hi => hge i hi)
  exact (not_le_of_gt h) hsum

theorem exists_coord_abs_lt_of_sum_abs_lt {s : Finset ι} {x y : ι → R}
    (h : (∑ i in s, |y i|) < ∑ i in s, |x i|) :
    ∃ i ∈ s, |y i| < |x i| := by
  exact exists_lt_of_sum_lt h

theorem sum_abs_update_eq {s : Finset ι} (i : ι) (x : ι → R) (v : R) :
    ∑ j in s, |Function.update x i v j|
      = ∑ j in s.erase i, |x j| + if i ∈ s then |v| else 0 := by
  by_cases hi : i ∈ s
  · calc
      ∑ j in s, |Function.update x i v j|
          = ∑ j in s.erase i, |Function.update x i v j| + |Function.update x i v i| := by
              symm
              exact Finset.sum_erase_add (fun j => |Function.update x i v j|) hi
      _ = ∑ j in s.erase i, |x j| + |v| := by
            simp [Function.update, hi]
      _ = ∑ j in s.erase i, |x j| + if i ∈ s then |v| else 0 := by
            simp [hi]
  · simp [hi, Function.update]

theorem sum_abs_eq_erase_add {s : Finset ι} (i : ι) (x : ι → R) :
    ∑ j in s, |x j|
      = ∑ j in s.erase i, |x j| + if i ∈ s then |x i| else 0 := by
  by_cases hi : i ∈ s
  · calc
      ∑ j in s, |x j|
          = ∑ j in s.erase i, |x j| + |x i| := by
              symm
              exact Finset.sum_erase_add (fun j => |x j|) hi
      _ = ∑ j in s.erase i, |x j| + if i ∈ s then |x i| else 0 := by
            simp [hi]
  · simp [hi]

theorem updated_coord_abs_lt_of_sum_descent
    {s : Finset ι} {x : ι → R} {i : ι} {v : R}
    (hi : i ∈ s)
    (hΦ : (∑ j in s, |Function.update x i v j|) < ∑ j in s, |x j|) :
    |v| < |x i| := by
  rw [sum_abs_update_eq (i := i) (x := x) (v := v), sum_abs_eq_erase_add (i := i) (x := x)] at hΦ
  simpa [hi] using lt_of_add_lt_add_left hΦ

theorem opposing_coord_of_descent
    {s : Finset ι} {x : ι → R} {i : ι} {δ : R}
    (hi : i ∈ s)
    (hΦ : (∑ j in s, |Function.update x i (x i + δ) j|) < ∑ j in s, |x j|) :
    x i * δ < 0 := by
  have hcoord : |x i + δ| < |x i| := by
    exact updated_coord_abs_lt_of_sum_descent (hi := hi) (hΦ := hΦ)
  exact abs_add_lt_abs_imp_mul_neg hcoord

end FinsetLemmas

end Poincare
