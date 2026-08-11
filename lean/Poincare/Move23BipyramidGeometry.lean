import Poincare.Move23BipyramidCoefficients

open Set

namespace Poincare

private def move23Point (x y z : ℝ) : Move23BipyramidAmbient :=
  WithLp.toLp 2 ![x, y, z]

def move23BipyramidA : Move23BipyramidAmbient := move23Point 1 0 0
def move23BipyramidB : Move23BipyramidAmbient := move23Point 0 1 0
def move23BipyramidC : Move23BipyramidAmbient := move23Point (-1) (-1) 0
def move23BipyramidD : Move23BipyramidAmbient := move23Point 0 0 1
def move23BipyramidE : Move23BipyramidAmbient := move23Point 0 0 (-1)

@[simp] theorem move23BipyramidA_apply (i : Fin 3) :
    move23BipyramidA i = ![1, 0, 0] i := rfl
@[simp] theorem move23BipyramidB_apply (i : Fin 3) :
    move23BipyramidB i = ![0, 1, 0] i := rfl
@[simp] theorem move23BipyramidC_apply (i : Fin 3) :
    move23BipyramidC i = ![-1, -1, 0] i := rfl
@[simp] theorem move23BipyramidD_apply (i : Fin 3) :
    move23BipyramidD i = ![0, 0, 1] i := rfl
@[simp] theorem move23BipyramidE_apply (i : Fin 3) :
    move23BipyramidE i = ![0, 0, -1] i := rfl

@[simp] theorem move23BipyramidA_ofLp_apply (i : Fin 3) :
    WithLp.ofLp move23BipyramidA i = ![1, 0, 0] i := rfl
@[simp] theorem move23BipyramidB_ofLp_apply (i : Fin 3) :
    WithLp.ofLp move23BipyramidB i = ![0, 1, 0] i := rfl
@[simp] theorem move23BipyramidC_ofLp_apply (i : Fin 3) :
    WithLp.ofLp move23BipyramidC i = ![-1, -1, 0] i := rfl
@[simp] theorem move23BipyramidD_ofLp_apply (i : Fin 3) :
    WithLp.ofLp move23BipyramidD i = ![0, 0, 1] i := rfl
@[simp] theorem move23BipyramidE_ofLp_apply (i : Fin 3) :
    WithLp.ofLp move23BipyramidE i = ![0, 0, -1] i := rfl

def move23BipyramidABCD : Fin 4 → Move23BipyramidAmbient :=
  ![move23BipyramidA, move23BipyramidB, move23BipyramidC, move23BipyramidD]
def move23BipyramidABCE : Fin 4 → Move23BipyramidAmbient :=
  ![move23BipyramidA, move23BipyramidB, move23BipyramidC, move23BipyramidE]
def move23BipyramidABDE : Fin 4 → Move23BipyramidAmbient :=
  ![move23BipyramidA, move23BipyramidB, move23BipyramidD, move23BipyramidE]
def move23BipyramidACDE : Fin 4 → Move23BipyramidAmbient :=
  ![move23BipyramidA, move23BipyramidC, move23BipyramidD, move23BipyramidE]
def move23BipyramidBCDE : Fin 4 → Move23BipyramidAmbient :=
  ![move23BipyramidB, move23BipyramidC, move23BipyramidD, move23BipyramidE]

noncomputable def move23TetrahedronBody
    (v : Fin 4 → Move23BipyramidAmbient) : Set Move23BipyramidAmbient :=
  convexHull ℝ (Set.range v)

noncomputable def move23BipyramidSourceBody : Set Move23BipyramidAmbient :=
  move23TetrahedronBody move23BipyramidABCD ∪
    move23TetrahedronBody move23BipyramidABCE

noncomputable def move23BipyramidTargetBody : Set Move23BipyramidAmbient :=
  move23TetrahedronBody move23BipyramidABDE ∪
    move23TetrahedronBody move23BipyramidACDE ∪
      move23TetrahedronBody move23BipyramidBCDE

private noncomputable def move23FiveCombination (a b c d e : ℝ) : Move23BipyramidAmbient :=
  a • move23BipyramidA + b • move23BipyramidB + c • move23BipyramidC +
    d • move23BipyramidD + e • move23BipyramidE

private theorem move23_shift_source (a b c d e m : ℝ) :
    move23FiveCombination (a - m) (b - m) (c - m)
        (d + (3 / 2) * m) (e + (3 / 2) * m) =
      move23FiveCombination a b c d e := by
  ext i
  fin_cases i <;>
    norm_num [move23FiveCombination, move23BipyramidA, move23BipyramidB,
      move23BipyramidC, move23BipyramidD, move23BipyramidE, move23Point] <;> ring

private theorem move23_shift_target (a b c d e m : ℝ) :
    move23FiveCombination (a + (2 / 3) * m) (b + (2 / 3) * m)
        (c + (2 / 3) * m) (d - m) (e - m) =
      move23FiveCombination a b c d e := by
  ext i
  fin_cases i <;>
    norm_num [move23FiveCombination, move23BipyramidA, move23BipyramidB,
      move23BipyramidC, move23BipyramidD, move23BipyramidE, move23Point]
  all_goals ring

private theorem nonneg_sub_min_left (a b : ℝ) : 0 ≤ a - min a b := by
  exact sub_nonneg.mpr (min_le_left _ _)

private theorem nonneg_sub_min_right (a b : ℝ) : 0 ≤ b - min a b := by
  exact sub_nonneg.mpr (min_le_right _ _)

private theorem min3_zero (a b c : ℝ) :
    a - min a (min b c) = 0 ∨ b - min a (min b c) = 0 ∨
      c - min a (min b c) = 0 := by
  rcases min_choice a (min b c) with h | h
  · left; rw [h]; ring
  · rcases min_choice b c with h' | h'
    · right; left; rw [h, h']; ring
    · right; right; rw [h, h']; ring

private theorem min2_zero (d e : ℝ) : d - min d e = 0 ∨ e - min d e = 0 := by
  rcases min_choice d e with h | h
  · left; rw [h]; ring
  · right; rw [h]; ring

theorem move23BipyramidSourceBody_eq_targetBody :
    move23BipyramidSourceBody = move23BipyramidTargetBody := by
  classical
  change
    (move23TetrahedronBody move23BipyramidABCD ∪
      move23TetrahedronBody move23BipyramidABCE) =
    ((move23TetrahedronBody move23BipyramidABDE ∪
      move23TetrahedronBody move23BipyramidACDE) ∪
      move23TetrahedronBody move23BipyramidBCDE)
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · rw [move23TetrahedronBody,
          mem_convexHull_range_fin4_iff_exists_weights] at hx
      obtain ⟨w, hw0, hw1, hwx⟩ := hx
      let a := w 0; let b := w 1; let c := w 2; let d := w 3
      let m := min a (min b c)
      have hm : 0 ≤ m := le_min (hw0 0) (le_min (hw0 1) (hw0 2))
      have hd : 0 ≤ d := hw0 3
      have ha : 0 ≤ a - m := nonneg_sub_min_left _ _
      have hb : 0 ≤ b - m := sub_nonneg.mpr (le_trans (min_le_right a (min b c)) (min_le_left b c))
      have hc : 0 ≤ c - m := sub_nonneg.mpr (le_trans (min_le_right a (min b c)) (min_le_right b c))
      have hsum : (a-m)+(b-m)+(c-m)+(d+(3/2)*m)+(0+(3/2)*m)=1 := by
        simp [Fin.sum_univ_succ] at hw1; linarith
      have hcomb : move23FiveCombination (a-m) (b-m) (c-m)
          (d+(3/2)*m) (0+(3/2)*m) = x := by
        rw [move23_shift_source]
        simpa [Fin.sum_univ_succ, move23FiveCombination, move23BipyramidABCD,
          a,b,c,d, add_assoc] using hwx
      rcases min3_zero a b c with h | h | h
      · right
        change a - m = 0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![b-m,c-m,d+(3/2)*m,(3/2)*m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [hb,hc,hm]; positivity
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidBCDE,
            move23FiveCombination, h, add_assoc] using hcomb
      · left; right
        change b - m = 0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a-m,c-m,d+(3/2)*m,(3/2)*m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hc,hm]; positivity
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidACDE,
            move23FiveCombination, h, add_assoc] using hcomb
      · left; left
        change c - m = 0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a-m,b-m,d+(3/2)*m,(3/2)*m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hb,hm]; positivity
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidABDE,
            move23FiveCombination, h, add_assoc] using hcomb
    · rw [move23TetrahedronBody,
          mem_convexHull_range_fin4_iff_exists_weights] at hx
      obtain ⟨w, hw0, hw1, hwx⟩ := hx
      let a := w 0; let b := w 1; let c := w 2; let e := w 3
      let m := min a (min b c)
      have hm : 0 ≤ m := le_min (hw0 0) (le_min (hw0 1) (hw0 2))
      have he : 0 ≤ e := hw0 3
      have ha : 0 ≤ a - m := nonneg_sub_min_left _ _
      have hb : 0 ≤ b - m := sub_nonneg.mpr (le_trans (min_le_right a (min b c)) (min_le_left b c))
      have hc : 0 ≤ c - m := sub_nonneg.mpr (le_trans (min_le_right a (min b c)) (min_le_right b c))
      have hcomb : move23FiveCombination (a-m) (b-m) (c-m)
          ((3/2)*m) (e+(3/2)*m) = x := by
        convert (move23_shift_source a b c 0 e m).trans ?_ using 1 <;> try ring
        simpa [Fin.sum_univ_succ, move23FiveCombination, move23BipyramidABCE,
          a,b,c,e, add_assoc] using hwx
      have hsum : (a-m)+(b-m)+(c-m)+((3/2)*m)+(e+(3/2)*m)=1 := by
        simp [Fin.sum_univ_succ] at hw1
        linarith
      rcases min3_zero a b c with h | h | h
      · right
        change a - m = 0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![b-m,c-m,(3/2)*m,e+(3/2)*m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [hb,hc,hm]; positivity
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidBCDE,
            move23FiveCombination, h, add_assoc] using hcomb
      · left; right
        change b - m = 0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a-m,c-m,(3/2)*m,e+(3/2)*m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hc,hm]; positivity
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidACDE,
            move23FiveCombination, h, add_assoc] using hcomb
      · left; left
        change c - m = 0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a-m,b-m,(3/2)*m,e+(3/2)*m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hb,hm]; positivity
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidABDE,
            move23FiveCombination, h, add_assoc] using hcomb
  · intro x hx
    rcases hx with (hx | hx) | hx
    all_goals
      rw [move23TetrahedronBody,
          mem_convexHull_range_fin4_iff_exists_weights] at hx
      obtain ⟨w, hw0, hw1, hwx⟩ := hx
    · let a := w 0; let b := w 1; let d := w 2; let e := w 3
      let c : ℝ := 0
      let m := min d e
      have hm : 0 ≤ m := le_min (hw0 2) (hw0 3)
      have ha : 0 ≤ a + (2/3)*m := by dsimp [a]; linarith [hw0 0]
      have hb : 0 ≤ b + (2/3)*m := by dsimp [b]; linarith [hw0 1]
      have hc : 0 ≤ c + (2/3)*m := by dsimp [c]; positivity
      have hdm : 0 ≤ d-m := nonneg_sub_min_left _ _
      have hem : 0 ≤ e-m := nonneg_sub_min_right _ _
      have hsum : (a+(2/3)*m)+(b+(2/3)*m)+(c+(2/3)*m)+(d-m)+(e-m)=1 := by
        simp [Fin.sum_univ_succ] at hw1
        linarith
      have hcomb : move23FiveCombination (a+(2/3)*m) (b+(2/3)*m)
          (c+(2/3)*m) (d-m) (e-m) = x := by
        rw [move23_shift_target]
        simpa [Fin.sum_univ_succ, move23FiveCombination, move23BipyramidABDE,
          a,b,c,d,e, add_assoc] using hwx
      rcases min2_zero d e with h | h
      · right
        change d-m=0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a+(2/3)*m,b+(2/3)*m,c+(2/3)*m,e-m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hb,hc,hem]
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidABCE,
            move23FiveCombination, h, add_assoc] using hcomb
      · left
        change e-m=0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a+(2/3)*m,b+(2/3)*m,c+(2/3)*m,d-m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hb,hc,hdm]
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidABCD,
            move23FiveCombination, h, add_assoc] using hcomb
    · let a := w 0; let c := w 1; let d := w 2; let e := w 3
      let b : ℝ := 0
      let m := min d e
      have hm : 0 ≤ m := le_min (hw0 2) (hw0 3)
      have ha : 0 ≤ a + (2/3)*m := by dsimp [a]; linarith [hw0 0]
      have hb : 0 ≤ b + (2/3)*m := by dsimp [b]; positivity
      have hc : 0 ≤ c + (2/3)*m := by dsimp [c]; linarith [hw0 1]
      have hdm : 0 ≤ d-m := nonneg_sub_min_left _ _
      have hem : 0 ≤ e-m := nonneg_sub_min_right _ _
      have hsum : (a+(2/3)*m)+(b+(2/3)*m)+(c+(2/3)*m)+(d-m)+(e-m)=1 := by
        simp [Fin.sum_univ_succ] at hw1
        linarith
      have hcomb : move23FiveCombination (a+(2/3)*m) (b+(2/3)*m)
          (c+(2/3)*m) (d-m) (e-m) = x := by
        rw [move23_shift_target]
        simpa [Fin.sum_univ_succ, move23FiveCombination, move23BipyramidACDE,
          a,b,c,d,e, add_assoc] using hwx
      rcases min2_zero d e with h | h
      · right
        change d-m=0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a+(2/3)*m,b+(2/3)*m,c+(2/3)*m,e-m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hb,hc,hem]
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidABCE,
            move23FiveCombination, h, add_assoc] using hcomb
      · left
        change e-m=0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a+(2/3)*m,b+(2/3)*m,c+(2/3)*m,d-m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hb,hc,hdm]
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidABCD,
            move23FiveCombination, h, add_assoc] using hcomb
    · let b := w 0; let c := w 1; let d := w 2; let e := w 3
      let a : ℝ := 0
      let m := min d e
      have hm : 0 ≤ m := le_min (hw0 2) (hw0 3)
      have ha : 0 ≤ a + (2/3)*m := by dsimp [a]; positivity
      have hb : 0 ≤ b + (2/3)*m := by dsimp [b]; linarith [hw0 0]
      have hc : 0 ≤ c + (2/3)*m := by dsimp [c]; linarith [hw0 1]
      have hdm : 0 ≤ d-m := nonneg_sub_min_left _ _
      have hem : 0 ≤ e-m := nonneg_sub_min_right _ _
      have hsum : (a+(2/3)*m)+(b+(2/3)*m)+(c+(2/3)*m)+(d-m)+(e-m)=1 := by
        simp [Fin.sum_univ_succ] at hw1
        linarith
      have hcomb : move23FiveCombination (a+(2/3)*m) (b+(2/3)*m)
          (c+(2/3)*m) (d-m) (e-m) = x := by
        rw [move23_shift_target]
        simpa [Fin.sum_univ_succ, move23FiveCombination, move23BipyramidBCDE,
          a,b,c,d,e, add_assoc] using hwx
      rcases min2_zero d e with h | h
      · right
        change d-m=0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a+(2/3)*m,b+(2/3)*m,c+(2/3)*m,e-m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hb,hc,hem]
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidABCE,
            move23FiveCombination, h, add_assoc] using hcomb
      · left
        change e-m=0 at h
        rw [move23TetrahedronBody, mem_convexHull_range_fin4_iff_exists_weights]
        refine ⟨![a+(2/3)*m,b+(2/3)*m,c+(2/3)*m,d-m], ?_, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha,hb,hc,hdm]
        · simpa [Fin.sum_univ_succ, h, add_assoc] using hsum
        · simpa [Fin.sum_univ_succ, move23BipyramidABCD,
            move23FiveCombination, h, add_assoc] using hcomb

theorem move23BipyramidABCD_injective : Function.Injective move23BipyramidABCD := by
  intro i j h; fin_cases i <;> fin_cases j <;>
    norm_num at h <;> simp_all [move23BipyramidABCD, move23BipyramidA, move23BipyramidB,
      move23BipyramidC, move23BipyramidD, move23Point]

theorem move23BipyramidABCE_injective : Function.Injective move23BipyramidABCE := by
  intro i j h; fin_cases i <;> fin_cases j <;>
    norm_num at h <;> simp_all [move23BipyramidABCE, move23BipyramidA, move23BipyramidB,
      move23BipyramidC, move23BipyramidE, move23Point]

theorem move23BipyramidABDE_injective : Function.Injective move23BipyramidABDE := by
  intro i j h; fin_cases i <;> fin_cases j <;>
    norm_num at h <;> simp_all [move23BipyramidABDE, move23BipyramidA, move23BipyramidB,
      move23BipyramidD, move23BipyramidE, move23Point] <;> linarith

theorem move23BipyramidACDE_injective : Function.Injective move23BipyramidACDE := by
  intro i j h; fin_cases i <;> fin_cases j <;>
    norm_num at h <;> simp_all [move23BipyramidACDE, move23BipyramidA, move23BipyramidC,
      move23BipyramidD, move23BipyramidE, move23Point] <;> linarith

theorem move23BipyramidBCDE_injective : Function.Injective move23BipyramidBCDE := by
  intro i j h; fin_cases i <;> fin_cases j <;>
    norm_num at h <;> simp_all [move23BipyramidBCDE, move23BipyramidB, move23BipyramidC,
      move23BipyramidD, move23BipyramidE, move23Point] <;> linarith

end Poincare
