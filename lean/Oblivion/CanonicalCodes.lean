namespace Oblivion

structure Code where
  deg : Nat

def Phi (C : Code) : Nat :=
  Nat.abs (C.deg - 6)

inductive Rewrite : Code → Code → Prop
| three_two (C : Code) : Rewrite C ⟨C.deg - 1⟩

def DeltaPhi (C C' : Code) : Int :=
  (Phi C') - (Phi C)

def ExtendsGlobally (C C' : Code) : Prop := True

def C0 : Code := ⟨6⟩

lemma delta_phi_decrease (d : Nat) (h : d > 6) :
  DeltaPhi ⟨d⟩ ⟨d-1⟩ < 0 := by
  simp [DeltaPhi, Phi]
  have : |(d-1 : Int) - 6| < |(d : Int) - 6| := by
    have : (d : Int) - 6 > 0 := by exact sub_pos.mpr h
    simp [abs_of_pos this, abs_of_pos (sub_pos.mpr (Nat.sub_lt h (by decide)))]
  simpa using this

theorem exists_descent (C : Code) (h : C.deg > 6) :
  ∃ C', Rewrite C C' ∧ DeltaPhi C C' < 0 := by
  refine ⟨⟨C.deg - 1⟩, ?_, ?_⟩
  · exact Rewrite.three_two C
  · exact delta_phi_decrease C.deg h

end Oblivion
