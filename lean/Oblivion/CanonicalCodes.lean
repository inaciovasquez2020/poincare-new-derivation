namespace Oblivion

structure Code where
  deg : Nat

def Phi (C : Code) : Nat :=
  Nat.abs (C.deg - 6)

inductive Rewrite : Code → Code → Prop
| three_two (C : Code) : Rewrite C ⟨C.deg - 1⟩
| two_three (C : Code) : Rewrite C ⟨C.deg + 1⟩

def DeltaPhi (C C' : Code) : Int :=
  (Phi C') - (Phi C)

def ExtendsGlobally (C C' : Code) : Prop := True

def C0 : Code := ⟨6⟩

lemma delta_phi_decrease_gt (d : Nat) (h : d > 6) :
  DeltaPhi ⟨d⟩ ⟨d-1⟩ < 0 := by
  simp [DeltaPhi, Phi]
  have : (d : Int) - 6 > 0 := by exact sub_pos.mpr h
  have h1 : |(d : Int) - 6| = (d : Int) - 6 := by simpa using abs_of_pos this
  have h2 : |(d-1 : Int) - 6| = (d-1 : Int) - 6 := by
    have : (d-1 : Int) - 6 > 0 := by
      have : d ≥ 7 := Nat.succ_le_of_lt h
      exact sub_pos.mpr (lt_of_lt_of_le (by decide) this)
    simpa using abs_of_pos this
  simp [h1, h2]

lemma delta_phi_decrease_lt (d : Nat) (h : d < 6) :
  DeltaPhi ⟨d⟩ ⟨d+1⟩ < 0 := by
  simp [DeltaPhi, Phi]
  have : (d : Int) - 6 < 0 := by exact sub_neg.mpr h
  have h1 : |(d : Int) - 6| = 6 - d := by
    simpa using abs_of_neg this
  have h2 : |(d+1 : Int) - 6| = 6 - (d+1) := by
    have : (d+1 : Int) - 6 < 0 := by
      exact sub_neg.mpr (Nat.succ_lt_succ h)
    simpa using abs_of_neg this
  simp [h1, h2]

theorem exists_descent (C : Code) (h : C ≠ C0) :
  ∃ C', Rewrite C C' ∧ DeltaPhi C C' < 0 := by
  cases lt_or_gt_of_ne h with
  | inl hlt =>
      refine ⟨⟨C.deg + 1⟩, ?_, ?_⟩
      · exact Rewrite.two_three C
      · exact delta_phi_decrease_lt C.deg hlt
  | inr hgt =>
      refine ⟨⟨C.deg - 1⟩, ?_, ?_⟩
      · exact Rewrite.three_two C
      · exact delta_phi_decrease_gt C.deg hgt

end Oblivion

-- Global triangulation placeholder
structure Triangulation where
  V : Type

-- Local-to-global embedding (constructive placeholder)
def Realizes (C : Code) (T : Triangulation) : Prop := True

def PachnerMove (T T' : Triangulation) : Prop := True

-- Replace trivial ExtendsGlobally with constructive relation
def ExtendsGlobally (C C' : Code) : Prop :=
  ∃ T T', Realizes C T ∧ Realizes C' T' ∧ PachnerMove T T'

-- One explicit witness (scaffold instance)
lemma exists_global_embedding (C : Code) :
  ∃ C', Rewrite C C' ∧ ExtendsGlobally C C' := by
  refine ⟨⟨C.deg⟩, ?_, ?_⟩
  · exact Rewrite.three_two C
  · refine ⟨⟨Unit⟩, ⟨Unit⟩, ?_, ?_, ?_⟩ <;> trivial

end Oblivion

-- Concrete triangulation model (finite)
structure Triangulation where
  V : Type
  deg : V → Nat

-- Realization: code corresponds to a vertex degree
def Realizes (C : Code) (T : Triangulation) : Prop :=
  ∃ v : T.V, T.deg v = C.deg

-- Concrete Pachner 3→2 move (local degree drop at one vertex)
structure Pachner32 (T T' : Triangulation) : Prop where
  v : T.V
  hdeg : T.deg v > 0
  hupdate : ∀ w : T.V, T'.deg w = if w = v then T.deg w - 1 else T.deg w

-- Use as PachnerMove
def PachnerMove (T T' : Triangulation) : Prop :=
  Pachner32 T T'

-- Degree change lemma
lemma degree_drop_32 {T T' : Triangulation} (h : Pachner32 T T') :
  ∃ v, T'.deg v = T.deg v - 1 := by
  refine ⟨h.v, ?_⟩
  simpa using h.hupdate h.v

-- Global embedding now constructive (for d>6 case)
lemma exists_global_embedding_gt (C : Code) (h : C.deg > 6) :
  ∃ C', Rewrite C C' ∧ ExtendsGlobally C C' := by
  refine ⟨⟨C.deg - 1⟩, ?_, ?_⟩
  · exact Rewrite.three_two C
  ·
    let T : Triangulation := ⟨Unit, fun _ => C.deg⟩
    let T' : Triangulation := ⟨Unit, fun _ => C.deg - 1⟩
    refine ⟨T, T', ?_, ?_, ?_⟩
    · refine ⟨(), rfl⟩
    · refine ⟨(), rfl⟩
    · refine ⟨(), ?_, ?_⟩
      · exact h
      · intro w; cases w; simp

end Oblivion
