namespace Oblivion

universe u

structure Configuration (α : Type u) where
  data : α
  rank : Nat

structure Witness (α : Type u) where
  support : Finset α
  center : α
  radius : Nat

structure WitnessSchema (α : Type u) where
  valid : Witness α → Prop

def witnessValue {α : Type u} (w : Witness α) : Nat := w.support.card

def extractR {α : Type u} (R : Nat) [DecidableEq α] (C : Configuration α) : Finset (Witness α) :=
  {{
    support := ({C.data} : Finset α),
    center := C.data,
    radius := R
  }}

def FOkAdmissible {α : Type u} (k R Δ B : Nat) (C : Configuration α) : Prop := by sorry

def DependencyRich {α : Type u} [DecidableEq α] (R : Nat) (C : Configuration α) : Prop :=
  ∃ w : Witness α, w ∈ extractR R C

def invariantAfter {α : Type u} (w : Witness α) (C : Configuration α) : Nat :=
  C.rank - witnessValue w

def ForcesCollapse {α : Type u} (W : Finset (Witness α)) (C : Configuration α) : Prop :=
  ∃ w : Witness α, w ∈ W ∧ invariantAfter w C < C.rank

def descend {α : Type u} (W : Finset (Witness α)) (C : Configuration α) : Nat :=
  match W.toList with
  | [] => C.rank
  | w :: _ => invariantAfter w C

theorem extractR_nonempty
  {α : Type u} [DecidableEq α] (R : Nat) (C : Configuration α) :
  ∃ w : Witness α, w ∈ extractR R C :=
by
  refine ⟨{
    support := ({C.data} : Finset α),
    center := C.data,
    radius := R
  }, ?_⟩
  simp [extractR]

theorem dependency_rich_of_extractR
  {α : Type u} [DecidableEq α] (R : Nat) (C : Configuration α) :
  DependencyRich R C :=
by
  exact extractR_nonempty R C

theorem witness_card_positive
  {α : Type u} [DecidableEq α] (R : Nat) (C : Configuration α) :
  witnessValue ({
    support := ({C.data} : Finset α),
    center := C.data,
    radius := R
  } : Witness α) = 1 :=
by
  simp [witnessValue]

theorem forcesCollapse_extractR
  {α : Type u} [DecidableEq α] (R : Nat) (C : Configuration α)
  (hr : 0 < C.rank) :
  ForcesCollapse (extractR R C) C :=
by
  refine ⟨{
    support := ({C.data} : Finset α),
    center := C.data,
    radius := R
  }, ?_, ?_⟩
  · simp [extractR]
  · simp [invariantAfter, witnessValue]
    exact Nat.sub_lt (Nat.succ_le_of_lt hr) (by decide)

theorem extractR_independent
  {α : Type u} [DecidableEq α] (R : Nat) (C : Configuration α) :
  ∀ w₁ ∈ extractR R C, ∀ w₂ ∈ extractR R C, w₁ = w₂ :=
by
  intro w₁ hw₁ w₂ hw₂
  have h1 : w₁ = {
    support := ({C.data} : Finset α),
    center := C.data,
    radius := R
  } := by simpa [extractR] using hw₁
  have h2 : w₂ = {
    support := ({C.data} : Finset α),
    center := C.data,
    radius := R
  } := by simpa [extractR] using hw₂
  rw [h1, h2]

theorem monotone_descent_of_forcesCollapse
  {α : Type u} (W : Finset (Witness α)) (C : Configuration α)
  (h : ForcesCollapse W C) :
  descend W C < C.rank :=
by
  rcases h with ⟨w, hw, hlt⟩
  cases hW : W.toList with
  | nil =>
      exfalso
      have : w ∈ ([] : List (Witness α)) := by simpa [Finset.mem_coe, hW] using hw
      simpa using this
  | cons w0 ws =>
      simp [descend, hW]
      have hw0 : w = w0 := by
        have : w ∈ w0 :: ws := by simpa [Finset.mem_coe, hW] using hw
        cases this with
        | head => rfl
        | tail htail =>
            cases htail
      simpa [hw0] using hlt

theorem lasr_finite_witness
  {α : Type u} [DecidableEq α]
  (k R Δ B : Nat)
  (C : Configuration α)
  (Hcfg : FOkAdmissible k R Δ B C)
  (Hdep : DependencyRich R C)
  (hr : 0 < C.rank)
  : ∃ W : Finset (Witness α),
      (∃ S : WitnessSchema α, ∀ w ∈ W, S.valid w) ∧
      ForcesCollapse W C :=
by
  refine ⟨extractR R C, ?_⟩
  refine ⟨⟨fun w => w ∈ extractR R C⟩, ?_, ?_⟩
  · intro w hw
    exact hw
  · exact forcesCollapse_extractR R C hr

end Oblivion
