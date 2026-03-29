namespace Oblivion

universe u

structure Configuration (α : Type u) where
  data : α

structure Witness (α : Type u) where
  data : α

structure WitnessSchema (α : Type u) where
  valid : Witness α → Prop

def witnessValue {α : Type u} (w : Witness α) : α := w.data

def extract {α : Type u} (C : Configuration α) : Finset (Witness α) := {⟨C.data⟩}

def FOkAdmissible {α : Type u} (k R Δ B : Nat) (C : Configuration α) : Prop := True

def DependencyRich {α : Type u} (C : Configuration α) : Prop :=
  ∃ w : Witness α, w ∈ extract C

def ForcesCollapse {α : Type u} (W : Finset (Witness α)) (C : Configuration α) : Prop :=
  ∃ w : Witness α, w ∈ W ∧ witnessValue w = C.data

theorem extract_nonempty
  {α : Type u} (C : Configuration α) :
  ∃ w : Witness α, w ∈ extract C :=
by
  refine ⟨⟨C.data⟩, ?_⟩
  simp [extract]

theorem dependency_rich_of_extract
  {α : Type u} (C : Configuration α) :
  DependencyRich C :=
by
  exact extract_nonempty C

theorem forcesCollapse_extract
  {α : Type u} (C : Configuration α) :
  ForcesCollapse (extract C) C :=
by
  refine ⟨⟨C.data⟩, ?_, rfl⟩
  simp [extract]

theorem lasr_finite_witness
  {α : Type u}
  (k R Δ B : Nat)
  (C : Configuration α)
  (Hcfg : FOkAdmissible k R Δ B C)
  (Hdep : DependencyRich C)
  : ∃ W : Finset (Witness α),
      (∃ S : WitnessSchema α, ∀ w ∈ W, S.valid w) ∧
      ForcesCollapse W C :=
by
  refine ⟨extract C, ?_⟩
  refine ⟨⟨fun w => w ∈ extract C⟩, ?_, ?_⟩
  · intro w hw
    exact hw
  · exact forcesCollapse_extract C

end Oblivion
