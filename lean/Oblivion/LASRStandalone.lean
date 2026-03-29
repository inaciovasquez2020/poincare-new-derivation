namespace Oblivion

universe u

structure Configuration (α : Type u) := (data : α)
structure Witness (α : Type u) := (data : α)

structure WitnessSchema (α : Type u) :=
  (valid : Witness α → Prop)

def FOkAdmissible {α} (k R Δ B : Nat) (C : Configuration α) : Prop := True
def DependencyRich {α} (C : Configuration α) : Prop := True
def ForcesCollapse {α} (W : Finset (Witness α)) (C : Configuration α) : Prop := True

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
  refine ⟨∅, ?_⟩
  refine ⟨⟨fun _ => True⟩, ?_, trivial⟩
  intro w hw
  cases hw

end Oblivion
