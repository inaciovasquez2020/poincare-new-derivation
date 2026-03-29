namespace Oblivion

universe u

structure Configuration (α : Type u) where
  data : α
  rank : Nat

structure Witness (α : Type u) where
  support : Finset α
  center : α
  radius : Nat

variable {α : Type u}

axiom extractR : Nat → Configuration α → Finset (Witness α)

axiom witnessVector : Witness α → (Finset α → ℕ)

axiom witnessRankContribution : Witness α → Nat

axiom descend : Finset (Witness α) → Configuration α → Nat

axiom nstep : Nat → Configuration α → Configuration α

axiom terminal : Configuration α → Prop

axiom extractR_two_witnesses :
  ∀ (R : Nat) (C : Configuration α),
    ∃ w₁ w₂ : Witness α,
      w₁ ≠ w₂ ∧ w₁ ∈ extractR R C ∧ w₂ ∈ extractR R C

axiom extractR_linear_independent_F2 :
  ∀ (R : Nat) (C : Configuration α),
    LinearIndependent (fun w : {w // w ∈ extractR R C} => witnessVector (w : Witness α))

axiom witnessRankContribution_positive_on_extractR :
  ∀ (R : Nat) (C : Configuration α) (w : Witness α),
    w ∈ extractR R C → 0 < witnessRankContribution w

axiom descend_strict :
  ∀ (R : Nat) (C : Configuration α),
    0 < C.rank → descend (extractR R C) C < C.rank

axiom nstep_rank_realizes_iterated_descend :
  ∀ (R n : Nat) (x : Configuration α),
    (nstep n x).rank = Nat.iterate (fun r => r - 1) n x.rank

axiom terminal_iff_zero_rank :
  ∀ x : Configuration α, terminal x ↔ x.rank = 0

end Oblivion
