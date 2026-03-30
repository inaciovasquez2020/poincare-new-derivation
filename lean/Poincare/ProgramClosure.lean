namespace Poincare

constant Triangulation : Type
constant Move : Type
constant allowedMoves : Triangulation → Finset Move
constant applyMove : Move → Triangulation → Triangulation
constant Phi : Triangulation → ℕ
constant S3 : Triangulation → Prop
constant terminal : Triangulation → Prop

theorem poincare_program_closure :
  (∀ T, ¬ S3 T → ∃ m ∈ allowedMoves T, Phi (applyMove m T) < Phi T) →
  (∀ T, Phi T = 0 → S3 T) →
  ∀ T, terminal T → S3 T := by
  intro h1 h2 T hT
  have : Phi T = 0 := by sorry
  exact h2 T this

end Poincare
