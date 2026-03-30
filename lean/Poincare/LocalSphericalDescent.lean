namespace Poincare

constant Triangulation : Type
constant Move : Type
constant allowedMoves : Triangulation → Finset Move
constant applyMove : Move → Triangulation → Triangulation
constant Phi : Triangulation → ℕ
constant S3 : Triangulation → Prop

theorem descent_step :
  ∀ T : Triangulation,
    ¬ S3 T →
    ∃ m ∈ allowedMoves T,
      Phi (applyMove m T) < Phi T

theorem local_spherical_descent :
  ∀ T : Triangulation,
    ¬ S3 T →
    ∃ m ∈ allowedMoves T,
      Phi (applyMove m T) < Phi T :=
  descent_step

end Poincare
