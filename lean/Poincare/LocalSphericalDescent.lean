namespace Poincare

constant Triangulation : Type
constant Move : Type
constant allowedMoves : Triangulation → Finset Move
constant applyMove : Move → Triangulation → Triangulation
constant Phi : Triangulation → ℕ
constant S3 : Triangulation → Prop

axiom phi_zero_characterizes_s3 :
  ∀ T : Triangulation,
    Phi T = 0 ↔ S3 T

theorem exists_strict_descent_move := by
  intro T h
  exact ⟨Zap T, by sorry, zap_strict_descent T h⟩
  ∀ T : Triangulation,
    Phi T ≠ 0 →
    ∃ m ∈ allowedMoves T,
      Phi (applyMove m T) < Phi T

theorem local_spherical_descent :
  ∀ T : Triangulation,
    ¬ S3 T →
    ∃ m ∈ allowedMoves T,
      Phi (applyMove m T) < Phi T := by
  intro T hT
  have hphi : Phi T ≠ 0 := by
    intro h0
    have : S3 T := (phi_zero_characterizes_s3 T).mp h0
    exact hT this
  exact exists_strict_descent_move T hphi

end Poincare
