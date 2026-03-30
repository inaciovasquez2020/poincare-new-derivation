namespace Poincare

constant Triangulation : Type
constant Move : Type
constant Phi : Triangulation → ℕ
constant applyMove : Move → Triangulation → Triangulation

-- Zåp operator: canonical descent selector
constant Zap : Triangulation → Move

axiom zap_strict_descent :
  ∀ T : Triangulation,
    Phi T ≠ 0 →
    Phi (applyMove (Zap T) T) < Phi T

end Poincare
