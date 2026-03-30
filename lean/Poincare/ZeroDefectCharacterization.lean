namespace Poincare

constant Triangulation : Type
constant Phi : Triangulation → ℕ
constant S3 : Triangulation → Prop

theorem zero_defect_characterization :
  ∀ T : Triangulation,
    Phi T = 0 → S3 T := by
  admit

end Poincare
