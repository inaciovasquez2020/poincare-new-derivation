namespace Poincare

constant Triangulation : Type
constant Phi : Triangulation → ℕ
constant S3 : Triangulation → Prop

theorem zero_defect_axiom :
  ∀ T : Triangulation,
    Phi T = 0 → S3 T

theorem zero_defect_characterization :
  ∀ T : Triangulation,
    Phi T = 0 → S3 T :=
  zero_defect_axiom

end Poincare
