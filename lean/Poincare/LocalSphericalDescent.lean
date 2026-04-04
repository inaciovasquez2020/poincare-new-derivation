import Mathlib
import Poincare.Triangulation
import Poincare.Moves
import Poincare.PhiZeroCharacterizesS3
import Poincare.ExistsStrictDescentMove

namespace Poincare

theorem local_spherical_descent :
  ∀ T : Triangulation,
    ¬ S3 T →
    ∃ m : PachnerMove,
      Phi (applyMove T m) < Phi T := by
  intro T hT
  have hphi : Phi T ≠ 0 := by
    intro h0
    have : S3 T := (phi_zero_characterizes_s3 T).mp h0
    exact hT this
  exact exists_strict_descent_move T hphi

end Poincare
