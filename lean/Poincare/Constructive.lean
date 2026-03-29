import Poincare.Kernel
import Poincare.Descent

namespace Poincare

theorem termination_strong :
  WellFounded (fun K1 K2 : Triangulation => measure K1 < measure K2) :=
  termination

theorem correctness_full (K : Triangulation) :
  measure K = 0 → S3 K :=
  correctness K

end Poincare
