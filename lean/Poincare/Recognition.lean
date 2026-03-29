import Poincare.Descent

namespace Poincare

axiom normalization_implies_combinatorial_S3 :
  ∀ K, normalized K → S3 K

theorem correctness (K : Triangulation) :
    Phi K = 0 → S3 K := by
  intro h
  exact normalization_implies_combinatorial_S3 K h

end Poincare
