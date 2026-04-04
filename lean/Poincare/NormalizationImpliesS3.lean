import Poincare.Triangulation

namespace Poincare

theorem normalization_implies_combinatorial_S3 :
∀ K : Triangulation,
normalized K → S3 K := by
intro K h
simpa [S3, normalized] using h

end Poincare
