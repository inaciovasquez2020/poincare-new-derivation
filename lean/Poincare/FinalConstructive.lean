import Poincare.Triangulation
import Poincare.Moves
import Poincare.Descent
import Poincare.DefectBalance

namespace Poincare

lemma pivotVertex_nonempty_of_Phi_pos :
  ∀ K : Triangulation,
    Phi K > 0 →
    pivotVertex K ≠ none :=
by admit

lemma vertexDefect_zero_iff_degree_target :
  ∀ K : Triangulation,
    ∀ v ∈ allVerts K,
      vertexDefect K v = 0 ↔ vertexDegree K v = targetDegree :=
by admit

lemma Phi_zero_iff_all_vertices_balanced :
  ∀ K : Triangulation,
    Phi K = 0 ↔ ∀ v ∈ allVerts K, vertexDegree K v = targetDegree :=
by admit

lemma normalization_implies_S3_constructive :
  ∀ K : Triangulation,
    (∀ v ∈ allVerts K, vertexDegree K v = targetDegree) →
    S3 K :=
by admit

lemma correctness_constructive :
  ∀ K : Triangulation,
    Phi K = 0 →
    S3 K :=
by admit

lemma termination_constructive :
  ∀ K : Triangulation,
    ∃ n : Nat, Phi (Nat.iterate step n K) = 0 :=
by admit

end Poincare

lemma iterate_step_strict_decrease :
  ∀ (K : Triangulation) (n : Nat),
    Phi K > n →
    Phi (Nat.iterate step n K) = Phi K - n :=
by admit

lemma iterate_step_hits_zero :
  ∀ K : Triangulation,
    Phi (Nat.iterate step (Phi K) K) = 0 :=
by admit

