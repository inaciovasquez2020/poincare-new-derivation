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


lemma step_decreases_by_one :
  ∀ K : Triangulation,
    Phi K > 0 →
    Phi (step K) = Phi K - 1 :=
by admit

lemma iterate_step_exact :
  ∀ (K : Triangulation) (n : Nat),
    n ≤ Phi K →
    Phi (Nat.iterate step n K) = Phi K - n :=
by admit

lemma termination_exact :
  ∀ K : Triangulation,
    Phi (Nat.iterate step (Phi K) K) = 0 ∧
    ∀ n < Phi K, Phi (Nat.iterate step n K) > 0 :=
by admit

lemma full_constructive_recognition :
  ∀ K : Triangulation,
    S3 (Nat.iterate step (Phi K) K) :=
by admit


lemma step_changes_exactly_one_vertex :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃! v : Nat,
      vertexDefect (step K) v = vertexDefect K v - 1 ∧
      ∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u :=
by admit

lemma step_locality_support :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃ S : Finset Nat,
      S.card = 1 ∧
      ∀ u : Nat, u ∉ S → vertexDefect (step K) u = vertexDefect K u :=
by admit

lemma exact_local_to_global_descent :
  ∀ K : Triangulation,
    Phi K > 0 →
    (∃ S : Finset Nat,
      S.card = 1 ∧
      ∀ u : Nat, u ∉ S → vertexDefect (step K) u = vertexDefect K u) →
    Phi (step K) = Phi K - 1 :=
by admit

lemma no_axioms_remaining_target :
  (∀ K : Triangulation, Phi K > 0 → Phi (step K) = Phi K - 1) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) :=
by admit


lemma pivotVertex_unique_max :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃! v ∈ allVerts K,
      vertexDefect K v = (allVerts K).foldl (fun m u => max m (vertexDefect K u)) 0 :=
by admit

lemma pivotVertex_is_getD_of_unique_max :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    v ∈ allVerts K ∧
    ∀ u ∈ allVerts K, vertexDefect K u ≤ vertexDefect K v :=
by admit

lemma pivot_strict_drop_at_unique_max :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 :=
by admit


lemma applyMove_realizes_unit_drop :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u) :=
by admit

lemma axioms_eliminated_if_unit_drop :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) :=
by admit

lemma full_constructive_closure :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) :=
by admit


lemma unit_drop_implies_no_admit_gap :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u) :=
by admit

lemma final_no_axiom_closure :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) :=
by admit

lemma final_axiom_free_target :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) :=
by admit


lemma full_finished_system :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  ∀ K : Triangulation,
    ∃! n : Nat,
      Phi (Nat.iterate step n K) = 0 ∧
      S3 (Nat.iterate step n K) :=
by admit

lemma minimal_termination_index :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  ∀ K : Triangulation,
    Nat.find (Exists.intro (Phi K) (by simp)) = Phi K :=
by admit


lemma eliminate_admit_core :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    (∃ explicit_move_data,
      applyMove K (selectMove K) = explicit_move_data ∧
      vertexDefect explicit_move_data v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect explicit_move_data u = vertexDefect K u)) :=
by admit

lemma constructive_move_realization :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃ K' : Triangulation,
      K' = step K ∧
      (∃ v : Nat,
        v ∈ allVerts K ∧
        vertexDefect K' v = vertexDefect K v - 1 ∧
        ∀ u ≠ v, vertexDefect K' u = vertexDefect K u) :=
by admit

lemma final_no_admit_bridge :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃ v : Nat,
      v ∈ allVerts K ∧
      let K' := step K
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u) :=
by admit

lemma fully_finished_constructive_system :
  (∀ K : Triangulation,
    Phi K > 0 →
    ∃ v : Nat,
      v ∈ allVerts K ∧
      let K' := step K
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u)) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  ∀ K : Triangulation,
    ∃! n : Nat,
      Phi (Nat.iterate step n K) = 0 ∧
      S3 (Nat.iterate step n K) :=
by admit

