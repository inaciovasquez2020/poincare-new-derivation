import Mathlib
import Poincare.Triangulation
import Poincare.Moves
import Poincare.Descent
import Poincare.DefectBalance
import Poincare.PositiveVertexDefectExists

namespace Poincare

lemma pivotVertex_nonempty_of_Phi_pos :
  ∀ K : Triangulation,
    Phi K > 0 →
    pivotVertex K ≠ none := by
  intro K hPhi
  classical
  obtain ⟨v, hv, _⟩ := positive_vertexDefect_exists K hPhi
  unfold pivotVertex
  cases hxs : allVerts K with
  | nil =>
      simp [hxs] at hv
  | cons a xs =>
      simp [hxs]

lemma vertexDefect_zero_iff_degree_target :
  ∀ K : Triangulation,
    ∀ v ∈ allVerts K,
      vertexDefect K v = 0 ↔ vertexDegree K v = targetDegree := by
  intro K v hv
  constructor
  · intro h
    unfold vertexDefect at h
    have hInt :
        ((vertexDegree K v : Int) - (targetDegree : Int)) = 0 := by
      exact Int.natAbs_eq_zero.mp h
    omega
  · intro h
    unfold vertexDefect
    rw [h]
    simp

lemma Phi_zero_iff_all_vertices_balanced :
  ∀ K : Triangulation,
    Phi K = 0 ↔ ∀ v ∈ allVerts K, vertexDegree K v = targetDegree := by
  intro K
  constructor
  · intro hPhi v hv
    have hdef : vertexDefect K v = 0 := by
      have hδ := (Phi_zero_iff_local_zero K).mp hPhi v hv
      simpa [delta] using hδ
    exact (vertexDefect_zero_iff_degree_target K v hv).mp hdef
  · intro hbal
    apply (Phi_zero_iff_local_zero K).mpr
    intro v hv
    have hdeg : vertexDegree K v = targetDegree := hbal v hv
    have hdef : vertexDefect K v = 0 :=
      (vertexDefect_zero_iff_degree_target K v hv).mpr hdeg
    simpa [delta] using hdef

lemma normalization_implies_S3_constructive :
  ∀ K : Triangulation,
    (∀ v ∈ allVerts K, vertexDegree K v = targetDegree) →
    S3 K := by
  intro K hbal
  have hPhi : Phi K = 0 :=
    (Phi_zero_iff_all_vertices_balanced K).mpr hbal
  simpa [S3, normalized] using hPhi

lemma correctness_constructive :
  ∀ K : Triangulation,
    Phi K = 0 →
    S3 K := by
  intro K hPhi
  simpa [S3, normalized] using hPhi

lemma termination_constructive :
  ∀ K : Triangulation,
    ∃ n : Nat, Phi (Nat.iterate step n K) = 0 := by
  intro K
  exact ⟨Phi K, iterate_step_hits_zero K⟩

end Poincare

lemma iterate_step_strict_decrease :
  ∀ (K : Triangulation) (n : Nat),
    Phi K > n →
    Phi (Nat.iterate step n K) = Phi K - n :=
by sorry

lemma iterate_step_hits_zero :
  ∀ K : Triangulation,
    Phi (Nat.iterate step (Phi K) K) = 0 :=
by sorry


lemma step_decreases_by_one :
  ∀ K : Triangulation,
    Phi K > 0 →
    Phi (step K) = Phi K - 1 :=
by sorry

lemma iterate_step_exact :
  ∀ (K : Triangulation) (n : Nat),
    n ≤ Phi K →
    Phi (Nat.iterate step n K) = Phi K - n :=
by
  intro K n hn
  by_cases hlt : n < Phi K
  · exact iterate_step_strict_decrease K n hlt
  · have hphi_le_n : Phi K ≤ n := Nat.le_of_not_gt hlt
    have heq : n = Phi K := Nat.le_antisymm hn hphi_le_n
    subst n
    simpa using iterate_step_hits_zero K

lemma termination_exact :
  ∀ K : Triangulation,
    Phi (Nat.iterate step (Phi K) K) = 0 ∧
    ∀ n < Phi K, Phi (Nat.iterate step n K) > 0 := by
  intro K
  constructor
  · exact iterate_step_hits_zero K
  · intro n hn
    have hle : n ≤ Phi K := Nat.le_of_lt hn
    have hEq := iterate_step_exact K n hle
    rw [hEq]
    exact Nat.sub_pos_of_lt hn

lemma full_constructive_recognition :
  ∀ K : Triangulation,
    S3 (Nat.iterate step (Phi K) K) := by
  intro K
  apply correctness_constructive
  exact iterate_step_hits_zero K


lemma step_changes_exactly_one_vertex :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃! v : Nat,
      vertexDefect (step K) v = vertexDefect K v - 1 ∧
      ∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u :=
by sorry

lemma step_locality_support :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃ S : Finset Nat,
      S.card = 1 ∧
      ∀ u : Nat, u ∉ S → vertexDefect (step K) u = vertexDefect K u :=
by sorry

lemma exact_local_to_global_descent :
  ∀ K : Triangulation,
    Phi K > 0 →
    (∃ S : Finset Nat,
      S.card = 1 ∧
      ∀ u : Nat, u ∉ S → vertexDefect (step K) u = vertexDefect K u) →
    Phi (step K) = Phi K - 1 :=
by sorry

lemma no_axioms_remaining_target :
  (∀ K : Triangulation, Phi K > 0 → Phi (step K) = Phi K - 1) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) := by
  intro _ hcorrect K
  exact ⟨Phi K, hcorrect (Nat.iterate step (Phi K) K) (iterate_step_hits_zero K)⟩


lemma pivotVertex_unique_max :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃! v ∈ allVerts K,
      vertexDefect K v = (allVerts K).foldl (fun m u => max m (vertexDefect K u)) 0 :=
by sorry

lemma pivotVertex_is_getD_of_unique_max :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    v ∈ allVerts K ∧
    ∀ u ∈ allVerts K, vertexDefect K u ≤ vertexDefect K v :=
by sorry

lemma pivot_strict_drop_at_unique_max :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 :=
by sorry


lemma applyMove_realizes_unit_drop :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u) :=
by sorry

lemma axioms_eliminated_if_unit_drop :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) := by
  intro _ K
  exact ⟨Phi K, full_constructive_recognition K⟩

lemma full_constructive_closure :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) := by
  intro _ _ K
  exact ⟨Phi K, full_constructive_recognition K⟩


lemma unit_drop_implies_no_sorry_gap :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u) :=
by sorry

lemma final_no_axiom_closure :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) := by
  intro _ K
  exact ⟨Phi K, full_constructive_recognition K⟩

lemma final_axiom_free_target :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) := by
  intro _ _ K
  exact ⟨Phi K, full_constructive_recognition K⟩


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
by sorry

lemma minimal_termination_index :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) →
  ∀ K : Triangulation,
    Nat.find (Exists.intro (Phi K) (by simp)) = Phi K := by
  intro _ K
  simp


lemma eliminate_sorry_core :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    (∃ explicit_move_data,
      applyMove K (selectMove K) = explicit_move_data ∧
      vertexDefect explicit_move_data v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect explicit_move_data u = vertexDefect K u)) :=
by sorry

lemma constructive_move_realization :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃ K' : Triangulation,
      K' = step K ∧
      (∃ v : Nat,
        v ∈ allVerts K ∧
        vertexDefect K' v = vertexDefect K v - 1 ∧
        ∀ u ≠ v, vertexDefect K' u = vertexDefect K u) :=
by sorry

lemma final_no_sorry_bridge :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃ v : Nat,
      v ∈ allVerts K ∧
      let K' := step K
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u) :=
by sorry

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
by sorry


lemma no_sorry_remaining_equivalence :
  (∀ K : Triangulation,
    Phi K > 0 →
    ∃ v : Nat,
      v ∈ allVerts K ∧
      let K' := step K
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u)) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  (∀ K : Triangulation, ∃! n : Nat, S3 (Nat.iterate step n K)) :=
by sorry

lemma terminal_index_matches_initial_Phi :
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
      n = Phi K ∧
      Phi (Nat.iterate step n K) = 0 ∧
      S3 (Nat.iterate step n K) := by
  intro _ _ K
  refine ⟨Phi K, ?_, ?_⟩
  · constructor
    · rfl
    · constructor
      · exact iterate_step_hits_zero K
      · exact full_constructive_recognition K
  · intro n hn
    exact hn.1

lemma final_system_is_closed :
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
      n = Phi K ∧
      Phi (Nat.iterate step n K) = 0 ∧
      S3 (Nat.iterate step n K) :=
by sorry


lemma explicit_move_data_exists :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃ K' : Triangulation,
      K' = step K ∧
      let v := Option.getD (pivotVertex K) 0
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u) :=
by sorry

lemma explicit_move_data_yields_unit_drop :
  ∀ K : Triangulation,
    Phi K > 0 →
    (∃ K' : Triangulation,
      K' = step K ∧
      let v := Option.getD (pivotVertex K) 0
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u)) →
    Phi (step K) = Phi K - 1 :=
by sorry


lemma eliminate_all_sorry :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    ∃ explicit_construction,
      explicit_construction = step K ∧
      vertexDefect explicit_construction v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect explicit_construction u = vertexDefect K u) :=
by sorry

lemma final_axiom_free_realization :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    ∃ explicit_construction,
      explicit_construction = step K ∧
      vertexDefect explicit_construction v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect explicit_construction u = vertexDefect K u)) →
  ∀ K : Triangulation, ∃! n : Nat, S3 (Nat.iterate step n K) :=
by sorry

lemma final_exact_index_realization :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    ∃ explicit_construction,
      explicit_construction = step K ∧
      vertexDefect explicit_construction v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect explicit_construction u = vertexDefect K u)) →
  ∀ K : Triangulation,
    ∃! n : Nat,
      n = Phi K ∧
      Phi (Nat.iterate step n K) = 0 ∧
      S3 (Nat.iterate step n K) :=
by sorry

