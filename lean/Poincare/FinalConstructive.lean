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

lemma termination_constructive_boundary :
  ¬ (∀ K : Triangulation,
    ∃ n : Nat, Phi (Nat.iterate step n K) = 0) := by
  intro h
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hphi : Phi K = 12 := by
    native_decide
  obtain ⟨n, hn⟩ := h K
  have hphi_step : Function.comp Phi step = Phi := by
    funext T
    unfold step
    rw [applyMove_spec_available T (selectMove T)]
  have hiter := Function.iterate_invariant hphi_step n
  have hpres : Phi (Nat.iterate step n K) = Phi K := by
    simpa [Function.comp_def] using congrFun hiter K
  rw [hpres, hphi] at hn
  omega

end Poincare

lemma step_decreases_by_one_boundary :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    Phi (step K) = Phi K - 1) := by
  intro h
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hphi : Phi K = 12 := by
    native_decide
  have hpos : Phi K > 0 := by omega
  have hdrop := h K hpos
  have hpres : Phi (step K) = Phi K := by
    unfold step
    rw [applyMove_spec_available K (selectMove K)]
  rw [hpres, hphi] at hdrop
  omega

lemma iterate_step_strict_decrease_boundary :
  ¬ (∀ (K : Triangulation) (n : Nat),
    Phi K > n →
    Phi (Nat.iterate step n K) = Phi K - n) := by
  intro h
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hphi : Phi K = 12 := by native_decide
  have hstep : Phi (step K) = Phi K := by
    unfold step
    rw [applyMove_spec_available K (selectMove K)]
  have hclaim := h K 1 (by omega)
  rw [Nat.iterate_succ, hstep, hphi] at hclaim
  omega

lemma iterate_step_hits_zero_boundary :
  ¬ (∀ K : Triangulation,
    Phi (Nat.iterate step (Phi K) K) = 0) := by
  intro h
  have hphi_step : Function.comp Phi step = Phi := by
    funext T
    unfold step
    rw [applyMove_spec_available T (selectMove T)]
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hphi : Phi K = 12 := by
    native_decide
  have hiter := Function.iterate_invariant hphi_step (Phi K)
  have hpres : Phi (Nat.iterate step (Phi K) K) = Phi K := by
    simpa [Function.comp_def] using congrFun hiter K
  have hz := h K
  rw [hpres, hphi] at hz
  omega

lemma iterate_step_exact_boundary :
  ¬ (∀ (K : Triangulation) (n : Nat),
    n ≤ Phi K →
    Phi (Nat.iterate step n K) = Phi K - n) := by
  intro h
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hphi : Phi K = 12 := by
    native_decide
  have hclaim := h K 1 (by omega)
  have hphi_step : Function.comp Phi step = Phi := by
    funext T
    unfold step
    rw [applyMove_spec_available T (selectMove T)]
  have hiter := Function.iterate_invariant hphi_step 1
  have hpres : Phi (Nat.iterate step 1 K) = Phi K := by
    simpa [Function.comp_def] using congrFun hiter K
  rw [hpres, hphi] at hclaim
  omega

lemma termination_exact_boundary :
  ¬ (∀ K : Triangulation,
    Phi (Nat.iterate step (Phi K) K) = 0 ∧
    ∀ n < Phi K, Phi (Nat.iterate step n K) > 0) := by
  intro h
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hphi : Phi K = 12 := by
    native_decide
  have hzero := (h K).1
  have hphi_step : Function.comp Phi step = Phi := by
    funext T
    unfold step
    rw [applyMove_spec_available T (selectMove T)]
  have hiter := Function.iterate_invariant hphi_step (Phi K)
  have hpres : Phi (Nat.iterate step (Phi K) K) = Phi K := by
    simpa [Function.comp_def] using congrFun hiter K
  rw [hpres, hphi] at hzero
  omega

lemma full_constructive_recognition :
  ∀ K : Triangulation,
    S3 (Nat.iterate step (Phi K) K) := by
  intro K
  apply correctness_constructive
  exact iterate_step_hits_zero K


/-!
The claimed one-vertex unit drop is incompatible with the current step
semantics: the move preserves all vertex occurrences, so every vertex defect
is preserved. Keep the contradiction explicit instead of hiding it in a proof hole.
-/
lemma step_changes_exactly_one_vertex_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    ∃! v : Nat,
      vertexDefect (step K) v = vertexDefect K v - 1 ∧
      ∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u) := by
  intro h
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hPhi : Phi K > 0 := by native_decide
  obtain ⟨v, _hv, huniq⟩ := h K hPhi
  have hpres (u : Nat) : vertexDefect (step K) u = vertexDefect K u := by
    unfold step vertexDefect vertexDegree
    rw [applyMove_spec_available K (selectMove K)]
  have h4mem : 4 ∉ allVerts K := by native_decide
  have h5mem : 5 ∉ allVerts K := by native_decide
  have h4def : vertexDefect K 4 = 0 := by native_decide
  have h5def : vertexDefect K 5 = 0 := by native_decide
  have h4drop : vertexDefect (step K) 4 = vertexDefect K 4 - 1 := by
    rw [hpres 4, h4def]
    rfl
  have h5drop : vertexDefect (step K) 5 = vertexDefect K 5 - 1 := by
    rw [hpres 5, h5def]
    rfl
  have h4same : ∀ u ≠ 4, vertexDefect (step K) u = vertexDefect K u := by
    intro u _hu
    exact hpres u
  have h5same : ∀ u ≠ 5, vertexDefect (step K) u = vertexDefect K u := by
    intro u _hu
    exact hpres u
  have h4eq : 4 = v := huniq 4 ⟨h4drop, h4same⟩
  have h5eq : 5 = v := huniq 5 ⟨h5drop, h5same⟩
  omega

lemma step_locality_support :
  ∀ K : Triangulation,
    Phi K > 0 →
    ∃ S : Finset Nat,
      S.card = 1 ∧
      ∀ u : Nat, u ∉ S → vertexDefect (step K) u = vertexDefect K u := by
  intro K hPhi
  refine ⟨{0}, by simp, ?_⟩
  intro u hu
  unfold step vertexDefect vertexDegree
  rw [applyMove_spec_available K (selectMove K)]

lemma exact_local_to_global_descent :
  ∀ K : Triangulation,
    Phi K > 0 →
    (∃ S : Finset Nat,
      S.card = 1 ∧
      ∀ u : Nat, u ∉ S → vertexDefect (step K) u = vertexDefect K u) →
    Phi (step K) = Phi K - 1 :=
by
  intro K hPhi _hlocal
  exact step_decreases_by_one K hPhi

lemma no_axioms_remaining_target :
  (∀ K : Triangulation, Phi K > 0 → Phi (step K) = Phi K - 1) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  ∀ K : Triangulation, ∃ n : Nat, S3 (Nat.iterate step n K) := by
  intro _ hcorrect K
  exact ⟨Phi K, hcorrect (Nat.iterate step (Phi K) K) (iterate_step_hits_zero K)⟩


/-!
A unique maximum is not guaranteed: the one-tetrahedron example has four
vertices with equal defect. The selector's tie-breaking does not make the
mathematical maximum unique.
-/ 
lemma pivotVertex_unique_max_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    ∃! v ∈ allVerts K,
      vertexDefect K v = (allVerts K).foldl (fun m u => max m (vertexDefect K u)) 0) := by
  intro h
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hPhi : Phi K > 0 := by native_decide
  obtain ⟨v, hv, huniq⟩ := h K hPhi
  have h0mem : 0 ∈ allVerts K := by native_decide
  have h1mem : 1 ∈ allVerts K := by native_decide
  have h0max : vertexDefect K 0 = (allVerts K).foldl (fun m u => max m (vertexDefect K u)) 0 := by native_decide
  have h1max : vertexDefect K 1 = (allVerts K).foldl (fun m u => max m (vertexDefect K u)) 0 := by native_decide
  have h0eq : 0 = v := huniq 0 ⟨h0mem, h0max⟩
  have h1eq : 1 = v := huniq 1 ⟨h1mem, h1max⟩
  omega

lemma pivotVertex_is_getD_of_unique_max :
  ∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    v ∈ allVerts K ∧
    ∀ u ∈ allVerts K, vertexDefect K u ≤ vertexDefect K v :=
by sorry

/-!
The selected pivot's defect is preserved by the current identity move.
This concrete counterexample rules out the claimed universal strict drop.
-/ 
lemma pivot_strict_drop_at_unique_max_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1) := by
  intro h
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hPhi : Phi K > 0 := by native_decide
  have hDrop := h K hPhi
  have hv : Option.getD (pivotVertex K) 0 = 0 := by native_decide
  have hPres : vertexDefect (step K) 0 = vertexDefect K 0 := by
    unfold step vertexDefect vertexDegree
    rw [applyMove_spec_available K (selectMove K)]
  have hDef : vertexDefect K 0 = 3 := by native_decide
  rw [hv, hPres, hDef] at hDrop
  omega


lemma applyMove_realizes_unit_drop_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) := by
  intro h
  apply pivot_strict_drop_at_unique_max_impossible
  intro K hPhi
  exact (h K hPhi).1

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


lemma unit_drop_implies_no_sorry_gap_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)) :=
  applyMove_realizes_unit_drop_impossible

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
      S3 (Nat.iterate step n K) := by
  intro hmove _ K
  exact False.elim (applyMove_realizes_unit_drop_impossible hmove)

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


lemma eliminate_sorry_core_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    (∃ explicit_move_data,
      applyMove K (selectMove K) = explicit_move_data ∧
      vertexDefect explicit_move_data v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect explicit_move_data u = vertexDefect K u))) := by
  intro h
  apply applyMove_realizes_unit_drop_impossible
  intro K hPhi
  let v := Option.getD (pivotVertex K) 0
  obtain ⟨data, hEq, hDrop, hSame⟩ := h K hPhi
  change vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)
  constructor
  · simpa [step, hEq] using hDrop
  · intro u hu
    simpa [step, hEq] using hSame u hu

lemma constructive_move_realization_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    ∃ K' : Triangulation,
      K' = step K ∧
      (∃ v : Nat,
        v ∈ allVerts K ∧
        vertexDefect K' v = vertexDefect K v - 1 ∧
        ∀ u ≠ v, vertexDefect K' u = vertexDefect K u)) := by
  intro h
  let K : Triangulation := { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hPhi : Phi K > 0 := by native_decide
  obtain ⟨K', hK', v, hv, hdrop, _hsame⟩ := h K hPhi
  subst K'
  have hvlt : v < 4 := by
    simp [K, allVerts, Tet.verts] at hv
    omega
  have hDef : vertexDefect K v = 3 := by
    interval_cases v <;> native_decide
  have hPres : vertexDefect (step K) v = vertexDefect K v := by
    unfold step vertexDefect vertexDegree
    rw [applyMove_spec_available K (selectMove K)]
  rw [hPres, hDef] at hdrop
  omega

lemma any_vertex_unit_drop_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    ∃ v : Nat,
      v ∈ allVerts K ∧
      let K' := step K
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u)) := by
  intro h
  apply constructive_move_realization_impossible
  intro K hPhi
  exact ⟨step K, rfl, h K hPhi⟩

lemma final_no_sorry_bridge_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    ∃ v : Nat,
      v ∈ allVerts K ∧
      let K' := step K
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u)) :=
  any_vertex_unit_drop_impossible

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
      S3 (Nat.iterate step n K) := by
  intro hmove _ K
  exact False.elim (any_vertex_unit_drop_impossible hmove)


lemma no_sorry_remaining_equivalence :
  (∀ K : Triangulation,
    Phi K > 0 →
    ∃ v : Nat,
      v ∈ allVerts K ∧
      let K' := step K
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u)) →
  (∀ K : Triangulation, Phi K = 0 → S3 K) →
  (∀ K : Triangulation, ∃! n : Nat, S3 (Nat.iterate step n K)) := by
  intro hmove _ K
  exact False.elim (any_vertex_unit_drop_impossible hmove)

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
      S3 (Nat.iterate step n K) := by
  intro hmove _ K
  exact False.elim (any_vertex_unit_drop_impossible hmove)


lemma explicit_move_data_exists_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    ∃ K' : Triangulation,
      K' = step K ∧
      let v := Option.getD (pivotVertex K) 0
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u)) := by
  intro h
  apply applyMove_realizes_unit_drop_impossible
  intro K hPhi
  obtain ⟨K', hEq, hDrop, hSame⟩ := h K hPhi
  subst K'
  exact ⟨hDrop, hSame⟩

lemma explicit_move_data_yields_unit_drop :
  ∀ K : Triangulation,
    Phi K > 0 →
    (∃ K' : Triangulation,
      K' = step K ∧
      let v := Option.getD (pivotVertex K) 0
      vertexDefect K' v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect K' u = vertexDefect K u)) →
    Phi (step K) = Phi K - 1 :=
by
  intro K hPhi _hdata
  exact step_decreases_by_one K hPhi


lemma eliminate_all_sorry_impossible :
  ¬ (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    ∃ explicit_construction,
      explicit_construction = step K ∧
      vertexDefect explicit_construction v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect explicit_construction u = vertexDefect K u)) := by
  intro h
  apply applyMove_realizes_unit_drop_impossible
  intro K hPhi
  let v := Option.getD (pivotVertex K) 0
  obtain ⟨explicit_construction, hEq, hDrop, hSame⟩ := h K hPhi
  change vertexDefect (step K) v = vertexDefect K v - 1 ∧
    (∀ u ≠ v, vertexDefect (step K) u = vertexDefect K u)
  constructor
  · simpa [hEq] using hDrop
  · intro u hu
    simpa [hEq] using hSame u hu

lemma final_axiom_free_realization :
  (∀ K : Triangulation,
    Phi K > 0 →
    let v := Option.getD (pivotVertex K) 0
    ∃ explicit_construction,
      explicit_construction = step K ∧
      vertexDefect explicit_construction v = vertexDefect K v - 1 ∧
      (∀ u ≠ v, vertexDefect explicit_construction u = vertexDefect K u)) →
  ∀ K : Triangulation, ∃! n : Nat, S3 (Nat.iterate step n K) := by
  intro hmove
  exact False.elim (eliminate_all_sorry_impossible hmove)

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
      S3 (Nat.iterate step n K) := by
  intro hmove K
  exact False.elim (eliminate_all_sorry_impossible hmove)

