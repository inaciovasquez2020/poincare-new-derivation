import Poincare.GlobalPhiSupportDegreeGap
import Mathlib.Tactic

namespace Poincare

open scoped BigOperators

private theorem sum_list_counts_eq_length
    (xs : List Nat) (s : Finset Nat)
    (hcover : ∀ v ∈ xs, v ∈ s) :
    (∑ v ∈ s, xs.count v) = xs.length := by
  induction xs with
  | nil =>
      simp
  | cons a xs ih =>
      have ha : a ∈ s := hcover a (by simp)
      have hxs : ∀ v ∈ xs, v ∈ s := by
        intro v hv
        exact hcover v (by simp [hv])
      have hsumOne :
          (∑ v ∈ s, if (a == v) = true then (1 : Nat) else 0) = 1 := by
        simpa [beq_iff_eq, ha] using
          (Finset.sum_ite_eq s a (fun _ : Nat => (1 : Nat)))
      calc
        (∑ v ∈ s, (a :: xs).count v) =
            (∑ v ∈ s, xs.count v) +
              (∑ v ∈ s, if (a == v) = true then (1 : Nat) else 0) := by
                simp only [List.count_cons, Finset.sum_add_distrib]
        _ = xs.length + 1 := by rw [ih hxs, hsumOne]
        _ = (a :: xs).length := by simp

private theorem flatMap_tet_verts_length (ts : List Tet) :
    (ts.flatMap Tet.verts).length = 4 * ts.length := by
  induction ts with
  | nil => simp
  | cons tau rest ih =>
      simp [List.flatMap_cons, Tet.verts, ih] <;> omega

private theorem sum_vertexDegrees_eq_four_mul_tets
    (K : Triangulation) :
    (∑ v ∈ (vertexSupport K).toFinset, vertexDegree K v) =
      4 * K.tets.length := by
  have hset :
      (vertexSupport K).toFinset = (allVerts K).toFinset := by
    ext v
    simp only [List.mem_toFinset]
    exact mem_vertexSupport_iff K v
  calc
    (∑ v ∈ (vertexSupport K).toFinset, vertexDegree K v) =
        (∑ v ∈ (allVerts K).toFinset, (allVerts K).count v) := by
          rw [hset]
          rfl
    _ = (allVerts K).length := by
          apply sum_list_counts_eq_length
          intro v hv
          exact List.mem_toFinset.mpr hv
    _ = 4 * K.tets.length := by
          simpa [allVerts] using flatMap_tet_verts_length K.tets

/-- Exact incidence bookkeeping for a closed triangulation core.
This is a counting identity, not a claim that a descending Pachner path exists. -/
theorem ClosedTriangulationCore.PhiSupport_eq_four_mul_tets_sub_vertices
    {K : Triangulation} (hcore : ClosedTriangulationCore K) :
    PhiSupport K = 4 * (K.tets.length - (vertexSupport K).length) := by
  let s : Finset Nat := (vertexSupport K).toFinset
  have hnodup : (vertexSupport K).Nodup := by
    unfold vertexSupport
    exact eraseDups_nodup_nat (allVerts K)
  have hcard : s.card = (vertexSupport K).length := by
    simpa [s] using List.toFinset_card_of_nodup hnodup
  have hdefect :
      ∀ v ∈ s, vertexDefect K v + 4 = vertexDegree K v := by
    intro v hv
    have hge : 4 ≤ vertexDegree K v :=
      hcore.vertexDegree_ge_four_of_mem_vertexSupport
        (List.mem_toFinset.mp hv)
    have hnonneg :
        (0 : Int) ≤ (vertexDegree K v : Int) - 4 := by
      omega
    have habs :=
      Int.natAbs_of_nonneg hnonneg
    unfold vertexDefect targetDegree
    omega
  have hsum :
      (∑ v ∈ s, vertexDefect K v) + 4 * s.card =
        (∑ v ∈ s, vertexDegree K v) := by
    calc
      (∑ v ∈ s, vertexDefect K v) + 4 * s.card =
          (∑ v ∈ s, (vertexDefect K v + 4)) := by
            simp [Finset.sum_add_distrib, mul_comm]
      _ = (∑ v ∈ s, vertexDegree K v) :=
        Finset.sum_congr rfl hdefect
  have hcount :
      PhiSupport K + 4 * (vertexSupport K).length =
        4 * K.tets.length := by
    calc
      PhiSupport K + 4 * (vertexSupport K).length =
          (∑ v ∈ s, vertexDefect K v) + 4 * s.card := by
            rw [phiSupport_eq_finset_sum K, hcard]
      _ = (∑ v ∈ s, vertexDegree K v) := hsum
      _ = 4 * K.tets.length := sum_vertexDegrees_eq_four_mul_tets K
  omega

end Poincare
