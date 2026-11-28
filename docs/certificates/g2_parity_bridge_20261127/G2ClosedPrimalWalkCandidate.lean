/-!
Append to a TEMPORARY COPY of
research/candidates/G2PiecewisePrimalLoopCancellation.lean
at PR #200 head 36df38d563014164bf288d17448255de4817abb8.
Add `import Poincare.CarrierPolygonalPath` in that copy's import block.

Independently reconstructs the finite ordered path partition; does not import
or assume the earlier inaccessible OrderedCarrierPartition.lean. The final
statement takes only actual simple connectivity, a triangle cocycle, and a
nonempty closed primal walk with distinct successive vertices and represented
edge cofaces. No partition or null-homotopy is assumed.

STATUS: NOT_RUN. This is candidate source, NOT a Lean certificate.
Pinned Mathlib: 05c4d64fa23b17a64c9ad4c53778102319544ac6.
No repository writes or dependency changes.
-/

namespace Poincare

open scoped unitInterval

private noncomputable def g2PartitionHalf (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

private noncomputable def g2PartitionSecond (t : unitInterval) : unitInterval :=
  ⟨((t : ℝ) + 1) / 2, by
    constructor <;> linarith [t.property.1, t.property.2]⟩

private theorem g2Partition_trans_left
    {X : Type*} [TopologicalSpace X] {a b c : X}
    (f : Path a b) (g : Path b c) (t : unitInterval) :
    (f.trans g) (g2PartitionHalf t) = f t := by
  rw [Path.trans_apply]
  split_ifs with h
  · apply congrArg (fun u : unitInterval => f u)
    apply Subtype.ext
    change 2 * ((t : ℝ) / 2) = (t : ℝ)
    ring
  · exfalso
    apply h
    change (t : ℝ) / 2 ≤ 1 / 2
    linarith [t.property.2]

private theorem g2Partition_trans_right
    {X : Type*} [TopologicalSpace X] {a b c : X}
    (f : Path a b) (g : Path b c) (t : unitInterval) :
    (f.trans g) (g2PartitionSecond t) = g t := by
  rw [Path.trans_apply]
  split_ifs with h
  · have ht : (t : ℝ) = 0 := by
      change ((t : ℝ) + 1) / 2 ≤ 1 / 2 at h
      linarith [t.property.1]
    have ht0 : t = 0 := by
      apply Subtype.ext
      exact ht
    calc
      _ = f 1 := by
        apply congrArg (fun u : unitInterval => f u)
        apply Subtype.ext
        change 2 * (((t : ℝ) + 1) / 2) = 1
        linarith
      _ = b := f.target
      _ = g t := by rw [ht0, g.source]
  · apply congrArg (fun u : unitInterval => g u)
    apply Subtype.ext
    change 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ)
    ring

/-- Finite nonempty composable path sequence, with an exact ordered partition.
The interval coverage includes both endpoints, even at the concatenation seam. -/
private theorem g2Partition_succ
    {X : Type*} [TopologicalSpace X]
    (p : Nat → X) (arc : ∀ k, Path (p k) (p (k+1))) (n : Nat) :
    ∃ f : Path (p 0) (p (n+1)), ∃ time : Nat → unitInterval,
      time 0 = 0 ∧ time (n+1) = 1 ∧
      (∀ k, k < n+1 → (time k : ℝ) < (time (k+1) : ℝ)) ∧
      (∀ k, k ≤ n+1 → f (time k) = p k) ∧
      (∀ k, k < n+1 → ∀ q : unitInterval,
        (time k : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ (time (k+1) : ℝ) →
        ∃ r : unitInterval, f q = arc k r) := by
  induction n with
  | zero =>
    let time : Nat → unitInterval := fun k => if k = 0 then 0 else 1
    refine ⟨arc 0, time, ?_, ?_, ?_, ?_, ?_⟩
    · simp [time]
    · simp [time]
    · intro k hk
      have hk0 : k = 0 := by omega
      subst k
      norm_num [time]
    · intro k hk
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simpa [time] using (arc 0).source
      · simpa [time] using (arc 0).target
    · intro k hk q _ _
      have hk0 : k = 0 := by omega
      subst k
      exact ⟨q, rfl⟩
  | succ n ih =>
    obtain ⟨f, time, h0, h1, horder, hvisit, hcover⟩ := ih
    let time' : Nat → unitInterval := fun k =>
      if k ≤ n+1 then g2PartitionHalf (time k) else 1
    have htime (k : Nat) (hk : k ≤ n+1) :
        time' k = g2PartitionHalf (time k) := if_pos hk
    have hend : time' (n+2) = 1 := if_neg (by omega)
    have hseam : (time' (n+1) : ℝ) = 1 / 2 := by
      rw [htime (n+1) (by omega), h1]
      rfl
    refine ⟨f.trans (arc (n+1)), time', ?_, hend, ?_, ?_, ?_⟩
    · rw [htime 0 (by omega), h0]
      apply Subtype.ext
      change (0 : ℝ) / 2 = 0
      norm_num
    · intro k hk
      by_cases hkn : k < n+1
      · rw [htime k (by omega), htime (k+1) (by omega)]
        change (time k : ℝ) / 2 < (time (k+1) : ℝ) / 2
        linarith [horder k hkn]
      · have hk' : k = n+1 := by omega
        subst k
        rw [hseam, hend]
        norm_num
    · intro k hk
      by_cases hkn : k ≤ n+1
      · rw [htime k hkn, g2Partition_trans_left, hvisit k hkn]
      · have hk' : k = n+2 := by omega
        subst k
        rw [hend]
        exact (f.trans (arc (n+1))).target
    · intro k hk q hq0 hq1
      by_cases hkn : k < n+1
      · rw [htime k (by omega)] at hq0
        rw [htime (k+1) (by omega)] at hq1
        change (time k : ℝ) / 2 ≤ (q : ℝ) at hq0
        change (q : ℝ) ≤ (time (k+1) : ℝ) / 2 at hq1
        let t : unitInterval := ⟨2 * (q : ℝ), by
          constructor
          · linarith [q.property.1]
          · linarith [(time (k+1)).property.2]⟩
        have ht : g2PartitionHalf t = q := by
          apply Subtype.ext
          change (2 * (q : ℝ)) / 2 = (q : ℝ)
          ring
        obtain ⟨r, hr⟩ := hcover k hkn t
          (by change (time k : ℝ) ≤ 2 * (q : ℝ); linarith)
          (by change 2 * (q : ℝ) ≤ (time (k+1) : ℝ); linarith)
        refine ⟨r, ?_⟩
        calc
          _ = (f.trans (arc (n+1))) (g2PartitionHalf t) :=
            congrArg (fun u : unitInterval => (f.trans (arc (n+1))) u) ht.symm
          _ = f t := g2Partition_trans_left f (arc (n+1)) t
          _ = arc k r := hr
      · have hk' : k = n+1 := by omega
        subst k
        rw [hseam] at hq0
        let t : unitInterval := ⟨2 * (q : ℝ) - 1, by
          constructor <;> linarith [q.property.2]⟩
        have ht : g2PartitionSecond t = q := by
          apply Subtype.ext
          change ((2 * (q : ℝ) - 1) + 1) / 2 = (q : ℝ)
          ring
        refine ⟨t, ?_⟩
        calc
          _ = (f.trans (arc (n+1))) (g2PartitionSecond t) :=
            congrArg (fun u : unitInterval => (f.trans (arc (n+1))) u) ht.symm
          _ = arc (n+1) t := g2Partition_trans_right f (arc (n+1)) t

private theorem g2Partition_nonempty
    {X : Type*} [TopologicalSpace X]
    (p : Nat → X) (arc : ∀ k, Path (p k) (p (k+1)))
    (m : Nat) (hm : 0 < m) :
    ∃ f : Path (p 0) (p m), ∃ time : Nat → unitInterval,
      time 0 = 0 ∧ time m = 1 ∧
      (∀ k, k < m → (time k : ℝ) < (time (k+1) : ℝ)) ∧
      (∀ k, k ≤ m → f (time k) = p k) ∧
      (∀ k, k < m → ∀ q : unitInterval,
        (time k : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ (time (k+1) : ℝ) →
        ∃ r : unitInterval, f q = arc k r) := by
  cases m with
  | zero => omega
  | succ n => exact g2Partition_succ p arc n

/-- Actual carrier simple connectivity annihilates the pairing of a triangle
cocycle with a nonempty closed primal walk having distinct successive vertices.
Only coface membership of each edge is needed. All geometry is constructed. -/
theorem g2_closed_primal_walk_pairing_zero_candidate
    {K : Triangulation}
    (hSC : TriangulationRealizationSimplyConnected K)
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ u, w u u = 0)
    (hsym : ∀ u v, w u v = w v u)
    (htri : ∀ tau : Tet, tau ∈ K.tets → ∀ a b c : Nat,
      a ∈ tau.verts → b ∈ tau.verts → c ∈ tau.verts →
      w a b + w b c + w c a = 0)
    (m : Nat) (hm : 0 < m) (vertex : Nat → Nat)
    (hclosed : vertex m = vertex 0)
    (hdistinct : ∀ k, k < m → vertex k ≠ vertex (k+1))
    (hstep : ∀ k, k < m → ∃ tau : Tet, tau ∈ K.tets ∧
      vertex k ∈ tau.verts ∧ vertex (k+1) ∈ tau.verts) :
    (∑ k ∈ Finset.range m, w (vertex k) (vertex (k+1))) = 0 := by
  classical
  -- Extend the finite vertex word by its basepoint. The extension is not
  -- traversed, but gives a total Nat-indexed path sequence.
  let v : Nat → Nat := fun k => if k < m then vertex k else vertex 0
  have hv (k : Nat) (hk : k ≤ m) : v k = vertex k := by
    dsimp [v]
    split_ifs with h
    · rfl
    · have hkm : k = m := by omega
      simpa [hkm] using hclosed.symm
  have hcoface : ∀ k : Nat, ∃ tau : Tet, tau ∈ K.tets ∧
      v k ∈ tau.verts ∧ v (k+1) ∈ tau.verts := by
    intro k
    by_cases hk : k < m
    · obtain ⟨tau, ht, ha, hb⟩ := hstep k hk
      exact ⟨tau, ht, by rw [hv k (by omega)]; exact ha,
        by rw [hv (k+1) (by omega)]; exact hb⟩
    · obtain ⟨tau, ht, ha, _⟩ := hstep 0 hm
      have hk' : ¬ k+1 < m := by omega
      exact ⟨tau, ht, by simpa [v, hk] using ha,
        by simpa [v, hk'] using ha⟩
  choose tau htau using hcoface
  have hs (k : Nat) : v k ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau k, (htau k).1, (htau k).2.1⟩
  let p : Nat → triangulationTopologicalGeometricCarrier K :=
    fun k => triangulationTopologicalCarrierVertex K (v k) (hs k)
  have hp (k : Nat) (hk : k ≤ m) :
      (p k).1 = triangulationTopologicalGeometricVertex (vertex k) := by
    change triangulationTopologicalGeometricVertex (v k) = _
    rw [hv k hk]
  have hleft (k : Nat) :
      (p k).1 ∈ triangulationTopologicalTetBody (tau k) :=
    triangulationTopologicalGeometricVertex_mem_tetBody (htau k).2.1
  have hright (k : Nat) :
      (p (k+1)).1 ∈ triangulationTopologicalTetBody (tau k) :=
    triangulationTopologicalGeometricVertex_mem_tetBody (htau k).2.2
  let arc : ∀ k, Path (p k) (p (k+1)) := fun k =>
    carrierSegmentInTet K (tau k) (htau k).1 _ _ (hleft k) (hright k)
  have hpm : p m = p 0 := by
    apply Subtype.ext
    rw [hp m (by omega), hp 0 (by omega), hclosed]
  obtain ⟨f, time, h0, h1, horder, hvisit, hcover⟩ :=
    g2Partition_nonempty p arc m hm
  let loop : Path (p 0) (p 0) := f.cast rfl hpm.symm
  have hloop (t : unitInterval) : loop t = f t := rfl
  obtain ⟨H⟩ := exists_carrierLoopNullHomotopyData hSC loop
  apply g2_piecewise_primal_loop_pairing_zero H w hzero hsym htri
    m hm vertex time h0 h1 horder hdistinct
  · intro k hk
    rw [hloop, hvisit k hk, hp k hk]
  · intro k hk q hq0 hq1
    obtain ⟨t, ht⟩ := hcover k hk q hq0 hq1
    refine ⟨(t : ℝ), ?_⟩
    rw [hloop, ht]
    change (carrierSegmentInTet K (tau k) (htau k).1 _ _
      (hleft k) (hright k) t).1 = _
    rw [carrierSegmentInTet_coe, hp k (by omega), hp (k+1) (by omega)]

#print axioms g2Partition_nonempty
#print axioms g2_closed_primal_walk_pairing_zero_candidate

end Poincare
