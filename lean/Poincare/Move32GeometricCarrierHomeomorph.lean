import Poincare.Move32UnchangedOverlap
import Mathlib.Topology.Separation.Hausdorff

open Set

namespace Poincare

theorem ClosedTriangulationCore.move32Site_unchangedCarrier_subset_source_space
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    s.unchangedGeometricCarrier K ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  rw [(hcore.move32Site_global_region_decomposition s hlegal).1]
  exact subset_union_right

theorem ClosedTriangulationCore.move32Site_unchangedCarrier_subset_target_space
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    s.unchangedGeometricCarrier K ⊆
      (triangulationTopologicalGeometricComplex (s.replace K)).space := by
  rw [(hcore.move32Site_global_region_decomposition s hlegal).2]
  exact subset_union_right

private noncomputable def move32GeometricCarrierForward
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    triangulationTopologicalGeometricCarrier K →
      triangulationTopologicalGeometricCarrier (s.replace K) := by
  classical
  exact fun p ↦
  dite (p.1 ∈ move23PiTargetLocalCarrier s.a s.b s.c s.d s.e)
    (fun hpS ↦
      ⟨((move23PiLocalHomeomorph
        (hcore.move32Site_distinct s hlegal.1)).symm
          ⟨p.1, hpS⟩).1,
        s.sourceLocalCarrier_subset_replace_geometricCarrier K
          ((move23PiLocalHomeomorph
            (hcore.move32Site_distinct s hlegal.1)).symm
              ⟨p.1, hpS⟩).2⟩)
    (fun hpS ↦ ⟨p.1, hcore.move32Site_unchangedCarrier_subset_target_space s hlegal (by
      have hp := (Set.ext_iff.mp
        (hcore.move32Site_global_region_decomposition s hlegal).1 p.1).mp p.2
      exact hp.resolve_left hpS)⟩)

private noncomputable def move32GeometricCarrierBackward
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    triangulationTopologicalGeometricCarrier (s.replace K) →
      triangulationTopologicalGeometricCarrier K := by
  classical
  exact fun q ↦
  dite (q.1 ∈ move23PiSourceLocalCarrier s.a s.b s.c s.d s.e)
    (fun hqT ↦
      ⟨(move23PiLocalHomeomorph
        (hcore.move32Site_distinct s hlegal.1)
          ⟨q.1, hqT⟩).1,
        s.targetLocalCarrier_subset_geometricCarrier hlegal.1
          (move23PiLocalHomeomorph
            (hcore.move32Site_distinct s hlegal.1)
              ⟨q.1, hqT⟩).2⟩)
    (fun hqT ↦ ⟨q.1, hcore.move32Site_unchangedCarrier_subset_source_space s hlegal (by
      have hq := (Set.ext_iff.mp
        (hcore.move32Site_global_region_decomposition s hlegal).2 q.1).mp q.2
      exact hq.resolve_left hqT)⟩)

private theorem move32GeometricCarrierForward_apply_eq_local
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (p : triangulationTopologicalGeometricCarrier K)
    (hpS : p.1 ∈ move23PiTargetLocalCarrier s.a s.b s.c s.d s.e) :
    (move32GeometricCarrierForward hcore s hlegal p).1 =
      ((move23PiLocalHomeomorph
        (hcore.move32Site_distinct s hlegal.1)).symm
          ⟨p.1, hpS⟩).1 := by
  simp [move32GeometricCarrierForward, hpS]

private theorem move32GeometricCarrierForward_apply_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (p : triangulationTopologicalGeometricCarrier K)
    (hpU : p.1 ∈ s.unchangedGeometricCarrier K) :
    (move32GeometricCarrierForward hcore s hlegal p).1 = p.1 := by
  by_cases hpS : p.1 ∈ move23PiTargetLocalCarrier s.a s.b s.c s.d s.e
  · rw [move32GeometricCarrierForward_apply_eq_local hcore s hlegal p hpS]
    exact hcore.move32LocalInverse_apply_eq_self_of_mem_unchanged s hlegal ⟨p.1, hpS⟩ hpU
  · simp [move32GeometricCarrierForward, hpS]

private theorem move32GeometricCarrierBackward_apply_eq_local
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (q : triangulationTopologicalGeometricCarrier (s.replace K))
    (hqT : q.1 ∈ move23PiSourceLocalCarrier s.a s.b s.c s.d s.e) :
    (move32GeometricCarrierBackward hcore s hlegal q).1 =
      (move23PiLocalHomeomorph
        (hcore.move32Site_distinct s hlegal.1)
          ⟨q.1, hqT⟩).1 := by
  simp [move32GeometricCarrierBackward, hqT]

private theorem move32GeometricCarrierBackward_apply_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (q : triangulationTopologicalGeometricCarrier (s.replace K))
    (hqU : q.1 ∈ s.unchangedGeometricCarrier K) :
    (move32GeometricCarrierBackward hcore s hlegal q).1 = q.1 := by
  by_cases hqT : q.1 ∈ move23PiSourceLocalCarrier s.a s.b s.c s.d s.e
  · rw [move32GeometricCarrierBackward_apply_eq_local hcore s hlegal q hqT]
    exact hcore.move32LocalForward_apply_eq_self_of_mem_unchanged s hlegal ⟨q.1, hqT⟩ hqU
  · simp [move32GeometricCarrierBackward, hqT]

private theorem move32GeometricCarrierForward_continuous
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    Continuous (move32GeometricCarrierForward hcore s hlegal) := by
  let S' : Set (triangulationTopologicalGeometricCarrier K) :=
    {p | p.1 ∈ move23PiTargetLocalCarrier s.a s.b s.c s.d s.e}
  let U' : Set (triangulationTopologicalGeometricCarrier K) :=
    {p | p.1 ∈ s.unchangedGeometricCarrier K}
  have hSclosed : IsClosed S' :=
    (move23PiTargetLocalCarrier_isClosed s.a s.b s.c s.d s.e).preimage
      continuous_subtype_val
  have hUclosed : IsClosed U' :=
    (s.unchangedGeometricCarrier_isClosed K).preimage continuous_subtype_val
  have hScont : ContinuousOn (move32GeometricCarrierForward hcore s hlegal) S' := by
    rw [continuousOn_iff_continuous_restrict]
    let localIn : S' → ↥(move23PiTargetLocalCarrier s.a s.b s.c s.d s.e) :=
      fun p ↦ ⟨p.1.1, p.2⟩
    let localOut : ↥(move23PiSourceLocalCarrier s.a s.b s.c s.d s.e) →
        triangulationTopologicalGeometricCarrier (s.replace K) := fun q ↦
      ⟨q.1, s.sourceLocalCarrier_subset_replace_geometricCarrier K q.2⟩
    have hin : Continuous localIn :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    have hout : Continuous localOut :=
      Continuous.subtype_mk continuous_subtype_val _
    have hcomp : Continuous (localOut ∘
        (move23PiLocalHomeomorph
          (hcore.move32Site_distinct s hlegal.1)).symm ∘ localIn) :=
      hout.comp ((move23PiLocalHomeomorph
        (hcore.move32Site_distinct s hlegal.1)).symm.continuous.comp hin)
    convert hcomp using 1
    funext p
    apply Subtype.ext
    exact move32GeometricCarrierForward_apply_eq_local hcore s hlegal p.1 p.2
  have hUcont : ContinuousOn (move32GeometricCarrierForward hcore s hlegal) U' := by
    rw [continuousOn_iff_continuous_restrict]
    let unchangedOut : U' →
        triangulationTopologicalGeometricCarrier (s.replace K) := fun p ↦
      ⟨p.1.1, hcore.move32Site_unchangedCarrier_subset_target_space s hlegal p.2⟩
    have hc : Continuous unchangedOut :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    convert hc using 1
    funext p
    apply Subtype.ext
    exact move32GeometricCarrierForward_apply_eq_self_of_mem_unchanged hcore s hlegal p.1 p.2
  have hcover : S' ∪ U' = Set.univ := by
    ext p
    simp only [S', U', mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact (Set.ext_iff.mp
      (hcore.move32Site_global_region_decomposition s hlegal).1 p.1).mp p.2
  have h := hScont.union_of_isClosed hUcont hSclosed hUclosed
  rw [hcover] at h
  exact continuousOn_univ.mp h

private theorem move32GeometricCarrierBackward_forward
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) (p) :
    move32GeometricCarrierBackward hcore s hlegal
        (move32GeometricCarrierForward hcore s hlegal p) = p := by
  apply Subtype.ext
  by_cases hpS : p.1 ∈ move23PiTargetLocalCarrier s.a s.b s.c s.d s.e
  · have hFT : (move32GeometricCarrierForward hcore s hlegal p).1 ∈
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e := by
      rw [move32GeometricCarrierForward_apply_eq_local hcore s hlegal p hpS]
      exact ((move23PiLocalHomeomorph
        (hcore.move32Site_distinct s hlegal.1)).symm ⟨p.1, hpS⟩).2
    rw [move32GeometricCarrierBackward_apply_eq_local hcore s hlegal _ hFT]
    have heq : ⟨(move32GeometricCarrierForward hcore s hlegal p).1, hFT⟩ =
        (move23PiLocalHomeomorph
          (hcore.move32Site_distinct s hlegal.1)).symm ⟨p.1, hpS⟩ := by
      apply Subtype.ext
      exact move32GeometricCarrierForward_apply_eq_local hcore s hlegal p hpS
    rw [heq, (move23PiLocalHomeomorph
      (hcore.move32Site_distinct s hlegal.1)).apply_symm_apply]
  · have hpU : p.1 ∈ s.unchangedGeometricCarrier K := by
      have hp := (Set.ext_iff.mp
        (hcore.move32Site_global_region_decomposition s hlegal).1 p.1).mp p.2
      exact hp.resolve_left hpS
    rw [move32GeometricCarrierBackward_apply_eq_self_of_mem_unchanged hcore s hlegal _ (by
      simpa [move32GeometricCarrierForward_apply_eq_self_of_mem_unchanged hcore s hlegal p hpU] using hpU)]
    exact move32GeometricCarrierForward_apply_eq_self_of_mem_unchanged hcore s hlegal p hpU

private theorem move32GeometricCarrierForward_backward
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) (q) :
    move32GeometricCarrierForward hcore s hlegal
        (move32GeometricCarrierBackward hcore s hlegal q) = q := by
  apply Subtype.ext
  by_cases hqT : q.1 ∈ move23PiSourceLocalCarrier s.a s.b s.c s.d s.e
  · have hGS : (move32GeometricCarrierBackward hcore s hlegal q).1 ∈
        move23PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
      rw [move32GeometricCarrierBackward_apply_eq_local hcore s hlegal q hqT]
      exact (move23PiLocalHomeomorph
        (hcore.move32Site_distinct s hlegal.1) ⟨q.1, hqT⟩).2
    rw [move32GeometricCarrierForward_apply_eq_local hcore s hlegal _ hGS]
    have heq : ⟨(move32GeometricCarrierBackward hcore s hlegal q).1, hGS⟩ =
        move23PiLocalHomeomorph
          (hcore.move32Site_distinct s hlegal.1) ⟨q.1, hqT⟩ := by
      apply Subtype.ext
      exact move32GeometricCarrierBackward_apply_eq_local hcore s hlegal q hqT
    rw [heq, (move23PiLocalHomeomorph
      (hcore.move32Site_distinct s hlegal.1)).symm_apply_apply]
  · have hqU : q.1 ∈ s.unchangedGeometricCarrier K := by
      have hq := (Set.ext_iff.mp
        (hcore.move32Site_global_region_decomposition s hlegal).2 q.1).mp q.2
      exact hq.resolve_left hqT
    rw [move32GeometricCarrierForward_apply_eq_self_of_mem_unchanged hcore s hlegal _ (by
      simpa [move32GeometricCarrierBackward_apply_eq_self_of_mem_unchanged hcore s hlegal q hqU] using hqU)]
    exact move32GeometricCarrierBackward_apply_eq_self_of_mem_unchanged hcore s hlegal q hqU

noncomputable def ClosedTriangulationCore.move32GeometricCarrierHomeomorph
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier (s.replace K) := by
  letI : T2Space (Nat → ℝ) := Pi.t2Space
  letI : T2Space (triangulationTopologicalGeometricCarrier (s.replace K)) :=
    T2Space.of_injective_continuous Subtype.val_injective continuous_subtype_val
  let F := move32GeometricCarrierForward hcore s hlegal
  have hbij : Function.Bijective F := ⟨
    fun p q hpq ↦ by
      rw [← move32GeometricCarrierBackward_forward hcore s hlegal p,
        ← move32GeometricCarrierBackward_forward hcore s hlegal q]
      exact congrArg (move32GeometricCarrierBackward hcore s hlegal) hpq,
    fun q ↦ ⟨move32GeometricCarrierBackward hcore s hlegal q,
      move32GeometricCarrierForward_backward hcore s hlegal q⟩⟩
  exact IsHomeomorph.homeomorph F
    ((isHomeomorph_iff_continuous_bijective).2
      ⟨move32GeometricCarrierForward_continuous hcore s hlegal, hbij⟩)

theorem ClosedTriangulationCore.move32GeometricCarrierHomeomorph_apply_eq_local
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (p : triangulationTopologicalGeometricCarrier K)
    (hpS : p.1 ∈ move23PiTargetLocalCarrier s.a s.b s.c s.d s.e) :
    (hcore.move32GeometricCarrierHomeomorph s hlegal p).1 =
      ((move23PiLocalHomeomorph
        (hcore.move32Site_distinct s hlegal.1)).symm
          ⟨p.1, hpS⟩).1 := by
  simpa [ClosedTriangulationCore.move32GeometricCarrierHomeomorph] using
    move32GeometricCarrierForward_apply_eq_local hcore s hlegal p hpS

theorem ClosedTriangulationCore.move32GeometricCarrierHomeomorph_apply_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (p : triangulationTopologicalGeometricCarrier K)
    (hpU : p.1 ∈ s.unchangedGeometricCarrier K) :
    (hcore.move32GeometricCarrierHomeomorph s hlegal p).1 = p.1 := by
  simpa [ClosedTriangulationCore.move32GeometricCarrierHomeomorph] using
    move32GeometricCarrierForward_apply_eq_self_of_mem_unchanged hcore s hlegal p hpU

theorem ClosedTriangulationCore.move32GeometricCarrierHomeomorph_symm_apply_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (q : triangulationTopologicalGeometricCarrier (s.replace K))
    (hqU : q.1 ∈ s.unchangedGeometricCarrier K) :
    ((hcore.move32GeometricCarrierHomeomorph s hlegal).symm q).1 = q.1 := by
  have heq : (hcore.move32GeometricCarrierHomeomorph s hlegal).symm q =
      move32GeometricCarrierBackward hcore s hlegal q := by
    apply (hcore.move32GeometricCarrierHomeomorph s hlegal).injective
    rw [(hcore.move32GeometricCarrierHomeomorph s hlegal).apply_symm_apply]
    exact (move32GeometricCarrierForward_backward hcore s hlegal q).symm
  rw [heq]
  exact move32GeometricCarrierBackward_apply_eq_self_of_mem_unchanged hcore s hlegal q hqU

end Poincare
