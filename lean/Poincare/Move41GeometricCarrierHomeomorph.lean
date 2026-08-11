import Poincare.Move41GlobalRegionDecomposition
import Mathlib.Topology.Separation.Hausdorff

open Set

namespace Poincare

noncomputable def move41PiLocalHomeomorph
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) :
    ↥(move41PiSourceLocalCarrier a b c d e) ≃ₜ
      ↥(move41PiTargetLocalCarrier a b c d e) :=
  IsHomeomorph.homeomorph
    (fun p ↦ ⟨move41PiRadialMap a b c d e p.1,
      move41PiRadialMap_mem_target h p.2⟩)
    (move41PiRadialMap_isHomeomorph h)

private theorem move41PiLocalHomeomorph_apply_eq_self
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    (hpS : p ∈ move41PiSourceLocalCarrier a b c d e)
    (hfix : move41PiRadialMap a b c d e p = p) :
    (move41PiLocalHomeomorph h ⟨p, hpS⟩).1 = p := by
  exact hfix

private theorem move41PiLocalHomeomorph_symm_apply_eq_self
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    (hpT : p ∈ move41PiTargetLocalCarrier a b c d e)
    (hpS : p ∈ move41PiSourceLocalCarrier a b c d e) :
    ((move41PiLocalHomeomorph h).symm ⟨p, hpT⟩).1 = p := by
  have heq : move41PiLocalHomeomorph h ⟨p, hpS⟩ = ⟨p, hpT⟩ := by
    apply Subtype.ext
    exact move41PiRadialMap_eq_self_of_center_eq_zero hpS
      (move41PiTargetLocalCarrier_center_eq_zero h hpT)
  rw [← heq, (move41PiLocalHomeomorph h).symm_apply_apply]

private noncomputable def move41GeometricCarrierForward
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    triangulationTopologicalGeometricCarrier K →
      triangulationTopologicalGeometricCarrier (s.replace K) := by
  classical
  exact fun p ↦
  dite (p.1 ∈ move41PiSourceLocalCarrier s.a s.b s.c s.d s.e)
    (fun hpS ↦
      ⟨(move41PiLocalHomeomorph
        s.distinct
          ⟨p.1, hpS⟩).1,
        hcore.move41Site_targetLocalCarrier_subset_target_space s hlegal
          (move41PiLocalHomeomorph
            s.distinct
              ⟨p.1, hpS⟩).2⟩)
    (fun hpS ↦ ⟨p.1, hcore.move41Site_unchangedCarrier_subset_target_space s hlegal (by
      have hp := (Set.ext_iff.mp
        (hcore.move41Site_global_region_decomposition s hlegal).1 p.1).mp p.2
      exact hp.resolve_left hpS)⟩)

private noncomputable def move41GeometricCarrierBackward
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    triangulationTopologicalGeometricCarrier (s.replace K) →
      triangulationTopologicalGeometricCarrier K := by
  classical
  exact fun q ↦
  dite (q.1 ∈ move41PiTargetLocalCarrier s.a s.b s.c s.d s.e)
    (fun hqT ↦
      ⟨((move41PiLocalHomeomorph
        s.distinct).symm
          ⟨q.1, hqT⟩).1,
        hcore.move41Site_sourceLocalCarrier_subset_source_space s hlegal
          ((move41PiLocalHomeomorph
            s.distinct).symm
              ⟨q.1, hqT⟩).2⟩)
    (fun hqT ↦ ⟨q.1, hcore.move41Site_unchangedCarrier_subset_source_space s hlegal (by
      have hq := (Set.ext_iff.mp
        (hcore.move41Site_global_region_decomposition s hlegal).2 q.1).mp q.2
      exact hq.resolve_left hqT)⟩)

private theorem move41GeometricCarrierForward_apply_eq_local
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K)
    (p : triangulationTopologicalGeometricCarrier K)
    (hpS : p.1 ∈ move41PiSourceLocalCarrier s.a s.b s.c s.d s.e) :
    (move41GeometricCarrierForward hcore s hlegal p).1 =
      (move41PiLocalHomeomorph
        s.distinct
          ⟨p.1, hpS⟩).1 := by
  simp [move41GeometricCarrierForward, hpS]

private theorem move41GeometricCarrierForward_apply_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K)
    (p : triangulationTopologicalGeometricCarrier K)
    (hpU : p.1 ∈ s.unchangedGeometricCarrier K) :
    (move41GeometricCarrierForward hcore s hlegal p).1 = p.1 := by
  by_cases hpS : p.1 ∈ move41PiSourceLocalCarrier s.a s.b s.c s.d s.e
  · rw [move41GeometricCarrierForward_apply_eq_local hcore s hlegal p hpS]
    exact move41PiLocalHomeomorph_apply_eq_self s.distinct hpS
      (hcore.move41Site_radialMap_eq_self_of_mem_unchanged s hlegal hpS hpU)
  · simp [move41GeometricCarrierForward, hpS]

private theorem move41GeometricCarrierBackward_apply_eq_local
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K)
    (q : triangulationTopologicalGeometricCarrier (s.replace K))
    (hqT : q.1 ∈ move41PiTargetLocalCarrier s.a s.b s.c s.d s.e) :
    (move41GeometricCarrierBackward hcore s hlegal q).1 =
      ((move41PiLocalHomeomorph
        s.distinct).symm
          ⟨q.1, hqT⟩).1 := by
  simp [move41GeometricCarrierBackward, hqT]

private theorem move41GeometricCarrierBackward_apply_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K)
    (q : triangulationTopologicalGeometricCarrier (s.replace K))
    (hqU : q.1 ∈ s.unchangedGeometricCarrier K) :
    (move41GeometricCarrierBackward hcore s hlegal q).1 = q.1 := by
  by_cases hqT : q.1 ∈ move41PiTargetLocalCarrier s.a s.b s.c s.d s.e
  · rw [move41GeometricCarrierBackward_apply_eq_local hcore s hlegal q hqT]
    exact move41PiLocalHomeomorph_symm_apply_eq_self s.distinct hqT
      (hcore.move41Site_unchangedCarrier_inter_target_subset_source s hlegal ⟨hqU, hqT⟩)
  · simp [move41GeometricCarrierBackward, hqT]

private theorem move41GeometricCarrierForward_continuous
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    Continuous (move41GeometricCarrierForward hcore s hlegal) := by
  let S' : Set (triangulationTopologicalGeometricCarrier K) :=
    {p | p.1 ∈ move41PiSourceLocalCarrier s.a s.b s.c s.d s.e}
  let U' : Set (triangulationTopologicalGeometricCarrier K) :=
    {p | p.1 ∈ s.unchangedGeometricCarrier K}
  have hSclosed : IsClosed S' :=
    (move41PiSourceLocalCarrier_isCompact s.a s.b s.c s.d s.e).isClosed.preimage
      continuous_subtype_val
  have hUclosed : IsClosed U' :=
    (s.unchangedGeometricCarrier_isClosed K).preimage continuous_subtype_val
  have hScont : ContinuousOn (move41GeometricCarrierForward hcore s hlegal) S' := by
    rw [continuousOn_iff_continuous_restrict]
    let localIn : S' → ↥(move41PiSourceLocalCarrier s.a s.b s.c s.d s.e) :=
      fun p ↦ ⟨p.1.1, p.2⟩
    let localOut : ↥(move41PiTargetLocalCarrier s.a s.b s.c s.d s.e) →
        triangulationTopologicalGeometricCarrier (s.replace K) := fun q ↦
      ⟨q.1, hcore.move41Site_targetLocalCarrier_subset_target_space s hlegal q.2⟩
    have hin : Continuous localIn :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    have hout : Continuous localOut :=
      Continuous.subtype_mk continuous_subtype_val _
    have hcomp : Continuous (localOut ∘
        move41PiLocalHomeomorph
          s.distinct ∘ localIn) :=
      hout.comp ((move41PiLocalHomeomorph
        s.distinct).continuous.comp hin)
    convert hcomp using 1
    funext p
    apply Subtype.ext
    exact move41GeometricCarrierForward_apply_eq_local hcore s hlegal p.1 p.2
  have hUcont : ContinuousOn (move41GeometricCarrierForward hcore s hlegal) U' := by
    rw [continuousOn_iff_continuous_restrict]
    let unchangedOut : U' →
        triangulationTopologicalGeometricCarrier (s.replace K) := fun p ↦
      ⟨p.1.1, hcore.move41Site_unchangedCarrier_subset_target_space s hlegal p.2⟩
    have hc : Continuous unchangedOut :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    convert hc using 1
    funext p
    apply Subtype.ext
    exact move41GeometricCarrierForward_apply_eq_self_of_mem_unchanged hcore s hlegal p.1 p.2
  have hcover : S' ∪ U' = Set.univ := by
    ext p
    simp only [S', U', mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact (Set.ext_iff.mp
      (hcore.move41Site_global_region_decomposition s hlegal).1 p.1).mp p.2
  have h := hScont.union_of_isClosed hUcont hSclosed hUclosed
  rw [hcover] at h
  exact continuousOn_univ.mp h

private theorem move41GeometricCarrierBackward_forward
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) (p) :
    move41GeometricCarrierBackward hcore s hlegal
        (move41GeometricCarrierForward hcore s hlegal p) = p := by
  apply Subtype.ext
  by_cases hpS : p.1 ∈ move41PiSourceLocalCarrier s.a s.b s.c s.d s.e
  · have hFT : (move41GeometricCarrierForward hcore s hlegal p).1 ∈
        move41PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
      rw [move41GeometricCarrierForward_apply_eq_local hcore s hlegal p hpS]
      exact (move41PiLocalHomeomorph
        s.distinct ⟨p.1, hpS⟩).2
    rw [move41GeometricCarrierBackward_apply_eq_local hcore s hlegal _ hFT]
    have heq : ⟨(move41GeometricCarrierForward hcore s hlegal p).1, hFT⟩ =
        move41PiLocalHomeomorph
          s.distinct ⟨p.1, hpS⟩ := by
      apply Subtype.ext
      exact move41GeometricCarrierForward_apply_eq_local hcore s hlegal p hpS
    rw [heq, (move41PiLocalHomeomorph
      s.distinct).symm_apply_apply]
  · have hpU : p.1 ∈ s.unchangedGeometricCarrier K := by
      have hp := (Set.ext_iff.mp
        (hcore.move41Site_global_region_decomposition s hlegal).1 p.1).mp p.2
      exact hp.resolve_left hpS
    rw [move41GeometricCarrierBackward_apply_eq_self_of_mem_unchanged hcore s hlegal _ (by
      simpa [move41GeometricCarrierForward_apply_eq_self_of_mem_unchanged hcore s hlegal p hpU] using hpU)]
    exact move41GeometricCarrierForward_apply_eq_self_of_mem_unchanged hcore s hlegal p hpU

private theorem move41GeometricCarrierForward_backward
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) (q) :
    move41GeometricCarrierForward hcore s hlegal
        (move41GeometricCarrierBackward hcore s hlegal q) = q := by
  apply Subtype.ext
  by_cases hqT : q.1 ∈ move41PiTargetLocalCarrier s.a s.b s.c s.d s.e
  · have hGS : (move41GeometricCarrierBackward hcore s hlegal q).1 ∈
        move41PiSourceLocalCarrier s.a s.b s.c s.d s.e := by
      rw [move41GeometricCarrierBackward_apply_eq_local hcore s hlegal q hqT]
      exact ((move41PiLocalHomeomorph
        s.distinct).symm ⟨q.1, hqT⟩).2
    rw [move41GeometricCarrierForward_apply_eq_local hcore s hlegal _ hGS]
    have heq : ⟨(move41GeometricCarrierBackward hcore s hlegal q).1, hGS⟩ =
        (move41PiLocalHomeomorph
          s.distinct).symm ⟨q.1, hqT⟩ := by
      apply Subtype.ext
      exact move41GeometricCarrierBackward_apply_eq_local hcore s hlegal q hqT
    rw [heq, (move41PiLocalHomeomorph
      s.distinct).apply_symm_apply]
  · have hqU : q.1 ∈ s.unchangedGeometricCarrier K := by
      have hq := (Set.ext_iff.mp
        (hcore.move41Site_global_region_decomposition s hlegal).2 q.1).mp q.2
      exact hq.resolve_left hqT
    rw [move41GeometricCarrierForward_apply_eq_self_of_mem_unchanged hcore s hlegal _ (by
      simpa [move41GeometricCarrierBackward_apply_eq_self_of_mem_unchanged hcore s hlegal q hqU] using hqU)]
    exact move41GeometricCarrierBackward_apply_eq_self_of_mem_unchanged hcore s hlegal q hqU

noncomputable def ClosedTriangulationCore.move41GeometricCarrierHomeomorph
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier (s.replace K) := by
  letI : T2Space (Nat → ℝ) := Pi.t2Space
  letI : T2Space (triangulationTopologicalGeometricCarrier (s.replace K)) :=
    T2Space.of_injective_continuous Subtype.val_injective continuous_subtype_val
  let F := move41GeometricCarrierForward hcore s hlegal
  have hbij : Function.Bijective F := ⟨
    fun p q hpq ↦ by
      rw [← move41GeometricCarrierBackward_forward hcore s hlegal p,
        ← move41GeometricCarrierBackward_forward hcore s hlegal q]
      exact congrArg (move41GeometricCarrierBackward hcore s hlegal) hpq,
    fun q ↦ ⟨move41GeometricCarrierBackward hcore s hlegal q,
      move41GeometricCarrierForward_backward hcore s hlegal q⟩⟩
  exact IsHomeomorph.homeomorph F
    ((isHomeomorph_iff_continuous_bijective).2
      ⟨move41GeometricCarrierForward_continuous hcore s hlegal, hbij⟩)

/-- A genuine legal `4 → 1` replacement preserves the topology-bearing
geometric carrier by an explicit radial map glued to the identity. -/
theorem ClosedTriangulationCore.move41Site_replace_homeomorphic
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    Nonempty
      (triangulationTopologicalGeometricCarrier K ≃ₜ
        triangulationTopologicalGeometricCarrier (s.replace K)) :=
  ⟨hcore.move41GeometricCarrierHomeomorph s hlegal⟩


end Poincare
