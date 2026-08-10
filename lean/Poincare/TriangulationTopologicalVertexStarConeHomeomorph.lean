import Poincare.TriangulationTopologicalVertexLink
import Mathlib.Topology.Algebra.Module.Basic

open Set

namespace Poincare

/-- Every point of the represented vertex link has zero apex coordinate. -/
theorem triangulationTopologicalVertexLink_apex_coordinate_eq_zero
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (v : Nat) (q : Nat → ℝ)
    (hq : q ∈ triangulationTopologicalVertexLink K v) :
    q v = 0 := by
  classical
  obtain ⟨σ, hσlink, hqσ⟩ :=
    (mem_triangulationTopologicalVertexLink_iff K v q).1 hq
  obtain ⟨τ, hτK, hτσ⟩ := (mem_vertexLinkTriangles_iff K v σ).1 hσlink
  have hvnotσ : v ∉ σ.verts :=
    τ.linkTriangleAt?_vertex_not_mem v σ (hcore.1 τ hτK) hτσ
  apply convexHull_min _ (convex_hyperplane
    ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hqσ
  rintro _ ⟨y, hy, rfl⟩
  have hyv : y ≠ v := by
    intro hyv
    subst y
    exact hvnotσ (List.mem_toFinset.mp hy)
  simp [triangulationTopologicalGeometricVertex, hyv]

private abbrev RadialLinkDomain (K : Triangulation) (v : Nat) :=
  ↥(Set.Ico (0 : ℝ) 1) × ↥(triangulationTopologicalVertexLink K v)

private abbrev PuncturedVertexStar (K : Triangulation) (v : Nat) :=
  ↥{p : Nat → ℝ |
    p ∈ triangulationTopologicalVertexStar K v ∧ p v < 1}

private noncomputable def radialForward
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat) :
    RadialLinkDomain K v → PuncturedVertexStar K v := fun tq ↦
  ⟨tq.1.1 • triangulationTopologicalGeometricVertex v +
      (1 - tq.1.1) • tq.2.1,
    (triangulationTopologicalVertexStar_mem_and_coordinate_lt_one_iff
      K hcore v _).2
      ⟨tq.1.1, tq.2.1, tq.1.2.1, tq.1.2.2, tq.2.2,
        triangulationTopologicalVertexLink_apex_coordinate_eq_zero
          K hcore v tq.2.1 tq.2.2, rfl⟩⟩

private theorem radialForward_apex_coordinate
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat)
    (tq : RadialLinkDomain K v) :
    (radialForward K hcore v tq).1 v = tq.1.1 := by
  simp [radialForward, triangulationTopologicalGeometricVertex,
    triangulationTopologicalVertexLink_apex_coordinate_eq_zero
      K hcore v tq.2.1 tq.2.2]

/-- The explicit projection of a non-apex star point onto its radial link point. -/
noncomputable def triangulationTopologicalRadialLinkProjection
    (K : Triangulation) (v : Nat) (p : PuncturedVertexStar K v) : Nat → ℝ :=
  (1 / (1 - p.1 v)) •
    (p.1 - p.1 v • triangulationTopologicalGeometricVertex v)

private theorem radialLinkProjection_mem
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat)
    (p : PuncturedVertexStar K v) :
    triangulationTopologicalRadialLinkProjection K v p ∈
      triangulationTopologicalVertexLink K v := by
  obtain ⟨t, q, ht, ht1, hqlink, hqv, hp⟩ :=
    (triangulationTopologicalVertexStar_mem_and_coordinate_lt_one_iff
      K hcore v p.1).1 p.2
  have hpvt : p.1 v = t := by
    rw [hp]
    simp [triangulationTopologicalGeometricVertex, hqv]
  have hne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
  have heq : triangulationTopologicalRadialLinkProjection K v p = q := by
    ext x
    simp only [triangulationTopologicalRadialLinkProjection, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    rw [hp]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp [triangulationTopologicalGeometricVertex, hqv]
    field_simp
  rw [heq]
  exact hqlink

private theorem puncturedVertexStar_apex_coordinate_nonneg
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat)
    (p : PuncturedVertexStar K v) : 0 ≤ p.1 v := by
  exact (triangulationTopologicalVertexStar_exists_vertexLink_cone_decomposition
    K hcore v p.1 p.2.1 p.2.2).1

private noncomputable def radialInverse
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat) :
    PuncturedVertexStar K v → RadialLinkDomain K v := fun p ↦
  (⟨p.1 v,
    puncturedVertexStar_apex_coordinate_nonneg K hcore v p,
    p.2.2⟩,
   ⟨triangulationTopologicalRadialLinkProjection K v p,
    radialLinkProjection_mem K hcore v p⟩)

private theorem radialInverse_left
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat) :
    Function.LeftInverse (radialInverse K hcore v) (radialForward K hcore v) := by
  intro tq
  apply Prod.ext
  · apply Subtype.ext
    exact radialForward_apex_coordinate K hcore v tq
  · apply Subtype.ext
    ext x
    have htv := tq.1.2.2
    have hne : 1 - tq.1.1 ≠ 0 := ne_of_gt (sub_pos.mpr htv)
    simp only [radialInverse, triangulationTopologicalRadialLinkProjection,
      radialForward, Pi.smul_apply, Pi.sub_apply,
      Pi.add_apply, smul_eq_mul]
    simp [triangulationTopologicalGeometricVertex,
      triangulationTopologicalVertexLink_apex_coordinate_eq_zero
        K hcore v tq.2.1 tq.2.2]
    field_simp

private theorem radialInverse_right
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat) :
    Function.RightInverse (radialInverse K hcore v) (radialForward K hcore v) := by
  intro p
  apply Subtype.ext
  ext x
  have hne : 1 - p.1 v ≠ 0 := ne_of_gt (sub_pos.mpr p.2.2)
  simp only [radialForward, radialInverse,
    triangulationTopologicalRadialLinkProjection, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

private theorem continuous_radialForward
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat) :
    Continuous (radialForward K hcore v) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd))

private theorem continuous_radialInverse
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat) :
    Continuous (radialInverse K hcore v) := by
  have hcoord : Continuous (fun p : PuncturedVertexStar K v ↦ p.1 v) :=
    (continuous_apply v).comp continuous_subtype_val
  have hdenom : Continuous (fun p : PuncturedVertexStar K v ↦ 1 - p.1 v) :=
    continuous_const.sub hcoord
  have hinv : Continuous (fun p : PuncturedVertexStar K v ↦ (1 - p.1 v)⁻¹) :=
    hdenom.inv₀ (fun p ↦ ne_of_gt (sub_pos.mpr p.2.2))
  have hprojection : Continuous
      (fun p : PuncturedVertexStar K v ↦
        triangulationTopologicalRadialLinkProjection K v p) := by
    simpa [triangulationTopologicalRadialLinkProjection, one_div] using
      hinv.smul
        (continuous_subtype_val.sub
          (hcoord.smul (continuous_const : Continuous fun _ : PuncturedVertexStar K v ↦
            triangulationTopologicalGeometricVertex v)))
  exact (Continuous.subtype_mk hcoord _).prodMk
    (Continuous.subtype_mk hprojection _)

/-- The non-apex represented vertex star is the product of its radial interval
and the existing represented Pi-space vertex link.  Both directions use the
explicit radial formulas. -/
noncomputable def triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat) :
    (↥(Set.Ico (0 : ℝ) 1) ×
      ↥(triangulationTopologicalVertexLink K v)) ≃ₜ
      ↥{p : Nat → ℝ |
        p ∈ triangulationTopologicalVertexStar K v ∧ p v < 1} where
  toFun := radialForward K hcore v
  invFun := radialInverse K hcore v
  left_inv := radialInverse_left K hcore v
  right_inv := radialInverse_right K hcore v
  continuous_toFun := continuous_radialForward K hcore v
  continuous_invFun := continuous_radialInverse K hcore v

@[simp] theorem
triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink_apply_val
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat)
    (tq : ↥(Set.Ico (0 : ℝ) 1) ×
      ↥(triangulationTopologicalVertexLink K v)) :
    ((triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
      K hcore v) tq).1 =
      tq.1.1 • triangulationTopologicalGeometricVertex v +
        (1 - tq.1.1) • tq.2.1 := rfl

/-- Every non-apex represented star point has a unique radial pair in the
literal interval/link product. -/
theorem triangulationTopologicalPuncturedVertexStar_existsUnique_radialPair
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat)
    (p : ↥{p : Nat → ℝ |
      p ∈ triangulationTopologicalVertexStar K v ∧ p v < 1}) :
    ∃! tq : ↥(Set.Ico (0 : ℝ) 1) ×
        ↥(triangulationTopologicalVertexLink K v),
      p.1 = tq.1.1 • triangulationTopologicalGeometricVertex v +
        (1 - tq.1.1) • tq.2.1 := by
  let e := triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink
    K hcore v
  refine ⟨e.symm p, ?_, ?_⟩
  · have h := congrArg Subtype.val (e.apply_symm_apply p)
    simpa [e, triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink,
      radialForward] using h.symm
  · intro tq htq
    apply e.injective
    apply Subtype.ext
    have h := congrArg Subtype.val (e.apply_symm_apply p)
    simpa [e, triangulationTopologicalPuncturedVertexStarHomeomorphRadialLink,
      radialForward, htq] using h.symm

end Poincare
