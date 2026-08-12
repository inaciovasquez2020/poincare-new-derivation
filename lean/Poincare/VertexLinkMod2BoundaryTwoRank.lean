import Poincare.VertexLinkMod2Chain
import Mathlib.LinearAlgebra.Matrix.Rank

namespace Poincare

open Module

private theorem nodup_eraseDups_nat (l : List Nat) : l.eraseDups.Nodup := by
  cases l with
  | nil => simp
  | cons a l =>
      rw [List.eraseDups_cons]
      constructor
      · intro x hx hax
        have hx' := List.mem_eraseDups.1 hx
        simp [hax] at hx'
      · exact nodup_eraseDups_nat _
termination_by l.length
decreasing_by
  exact lt_of_le_of_lt (List.length_filter_le _ _) (Nat.lt_succ_self _)

private theorem sharesEdge_exists_linkEdge
    {σ ρ : LinkTriangle} (h : σ.SharesEdge ρ) :
    ∃ e : LinkEdge, e.InTriangle σ ∧ e.InTriangle ρ := by
  unfold LinkTriangle.SharesEdge LinkTriangle.commonVertexCount at h
  let l := σ.verts.eraseDups.filter (fun x => ρ.verts.contains x)
  have hl : 2 ≤ l.length := h
  obtain ⟨a, b, t, heq⟩ : ∃ a b t, l = a :: b :: t := by
    cases hlst : l with
    | nil => simp [hlst] at hl
    | cons a l =>
      cases hlst2 : l with
      | nil => simp [hlst, hlst2] at hl
      | cons b t => exact ⟨a, b, t, rfl⟩
  have hab : a ≠ b := by
    have hn : l.Nodup := (nodup_eraseDups_nat σ.verts).filter _
    rw [heq] at hn
    simp_all
  let e := LinkEdge.ofDistinct a b hab
  refine ⟨e, LinkEdge.ofDistinct_inTriangle σ a b hab ?_ ?_,
    LinkEdge.ofDistinct_inTriangle ρ a b hab ?_ ?_⟩
  · have hm : a ∈ l := by rw [heq]; simp
    exact List.mem_eraseDups.1 (List.mem_filter.1 hm).1
  · have hm : b ∈ l := by rw [heq]; simp
    exact List.mem_eraseDups.1 (List.mem_filter.1 hm).1
  · have hm : a ∈ l := by rw [heq]; simp
    simpa using (List.mem_filter.1 hm).2
  · have hm : b ∈ l := by rw [heq]; simp
    simpa using (List.mem_filter.1 hm).2

theorem vertexLinkMod2BoundaryTwo_kernel_adjacent_eq
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat)
    (hSurf : VertexLinkConnectedClosedSurfaceCertificate K v)
    (f : VertexLinkMod2Triangle K v → ZMod 2)
    (hf : f ∈ LinearMap.ker (vertexLinkMod2BoundaryTwo K hcore v))
    (σ ρ : LinkTriangle) (hadj : VertexLinkAdjacent K v σ ρ) :
    f ⟨σ, (List.mem_toFinset).2 hadj.1⟩ =
      f ⟨ρ, (List.mem_toFinset).2 hadj.2.1⟩ := by
  classical
  by_cases hsr : σ = ρ
  · subst ρ; rfl
  obtain ⟨e, heσ, heρ⟩ := hadj.2.2.elim sharesEdge_exists_linkEdge
    (fun h => by
      obtain ⟨e, heρ, heσ⟩ := sharesEdge_exists_linkEdge h
      exact ⟨e, heσ, heρ⟩)
  have hrep : e.RepresentedAt K v := ⟨σ, hadj.1, heσ⟩
  let T := VertexLinkMod2Triangle K v
  let se : T := ⟨σ, (List.mem_toFinset).2 hadj.1⟩
  let re : T := ⟨ρ, (List.mem_toFinset).2 hadj.2.1⟩
  have hcard : (Finset.univ.filter (fun τ : T => e.InTriangle τ.1)).card = 2 := by
    let S := (vertexLinkTriangles K v).toFinset
    rw [Finset.card_filter, Finset.univ_eq_attach S]
    rw [Finset.sum_attach S (fun τ => if e.InTriangle τ then 1 else 0)]
    rw [← Finset.card_filter]
    change ((vertexLinkTriangles K v).toFinset.filter (fun τ => e.InTriangle τ)).card = 2
    have heq : (vertexLinkTriangles K v).toFinset.filter (fun τ => e.InTriangle τ) =
        ((vertexLinkTriangles K v).filter
          (fun τ => decide (e.InTriangle τ))).toFinset := by ext; simp
    rw [heq]
    rw [List.toFinset_card_of_nodup]
    · exact hSurf.1.2.2.1 e hrep
    · exact (vertexLinkTriangles_nodup K hcore v).filter _
  have hfilter : Finset.univ.filter (fun τ : T => e.InTriangle τ.1) = {se, re} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [se, re, heσ, heρ]
    · rw [hcard]
      have hsrene : se ≠ re := by
        intro h; exact hsr (congrArg Subtype.val h)
      simp [hsrene]
  have hz := congrFun (LinearMap.mem_ker.mp hf)
    (⟨e, (List.mem_toFinset).2 (represented_mem_vertexLinkEdges K hcore v e hrep)⟩ :
      VertexLinkMod2Edge K hcore v)
  simp only [vertexLinkMod2BoundaryTwo, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, vertexLinkMod2BoundaryTwoMatrix] at hz
  change (∑ τ : T, (if e.InTriangle τ.1 then 1 else 0) * f τ) = 0 at hz
  simp_rw [ite_mul, one_mul, zero_mul] at hz
  rw [← Finset.sum_filter, hfilter] at hz
  have hsrene : se ≠ re := by intro h; exact hsr (congrArg Subtype.val h)
  simp [se, re, hsrene] at hz
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, neg_eq_self] using hz)

theorem vertexLinkMod2BoundaryTwo_kernel_global_constant
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat)
    (hSurf : VertexLinkConnectedClosedSurfaceCertificate K v)
    (f : VertexLinkMod2Triangle K v → ZMod 2)
    (hf : f ∈ LinearMap.ker (vertexLinkMod2BoundaryTwo K hcore v))
    (σ ρ : VertexLinkMod2Triangle K v) : f σ = f ρ := by
  have hchain : ∀ {α β : LinkTriangle}
      (hc : Relation.ReflTransGen (VertexLinkAdjacent K v) α β),
      ∀ (hα : α ∈ vertexLinkTriangles K v) (hβ : β ∈ vertexLinkTriangles K v),
        f ⟨α, (List.mem_toFinset).2 hα⟩ = f ⟨β, (List.mem_toFinset).2 hβ⟩ := by
    intro α β hc
    induction hc using Relation.ReflTransGen.trans_induction_on with
    | refl => intros; rfl
    | single h =>
        intro _ _
        exact vertexLinkMod2BoundaryTwo_kernel_adjacent_eq K hcore v hSurf f hf _ _ h
    | @trans α β γ h₁ h₂ ih₁ ih₂ =>
        intro hα hγ
        have hβ : β ∈ vertexLinkTriangles K v := by
          induction h₁ with
          | refl => exact hα
          | tail _ h _ => exact h.2.1
        exact (ih₁ hα hβ).trans (ih₂ hβ hγ)
  exact hchain (hSurf.2 σ.1 ((List.mem_toFinset).1 σ.2)
    ρ.1 ((List.mem_toFinset).1 ρ.2))
    ((List.mem_toFinset).1 σ.2) ((List.mem_toFinset).1 ρ.2)

theorem vertexLinkMod2BoundaryTwo_range_finrank_eq_card_sub_one
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hSurf : VertexLinkConnectedClosedSurfaceCertificate K v) :
    Module.finrank (ZMod 2)
        (LinearMap.range (vertexLinkMod2BoundaryTwo K hcore v)) =
      Fintype.card (VertexLinkMod2Triangle K v) - 1 := by
  classical
  let T := VertexLinkMod2Triangle K v
  let E := VertexLinkMod2Edge K hcore v
  let M := vertexLinkMod2BoundaryTwoMatrix K hcore v
  by_cases hT : IsEmpty T
  · have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
    haveI : IsEmpty T := hT
    rw [hcard]
    simp only [Nat.zero_sub]
    have hm : vertexLinkMod2BoundaryTwo K hcore v = 0 := by
      ext x
      exact isEmptyElim x
    rw [hm]
    simp
  · letI : Nonempty T := not_isEmpty_iff.mp hT
    let root : T := Classical.choice inferInstance
    let kerEquiv : LinearMap.ker M.mulVecLin ≃ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun f => f.1 root
        map_add' := by intros; rfl
        map_smul' := by intros; rfl
        invFun := fun c => ⟨fun _ => c, by
          apply LinearMap.mem_ker.mpr
          funext e
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M,
            vertexLinkMod2BoundaryTwoMatrix]
          let A := Finset.univ.filter (fun τ : T => e.1.InTriangle τ.1)
          have hrep := (mem_vertexLinkEdges_iff K hcore v e.1).1
            ((List.mem_toFinset).1 e.2)
          have hcard : A.card = 2 := by
            let S := (vertexLinkTriangles K v).toFinset
            change (Finset.univ.filter (fun τ : T => e.1.InTriangle τ.1)).card = 2
            rw [Finset.card_filter, Finset.univ_eq_attach S]
            rw [Finset.sum_attach S (fun τ => if e.1.InTriangle τ then 1 else 0)]
            rw [← Finset.card_filter]
            change ((vertexLinkTriangles K v).toFinset.filter
                (fun τ => e.1.InTriangle τ)).card = 2
            have heq : (vertexLinkTriangles K v).toFinset.filter
                (fun τ => e.1.InTriangle τ) =
                ((vertexLinkTriangles K v).filter
                  (fun τ => decide (e.1.InTriangle τ))).toFinset := by ext; simp
            rw [heq, List.toFinset_card_of_nodup]
            · exact hSurf.1.2.2.1 e.1 hrep
            · exact (vertexLinkTriangles_nodup K hcore v).filter _
          change (∑ τ : T, (if e.1.InTriangle τ.1 then 1 else 0) * c) = 0
          simp_rw [ite_mul, one_mul, zero_mul]
          rw [← Finset.sum_filter]
          rw [Finset.sum_const, hcard]
          simpa [two_smul] using CharTwo.add_self_eq_zero c
          ⟩
        left_inv := by
          intro f
          apply Subtype.ext
          funext x
          exact (vertexLinkMod2BoundaryTwo_kernel_global_constant K hcore v hSurf
            f.1 f.2 x root).symm
        right_inv := by intro c; rfl }
    have hker : Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = 1 := by
      rw [LinearEquiv.finrank_eq kerEquiv]
      exact Module.finrank_self (ZMod 2)
    change M.rank = Fintype.card T - 1
    have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [hker, Module.finrank_pi] at hrn
    change M.rank + 1 = Fintype.card T at hrn
    omega

end Poincare
