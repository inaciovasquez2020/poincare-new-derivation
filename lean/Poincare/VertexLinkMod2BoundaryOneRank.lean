import Poincare.VertexLinkMod2Chain
import Mathlib.LinearAlgebra.Matrix.Rank

namespace Poincare

open Module

theorem vertexLinkMod2BoundaryOne_range_finrank_eq_card_sub_one
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hSurf : VertexLinkConnectedClosedSurfaceCertificate K v) :
    Module.finrank (ZMod 2)
        (LinearMap.range
          (vertexLinkMod2BoundaryOne K hcore v)) =
      Fintype.card (VertexLinkMod2Vertex K v) - 1 := by
  classical
  let V := VertexLinkMod2Vertex K v
  let E := VertexLinkMod2Edge K hcore v
  let M := vertexLinkMod2BoundaryOneMatrix K hcore v
  let S : Finset V := Finset.univ
  have hedge_eq (f : V → ZMod 2)
      (hf : f ∈ LinearMap.ker M.transpose.mulVecLin)
      (e : LinkEdge) (he : e ∈ vertexLinkEdges K hcore v) :
      f ⟨e.lo, (List.mem_toFinset).2
        (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e he).1⟩ =
      f ⟨e.hi, (List.mem_toFinset).2
        (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e he).2.1⟩ := by
    have hz := congrFun (LinearMap.mem_ker.mp hf)
      (⟨e, (List.mem_toFinset).2 he⟩ : E)
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, M, vertexLinkMod2BoundaryOneMatrix] at hz
    change (∑ x : V, (if x.1 = e.lo ∨ x.1 = e.hi then 1 else 0) * f x) = 0 at hz
    have hlohi : e.lo ≠ e.hi := Nat.ne_of_lt e.sorted
    have hsplit : (∑ x : V,
        (if x.1 = e.lo ∨ x.1 = e.hi then 1 else 0) * f x) =
        f ⟨e.lo, (List.mem_toFinset).2
          (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e he).1⟩ +
        ∑ x ∈ S.erase
          (⟨e.lo, (List.mem_toFinset).2
            (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e he).1⟩ : V),
          (if x.1 = e.lo ∨ x.1 = e.hi then 1 else 0) * f x := by
      let a : V := ⟨e.lo, (List.mem_toFinset).2
        (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e he).1⟩
      have hh := Finset.sum_erase_add S
        (fun x : V => (if x.1 = e.lo ∨ x.1 = e.hi then 1 else 0) * f x)
        (a := a) (by simp [S])
      calc
        _ = (∑ x ∈ S.erase a,
              (if x.1 = e.lo ∨ x.1 = e.hi then 1 else 0) * f x) +
              (if a.1 = e.lo ∨ a.1 = e.hi then 1 else 0) * f a := hh.symm
        _ = _ := by simp [a, add_comm]
    rw [hsplit] at hz
    have hrest :
        ∑ x ∈ (S.erase
          (⟨e.lo, (List.mem_toFinset).2
            (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e he).1⟩ : V)),
          (if x.1 = e.lo ∨ x.1 = e.hi then 1 else 0) * f x =
        f ⟨e.hi, (List.mem_toFinset).2
          (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e he).2.1⟩ := by
      rw [Finset.sum_eq_single
        (⟨e.hi, (List.mem_toFinset).2
          (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e he).2.1⟩ : V)]
      · simp
      · intro b hb hne
        simp only [Finset.mem_erase] at hb
        simp only [ite_mul, one_mul, zero_mul]
        split
        · rename_i hinc
          rcases hinc with h | h
          · exact (hb.1 (Subtype.ext h)).elim
          · exact (hne (Subtype.ext h)).elim
        · rfl
      · simp [S, Ne.symm hlohi]
    rw [hrest] at hz
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, neg_eq_self] using hz)
  have htriangle (f : V → ZMod 2)
      (hf : f ∈ LinearMap.ker M.transpose.mulVecLin)
      (σ : LinkTriangle) (hσ : σ ∈ vertexLinkTriangles K v)
      (a b : Nat) (ha : a ∈ σ.verts) (hb : b ∈ σ.verts) :
      f ⟨a, (List.mem_toFinset).2 ((mem_vertexLinkVertices_iff K v a).2 ⟨σ, hσ, ha⟩)⟩ =
      f ⟨b, (List.mem_toFinset).2 ((mem_vertexLinkVertices_iff K v b).2 ⟨σ, hσ, hb⟩)⟩ := by
    by_cases hab : a = b
    · subst b
      rfl
    · let e := LinkEdge.ofDistinct a b hab
      have heRep : e.RepresentedAt K v :=
        ⟨σ, hσ, LinkEdge.ofDistinct_inTriangle σ a b hab ha hb⟩
      have he := represented_mem_vertexLinkEdges K hcore v e heRep
      have heq := hedge_eq f hf e he
      have hend := LinkEdge.incident_ofDistinct_iff a b a hab
      unfold e at heq
      unfold LinkEdge.ofDistinct at heq
      split at heq
      · simpa using heq
      · simpa using heq.symm
  have hadjacent (f : V → ZMod 2)
      (hf : f ∈ LinearMap.ker M.transpose.mulVecLin)
      (σ ρ : LinkTriangle) (hadj : VertexLinkAdjacent K v σ ρ)
      (a : Nat) (ha : a ∈ σ.verts) (b : Nat) (hb : b ∈ ρ.verts) :
      f ⟨a, (List.mem_toFinset).2 ((mem_vertexLinkVertices_iff K v a).2 ⟨σ, hadj.1, ha⟩)⟩ =
      f ⟨b, (List.mem_toFinset).2 ((mem_vertexLinkVertices_iff K v b).2 ⟨ρ, hadj.2.1, hb⟩)⟩ := by
    have hshare : ∃ x, x ∈ σ.verts ∧ x ∈ ρ.verts := by
      rcases hadj.2.2 with hs | hs
      · unfold LinkTriangle.SharesEdge LinkTriangle.commonVertexCount at hs
        have hn : (σ.verts.eraseDups.filter (fun x => ρ.verts.contains x)).length ≠ 0 := by omega
        have hnil : σ.verts.eraseDups.filter (fun x => ρ.verts.contains x) ≠ [] := by
          intro hh
          rw [hh] at hs
          simp at hs
        rcases List.exists_mem_of_ne_nil _ hnil with ⟨x, hx⟩
        simp only [List.mem_filter, List.mem_eraseDups] at hx
        exact ⟨x, hx.1, by simpa using hx.2⟩
      · unfold LinkTriangle.SharesEdge LinkTriangle.commonVertexCount at hs
        have hn : (ρ.verts.eraseDups.filter (fun x => σ.verts.contains x)).length ≠ 0 := by omega
        have hnil : ρ.verts.eraseDups.filter (fun x => σ.verts.contains x) ≠ [] := by
          intro hh
          rw [hh] at hs
          simp at hs
        rcases List.exists_mem_of_ne_nil _ hnil with ⟨x, hx⟩
        simp only [List.mem_filter, List.mem_eraseDups] at hx
        exact ⟨x, by simpa using hx.2, hx.1⟩
    rcases hshare with ⟨x, hxσ, hxρ⟩
    exact (htriangle f hf σ hadj.1 a x ha hxσ).trans
      (htriangle f hf ρ hadj.2.1 x b hxρ hb)
  have hglobal (f : V → ZMod 2)
      (hf : f ∈ LinearMap.ker M.transpose.mulVecLin)
      (x y : V) : f x = f y := by
    obtain ⟨σ, hσ, hxσ⟩ := (mem_vertexLinkVertices_iff K v x.1).1
      ((List.mem_toFinset).1 x.2)
    obtain ⟨ρ, hρ, hyρ⟩ := (mem_vertexLinkVertices_iff K v y.1).1
      ((List.mem_toFinset).1 y.2)
    have hc := hSurf.2 σ hσ ρ hρ
    have hmem {α β : LinkTriangle}
        (hc : Relation.ReflTransGen (VertexLinkAdjacent K v) α β)
        (hα : α ∈ vertexLinkTriangles K v) : β ∈ vertexLinkTriangles K v := by
      induction hc with
      | refl => exact hα
      | tail hab hbc ih => exact hbc.2.1
    have hchain : ∀ {α β : LinkTriangle}
        (hc : Relation.ReflTransGen (VertexLinkAdjacent K v) α β),
        ∀ (hα : α ∈ vertexLinkTriangles K v)
          (hβ : β ∈ vertexLinkTriangles K v)
          (p q : V), p.1 ∈ α.verts → q.1 ∈ β.verts → f p = f q := by
      intro α β hc
      induction hc using Relation.ReflTransGen.trans_induction_on with
      | refl =>
          intro hα _ p q hp hq
          exact htriangle f hf _ hα p.1 q.1 hp hq
      | single hadj =>
          intro _ _ p q hp hq
          exact hadjacent f hf _ _ hadj p.1 hp q.1 hq
      | @trans α β γ h₁ h₂ ih₁ ih₂ =>
          intro hα hγ p q hp hq
          have hβ := hmem h₁ hα
          let z : V := ⟨β.v0, (List.mem_toFinset).2
            ((mem_vertexLinkVertices_iff K v β.v0).2
              ⟨β, hβ, by simp [LinkTriangle.verts]⟩)⟩
          exact (ih₁ hα hβ p z hp (by simp [z, LinkTriangle.verts])).trans
            (ih₂ hβ hγ z q (by simp [z, LinkTriangle.verts]) hq)
    exact hchain hc hσ hρ x y hxσ hyρ
  by_cases hV : IsEmpty V
  · have hcard : Fintype.card V = 0 := Fintype.card_eq_zero
    change M.rank = Fintype.card V - 1
    simp [Matrix.rank, hcard]
  · letI : Nonempty V := not_isEmpty_iff.mp hV
    let root : V := Classical.choice inferInstance
    let kerEquiv : LinearMap.ker M.transpose.mulVecLin ≃ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun f => f.1 root
        map_add' := by intros; rfl
        map_smul' := by intros; rfl
        invFun := fun c => ⟨fun _ => c, by
          apply LinearMap.mem_ker.mpr
          funext e
          simp [M, vertexLinkMod2BoundaryOneMatrix, Matrix.mulVecLin_apply,
            Matrix.mulVec, dotProduct]
          unfold Matrix.vecMul dotProduct vertexLinkMod2BoundaryOneMatrix
          change (∑ x : V,
            c * (if x.1 = e.1.lo ∨ x.1 = e.1.hi then 1 else 0)) = 0
          have hsplit : (∑ x : V,
              c * (if x.1 = e.1.lo ∨ x.1 = e.1.hi then 1 else 0)) =
              c + ∑ x ∈ S.erase
              (⟨e.1.lo, (List.mem_toFinset).2
                (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e.1
                  ((List.mem_toFinset).1 e.2)).1⟩ : V),
                c * (if x.1 = e.1.lo ∨ x.1 = e.1.hi then 1 else 0) := by
            let a : V := ⟨e.1.lo, (List.mem_toFinset).2
              (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e.1
                ((List.mem_toFinset).1 e.2)).1⟩
            have hh := Finset.sum_erase_add S
              (fun x : V => c *
                (if x.1 = e.1.lo ∨ x.1 = e.1.hi then 1 else 0))
              (a := a) (by simp [S])
            calc
              _ = (∑ x ∈ S.erase a, c *
                    (if x.1 = e.1.lo ∨ x.1 = e.1.hi then 1 else 0)) +
                    c * (if a.1 = e.1.lo ∨ a.1 = e.1.hi then 1 else 0) := hh.symm
              _ = _ := by simp [a, add_comm]
          rw [hsplit]
          rw [Finset.sum_eq_single
            (⟨e.1.hi, (List.mem_toFinset).2
              (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e.1
                ((List.mem_toFinset).1 e.2)).2.1⟩ : V)]
          · simpa using CharTwo.add_self_eq_zero c
          · intro b hb hne
            have hb' := (Finset.mem_erase.mp hb).1
            simp only [mul_ite, mul_one, mul_zero]
            split
            · rename_i hinc
              rcases hinc with h | h
              · exact (hb' (Subtype.ext h)).elim
              · exact (hne (Subtype.ext h)).elim
            · rfl
          · simp [S, Ne.symm (Nat.ne_of_lt e.1.sorted)]
          ⟩
        left_inv := by
          intro f
          apply Subtype.ext
          funext x
          exact (hglobal f.1 f.2 x root).symm
        right_inv := by intro c; rfl }
    have hker : Module.finrank (ZMod 2)
        (LinearMap.ker M.transpose.mulVecLin) = 1 := by
      rw [LinearEquiv.finrank_eq kerEquiv]
      exact Module.finrank_self (ZMod 2)
    change M.rank = Fintype.card V - 1
    rw [← Matrix.rank_transpose M]
    have hrn := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
    rw [hker, Module.finrank_pi] at hrn
    change M.transpose.rank + 1 = Fintype.card V at hrn
    omega

end Poincare
