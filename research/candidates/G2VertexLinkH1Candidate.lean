/-!
Append after G2CocyclePotentialCandidate.lean, with imports
  Poincare.VertexLinkMod2Chain
  Mathlib.LinearAlgebra.Dual.Lemmas
in the initial import block. Pinned parent fa2acb2cd3c1db7a7c0a6fa777485217b5a28edf.
NOT_RUN. The conclusion uses the actual represented boundary maps.
-/
namespace Poincare
open scoped BigOperators

private theorem g2Functional_coordinate_sum {E : Type*} [Fintype E] [DecidableEq E]
    (f : (E → ZMod 2) →ₗ[ZMod 2] ZMod 2) (z : E → ZMod 2) :
    f z = ∑ e : E, z e * f (Pi.single e 1) := by
  have hz : (∑ e : E, z e • (Pi.single e 1 : E → ZMod 2)) = z := by
    funext e
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hj
      simp [hj, Ne.symm hj]
    · simp
  calc
    f z = f (∑ e : E, z e • (Pi.single e 1 : E → ZMod 2)) := congrArg f hz.symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

private theorem g2Nodup_list_sum {E : Type*} [DecidableEq E]
    (l : List E) (h : l.Nodup) (f : E → ZMod 2) :
    (∑ e ∈ l.toFinset, f e) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hn := List.nodup_cons.mp h
      rw [List.toFinset_cons, Finset.sum_insert (by simpa using hn.1), ih hn.2] <;> rfl

/-- The actual mod-two link chain complex is exact in degree one. -/
theorem g2_vertex_link_mod2_h1_zero_candidate
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v : Nat} (hv : v ∈ vertexSupport K) : VertexLinkMod2H1Zero K hcore v := by
  classical
  let E := VertexLinkMod2Edge K hcore v
  let V := VertexLinkMod2Vertex K v
  let T := VertexLinkMod2Triangle K v
  let D1 := vertexLinkMod2BoundaryOne K hcore v
  let D2 := vertexLinkMod2BoundaryTwo K hcore v
  change LinearMap.ker D1 = LinearMap.range D2
  apply le_antisymm
  · intro z hz
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range D2) z).mp
    intro φ hφ
    let coeff (e : LinkEdge) : ZMod 2 :=
      if he : e ∈ vertexLinkEdges K hcore v then
        φ (Pi.single (⟨e, List.mem_toFinset.mpr he⟩ : E) 1) else 0
    have hcoeff (e : E) : coeff e.1 = φ (Pi.single e 1) := by
      simp only [coeff, dif_pos (List.mem_toFinset.mp e.2)]
      have heq : (⟨e.1, List.mem_toFinset.mpr (List.mem_toFinset.mp e.2)⟩ : E) = e := by
        apply Subtype.ext
        rfl
      rw [heq]
    let w (a b : Nat) : ZMod 2 :=
      if hab : a ≠ b then coeff (LinkEdge.ofDistinct a b hab) else 0
    have hzero (a : Nat) : w a a = 0 := by simp [w]
    have hsym (a b : Nat) : w a b = w b a := by
      by_cases hab : a = b
      · subst b; rfl
      · simp only [w, dif_pos hab, dif_pos (Ne.symm hab)]
        rw [LinkEdge.ofDistinct_symm a b hab]
    have htriangle (s : LinkTriangle) (hs : s ∈ vertexLinkTriangles K v) :
        ∀ a b c : Nat, a ∈ s.verts → b ∈ s.verts → c ∈ s.verts →
          w a b + w b c + w c a = 0 := by
      let t : T := ⟨s, List.mem_toFinset.mpr hs⟩
      have hφzero : φ (D2 (Pi.single t 1)) = 0 :=
        (Submodule.mem_dualAnnihilator φ).mp hφ _ ⟨_, rfl⟩
      rw [g2Functional_coordinate_sum] at hφzero
      simp only [D2, vertexLinkMod2BoundaryTwo, Matrix.mulVecLin_apply,
        Matrix.mulVec_single_one, Matrix.col_apply, vertexLinkMod2BoundaryTwoMatrix] at hφzero
      simp_rw [← hcoeff, ite_mul, one_mul, zero_mul] at hφzero
      let S := (vertexLinkEdges K hcore v).toFinset
      change (∑ e : ↥S, if e.1.InTriangle s then coeff e.1 else 0) = 0 at hφzero
      rw [Finset.univ_eq_attach S, Finset.sum_attach S (fun e : LinkEdge =>
        if e.InTriangle s then coeff e else 0), ← Finset.sum_filter,
        vertexLinkEdges_filter_inTriangle K hcore v s hs] at hφzero
      rw [g2Nodup_list_sum _ (LinkTriangle.edges_nodup s
        (vertexLinkTriangles_triangle_nodup K hcore v s hs))] at hφzero
      have hn := vertexLinkTriangles_triangle_nodup K hcore v s hs
      rcases s with ⟨x, y, z'⟩
      have hnd : (x ≠ y ∧ x ≠ z') ∧ y ≠ z' := by
        simpa [LinkTriangle.verts] using hn
      have hcanon : w x y + w x z' + w y z' = 0 := by
        simpa [LinkTriangle.edges, w, hnd.1.1, hnd.1.2, hnd.2, add_assoc] using hφzero
      have hyx := hsym y x
      have hzx := hsym z' x
      have hzy := hsym z' y
      intro a b c ha hb hc
      simp only [LinkTriangle.verts, List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
      rcases ha with rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl <;>
        rcases hc with rfl | rfl | rfl <;>
        simp only [hzero, hyx, hzx, hzy, add_zero, zero_add, CharTwo.add_self_eq_zero]
      all_goals simpa only [add_comm, add_left_comm, add_assoc] using hcanon
    obtain ⟨A, hA⟩ := g2_vertex_link_cocycle_exact_candidate hcore hM hv w hzero hsym htriangle
    have hweights (e : E) : φ (Pi.single e 1) = A e.1.lo + A e.1.hi := by
      have he := List.mem_toFinset.mp e.2
      obtain ⟨s, hs, hlo, hhi⟩ := (mem_vertexLinkEdges_iff K hcore v e.1).mp he
      have hcanonical := (vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e.1 he).2.2
      have h := hA s hs e.1.lo e.1.hi hlo hhi
      simp only [w, dif_pos e.1.sorted.ne, ← hcanonical, hcoeff] at h
      exact h
    let ψ : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      ∑ x : V, A x.1 • (LinearMap.proj x : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    have hψ (x : V) : ψ (Pi.single x 1) = A x.1 := by
      simp only [ψ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.proj_apply]
      rw [Finset.sum_eq_single x]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj, Ne.symm hj]
      · simp
    have hfactor : φ = ψ.comp D1 := by
      apply (Pi.basisFun (ZMod 2) E).ext
      intro e
      simp only [Pi.basisFun_apply, LinearMap.comp_apply]
      have he := List.mem_toFinset.mp e.2
      have hend := vertexLinkRepresentedEdge_has_canonical_endpoints K hcore v e.1 he
      let lo : V := ⟨e.1.lo, List.mem_toFinset.mpr hend.1⟩
      let hi : V := ⟨e.1.hi, List.mem_toFinset.mpr hend.2.1⟩
      have hne : lo ≠ hi := fun h => e.1.sorted.ne (congrArg Subtype.val h)
      have hcol : D1 (Pi.single e 1) = Pi.single lo 1 + Pi.single hi 1 := by
        funext x
        simp only [D1, vertexLinkMod2BoundaryOne, Matrix.mulVecLin_apply,
          Matrix.mulVec_single_one, Matrix.col_apply, vertexLinkMod2BoundaryOneMatrix,
          Pi.add_apply, Pi.single_apply]
        have hlo : x.1 = e.1.lo ↔ x = lo := ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
        have hhi : x.1 = e.1.hi ↔ x = hi := ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
        rw [hlo, hhi]
        by_cases hl : x = lo
        · subst x; simp [hne, Ne.symm hne]
        · by_cases hh : x = hi
          · subst x; simp [hne, Ne.symm hne]
          · simp [hl, hh, Ne.symm hl, Ne.symm hh]
      rw [hcol, map_add, hψ, hψ, hweights]
    rw [hfactor, LinearMap.comp_apply, LinearMap.mem_ker.mp hz, map_zero]
  · rintro z ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hcomp : D1.comp D2 = 0 := vertexLinkMod2_boundary_one_comp_boundary_two K hcore v
    exact LinearMap.congr_fun hcomp y

#print axioms g2_vertex_link_mod2_h1_zero_candidate
end Poincare
