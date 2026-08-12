import Poincare.VertexLinkMod2BoundaryOneRank
import Poincare.VertexLinkMod2BoundaryTwoRank
import Mathlib.Tactic

namespace Poincare

private theorem nodup_eraseDups_local
    {α : Type} [BEq α] [LawfulBEq α]
    (l : List α) : l.eraseDups.Nodup := by
  cases l with
  | nil => simp
  | cons a l =>
      rw [List.eraseDups_cons]
      constructor
      · intro x hx hax
        have hx' := List.mem_eraseDups.1 hx
        simp [hax] at hx'
      · exact nodup_eraseDups_local _
termination_by l.length
decreasing_by
  exact
    lt_of_le_of_lt
      (List.length_filter_le _ _)
      (Nat.lt_succ_self _)

/--
A nonempty connected closed represented vertex-link surface whose exact
mod-2 first homology vanishes has Euler characteristic two.
-/
theorem
    vertexLinkEulerCharacteristic_eq_two_of_connectedClosedSurface_and_mod2H1Zero
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hSurf : VertexLinkConnectedClosedSurfaceCertificate K v)
    (hT : Nonempty (VertexLinkMod2Triangle K v))
    (hH1 : VertexLinkMod2H1Zero K hcore v) :
    vertexLinkEulerCharacteristic K hcore v = 2 := by
  classical

  have hr1 :
      Module.finrank (ZMod 2)
          (LinearMap.range
            (vertexLinkMod2BoundaryOne K hcore v)) =
        Fintype.card (VertexLinkMod2Vertex K v) - 1 :=
    vertexLinkMod2BoundaryOne_range_finrank_eq_card_sub_one
      K hcore v hSurf

  have hr2 :
      Module.finrank (ZMod 2)
          (LinearMap.range
            (vertexLinkMod2BoundaryTwo K hcore v)) =
        Fintype.card (VertexLinkMod2Triangle K v) - 1 :=
    vertexLinkMod2BoundaryTwo_range_finrank_eq_card_sub_one
      K hcore v hSurf

  have hH1' :
      LinearMap.ker
          (vertexLinkMod2BoundaryOne K hcore v) =
        LinearMap.range
          (vertexLinkMod2BoundaryTwo K hcore v) :=
    (vertexLinkMod2H1Zero_iff K hcore v).1 hH1

  have hker :
      Module.finrank (ZMod 2)
          (LinearMap.ker
            (vertexLinkMod2BoundaryOne K hcore v)) =
        Fintype.card (VertexLinkMod2Triangle K v) - 1 := by
    rw [hH1']
    exact hr2

  have hrn :=
    LinearMap.finrank_range_add_finrank_ker
      (vertexLinkMod2BoundaryOne K hcore v)

  rw [hr1, hker, Module.finrank_pi] at hrn

  have hFpos :
      0 < Fintype.card (VertexLinkMod2Triangle K v) :=
    Fintype.card_pos_iff.mpr hT

  obtain ⟨σ⟩ := hT

  have hσmem :
      σ.1 ∈ vertexLinkTriangles K v :=
    (List.mem_toFinset).1 σ.2

  have hv0 :
      σ.1.v0 ∈ vertexLinkVertices K v := by
    apply (mem_vertexLinkVertices_iff K v σ.1.v0).2
    exact
      ⟨σ.1, hσmem, by
        simp [LinkTriangle.verts]⟩

  have hVnonempty :
      Nonempty (VertexLinkMod2Vertex K v) :=
    ⟨⟨σ.1.v0, (List.mem_toFinset).2 hv0⟩⟩

  have hVpos :
      0 < Fintype.card (VertexLinkMod2Vertex K v) :=
    Fintype.card_pos_iff.mpr hVnonempty

  have hNat :
      Fintype.card (VertexLinkMod2Vertex K v) +
          Fintype.card (VertexLinkMod2Triangle K v) =
        Fintype.card (VertexLinkMod2Edge K hcore v) + 2 := by
    omega

  have hVnodup :
      (vertexLinkVertices K v).Nodup := by
    unfold vertexLinkVertices
    exact nodup_eraseDups_local _

  have hEnodup :
      (vertexLinkEdges K hcore v).Nodup := by
    unfold vertexLinkEdges
    exact nodup_eraseDups_local _

  have hTnodup :
      (vertexLinkTriangles K v).Nodup :=
    vertexLinkTriangles_nodup K hcore v

  have hVcard :
      Fintype.card (VertexLinkMod2Vertex K v) =
        (vertexLinkVertices K v).length := by
    rw [Fintype.card_coe]
    exact List.toFinset_card_of_nodup hVnodup

  have hEcard :
      Fintype.card (VertexLinkMod2Edge K hcore v) =
        (vertexLinkEdges K hcore v).length := by
    rw [Fintype.card_coe]
    exact List.toFinset_card_of_nodup hEnodup

  have hFcard :
      Fintype.card (VertexLinkMod2Triangle K v) =
        (vertexLinkTriangles K v).length := by
    rw [Fintype.card_coe]
    exact List.toFinset_card_of_nodup hTnodup

  have hLengths :
      (vertexLinkVertices K v).length +
          (vertexLinkTriangles K v).length =
        (vertexLinkEdges K hcore v).length + 2 := by
    rw [← hVcard, ← hFcard, ← hEcard]
    exact hNat

  unfold vertexLinkEulerCharacteristic
  omega

end Poincare
