import Poincare.FacePairingCompletePillowFixture

namespace Poincare

/-!
Unoriented local-edge keys and their invariance under the closed,
identity-face-glued double pillow. This is the first required
identification bridge before any class-valence statement.
-/

/-- Canonical unordered local endpoint pair. -/
def FacePairingLocalEdge.undirectedKey {n : Nat}
    (e : FacePairingLocalEdge n) : Nat × Nat :=
  (min e.first.val e.second.val, max e.first.val e.second.val)

/-- Every gluing in the complete double pillow fixes local vertex labels. -/
theorem completeDoublePillow_identifications_identity :
    ∀ g ∈ completeDoublePillow.identifications,
      ∀ v : Fin 4, g.localVertexMap v = v := by
  intro g hg v
  simp [completeDoublePillow] at hg
  rcases hg with rfl | rfl | rfl | rfl
  all_goals rfl

/-- The actual inductively generated edge quotient preserves the unordered
endpoint key; this does not yet assert the converse for arbitrary fixtures. -/
theorem completeDoublePillow_equivalence_preserves_key
    {e f : FacePairingLocalEdge 2}
    (h : completeDoublePillow.EdgeEquivalent e f) :
    e.undirectedKey = f.undirectedKey := by
  induction h with
  | refl e => rfl
  | reverse e =>
      simp [FacePairingLocalEdge.undirectedKey,
        FacePairingLocalEdge.reverse, Nat.min_comm, max_comm]
  | pair g hg h =>
      rcases h with ⟨_, _, _, _, hfirst, hsecond⟩
      have hf := completeDoublePillow_identifications_identity g hg e.first
      have hs := completeDoublePillow_identifications_identity g hg e.second
      rw [hf] at hfirst
      rw [hs] at hsecond
      simp [FacePairingLocalEdge.undirectedKey, hfirst, hsecond]
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

end Poincare
