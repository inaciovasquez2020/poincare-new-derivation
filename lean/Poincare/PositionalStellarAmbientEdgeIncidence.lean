import Poincare.PositionalStellarOldEdgeIncidence
import Mathlib.Tactic

namespace Poincare

/-- Exact ambient edge-incidence change for any distinct old vertices across
an arbitrary-position fresh 1→4 insertion. This does not assert 3→2 legality. -/
theorem Move41Site.insertFreshAt_old_edge_incidence
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hfresh : s.e ∉ vertexSupport K)
    (u v : Nat)
    (hu : u ≠ s.e) (hv : v ≠ s.e) (huv : u ≠ v) :
    ((s.insertFreshAt K before after hsource hfresh).tets.filter
      (fun τ => decide (u ∈ τ.verts ∧ v ∈ τ.verts))).length =
      (K.tets.filter (fun τ => decide (u ∈ τ.verts ∧ v ∈ τ.verts))).length +
        (if u ∈ s.targetTet.verts ∧ v ∈ s.targetTet.verts then 1 else 0) := by
  let p : Tet → Bool := fun τ => decide (u ∈ τ.verts ∧ v ∈ τ.verts)
  have hs := s.sourceTets_old_edge_count u v hu hv huv
  change (s.sourceTets.filter p).length =
    (if u ∈ s.targetTet.verts ∧ v ∈ s.targetTet.verts then 2 else 0) at hs
  rw [hsource]
  change ((before ++ s.sourceTets ++ after).filter p).length =
    ((before ++ s.targetTet :: after).filter p).length +
      (if u ∈ s.targetTet.verts ∧ v ∈ s.targetTet.verts then 1 else 0)
  simp only [List.filter_append, List.length_append, List.filter_cons]
  by_cases h : u ∈ s.targetTet.verts ∧ v ∈ s.targetTet.verts
  · have hp : p s.targetTet = true := by simp [p, h]
    simp only [hp, if_true, List.length_cons] at *
    rw [if_pos h] at hs
    omega
  · have hp : p s.targetTet = false := by simp [p, h]
    simp only [hp, if_false] at *
    rw [if_neg h] at hs
    omega

end Poincare
