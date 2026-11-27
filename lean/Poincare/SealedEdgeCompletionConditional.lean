import Mathlib

namespace Poincare

section SealedEdgeResourceBounds
-- Use Lean's default bounded elaboration limits for these conditional proofs.

private def edgeLinkAdjacent
    (completion : Finset (Finset Nat))
    (edge : Finset Nat)
    (u v : Nat) : Prop :=
  u ∉ edge ∧ v ∉ edge ∧
  ∃ tet ∈ completion, edge ⊆ tet ∧ u ∈ tet ∧ v ∈ tet

private theorem saturated_subset_equal
    (seed completion : Finset (Finset Nat))
    (face : Finset Nat)
    (hsub : seed ⊆ completion)
    (hseed : (seed.filter (fun tet => face ⊆ tet)).card = 2)
    (hcompletion : (completion.filter (fun tet => face ⊆ tet)).card ≤ 2) :
    seed.filter (fun tet => face ⊆ tet) =
    completion.filter (fun tet => face ⊆ tet) := by
  classical
  have hfiltered :
      seed.filter (fun t => face ⊆ t) ⊆
      completion.filter (fun t => face ⊆ t) := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨hm, hf⟩
    exact Finset.mem_filter.mpr ⟨hsub hm, hf⟩
  have hcard :
      (completion.filter (fun t => face ⊆ t)).card ≤
      (seed.filter (fun t => face ⊆ t)).card := by
    omega
  exact Finset.eq_of_subset_of_card_le hfiltered hcard

private theorem sealed_edge_link_reachability
    (seed completion : Finset (Finset Nat))
    (edge : Finset Nat)
    (hsub : seed ⊆ completion)
    (hsaturated :
      ∀ u : Nat, u ∉ edge →
        (∃ tet ∈ seed, edge ⊆ tet ∧ u ∈ tet) →
        (seed.filter (fun tet => insert u edge ⊆ tet)).card = 2)
    (hincidence :
      ∀ u : Nat, u ∉ edge →
        (completion.filter (fun tet => insert u edge ⊆ tet)).card ≤ 2)
    (start finish : Nat)
    (hstart : start ∉ edge ∧
      ∃ tet ∈ seed, edge ⊆ tet ∧ start ∈ tet)
    (hreach : Relation.ReflTransGen
      (edgeLinkAdjacent completion edge) start finish) :
    finish ∉ edge ∧
      ∃ tet ∈ seed, edge ⊆ tet ∧ finish ∈ tet := by
  classical
  have propagate :
      ∀ (u v : Nat),
        (u ∉ edge ∧
          ∃ tet ∈ seed, edge ⊆ tet ∧ u ∈ tet) →
        edgeLinkAdjacent completion edge u v →
        (v ∉ edge ∧
          ∃ tet ∈ seed, edge ⊆ tet ∧ v ∈ tet) := by
    intro u v hu hstep
    rcases hu with ⟨huOutside, oldTet, hOldSeed, hOldEdge, hOldU⟩
    rcases hstep with
      ⟨_, hvOutside, newTet, hNewCompletion, hNewEdge, hNewU, hNewV⟩
    have hSeedCount :
        (seed.filter (fun tet => insert u edge ⊆ tet)).card = 2 :=
      hsaturated u huOutside
        ⟨oldTet, hOldSeed, hOldEdge, hOldU⟩
    have hCompletionBound :
        (completion.filter (fun tet => insert u edge ⊆ tet)).card ≤ 2 :=
      hincidence u huOutside
    have hEqual := saturated_subset_equal seed completion
      (insert u edge) hsub hSeedCount hCompletionBound
    have hFaceNew : insert u edge ⊆ newTet := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hNewU
      · exact hNewEdge hx
    have hNewSeed : newTet ∈ seed := by
      have ht : newTet ∈ completion.filter
          (fun tet => insert u edge ⊆ tet) :=
        Finset.mem_filter.mpr ⟨hNewCompletion, hFaceNew⟩
      rw [← hEqual] at ht
      exact (Finset.mem_filter.mp ht).1
    exact ⟨hvOutside, newTet, hNewSeed, hNewEdge, hNewV⟩
  induction hreach with
  | refl => exact hstart
  | tail hprevious hstep ih => exact propagate _ _ ih hstep

private theorem sealed_edge_exclusion
    (seed completion : Finset (Finset Nat))
    (edge : Finset Nat)
    (hsub : seed ⊆ completion)
    (hsaturated :
      ∀ u : Nat, u ∉ edge →
        (∃ tet ∈ seed, edge ⊆ tet ∧ u ∈ tet) →
        (seed.filter (fun tet => insert u edge ⊆ tet)).card = 2)
    (hincidence :
      ∀ u : Nat, u ∉ edge →
        (completion.filter (fun tet => insert u edge ⊆ tet)).card ≤ 2)
    (start : Nat)
    (hstart : start ∉ edge ∧
      ∃ tet ∈ seed, edge ⊆ tet ∧ start ∈ tet)
    (hconnected :
      ∀ tet ∈ completion, edge ⊆ tet →
      ∃ u : Nat, u ∈ tet ∧ u ∉ edge ∧
        Relation.ReflTransGen
          (edgeLinkAdjacent completion edge) start u) :
    ∀ tet ∈ completion, edge ⊆ tet → tet ∈ seed := by
  classical
  intro tet htCompletion hEdge
  obtain ⟨u, huTet, huOutside, hReach⟩ :=
    hconnected tet htCompletion hEdge
  obtain ⟨_, seedTet, hSeedTet, hSeedEdge, hSeedU⟩ :=
    sealed_edge_link_reachability seed completion edge
      hsub hsaturated hincidence start u hstart hReach
  have hSeedCount :
      (seed.filter (fun t => insert u edge ⊆ t)).card = 2 :=
    hsaturated u huOutside
      ⟨seedTet, hSeedTet, hSeedEdge, hSeedU⟩
  have hCompletionBound :
      (completion.filter (fun t => insert u edge ⊆ t)).card ≤ 2 :=
    hincidence u huOutside
  have hEqual := saturated_subset_equal seed completion
      (insert u edge) hsub hSeedCount hCompletionBound
  have hFaceTet : insert u edge ⊆ tet := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact huTet
    · exact hEdge hx
  have htFiltered : tet ∈ completion.filter
      (fun t => insert u edge ⊆ t) :=
    Finset.mem_filter.mpr ⟨htCompletion, hFaceTet⟩
  rw [← hEqual] at htFiltered
  exact (Finset.mem_filter.mp htFiltered).1


#print axioms saturated_subset_equal
#print axioms sealed_edge_link_reachability
#print axioms sealed_edge_exclusion

end SealedEdgeResourceBounds
end Poincare
