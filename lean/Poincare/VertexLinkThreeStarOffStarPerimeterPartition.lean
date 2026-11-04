import Poincare.VertexLinkThreeStarOffStarComponentCrossing
import Mathlib.Tactic

namespace Poincare

/--
Finite off-star crossing partition.

The function `outside` chooses the off-star triangle across each perimeter
edge. Geometry must construct this function from closed-core link-edge
incidence; no existence or uniqueness of such a triangle is assumed here.

The components cover the off-star triangles and are pairwise disjoint.
Consequently, each perimeter edge belongs to exactly one component's
crossing count, and the component counts sum to the perimeter cardinality.
-/
theorem perimeter_component_crossing_partition
    (perimeter : Finset LinkEdge)
    (offStar : Finset LinkTriangle)
    (components : Finset (Finset LinkTriangle))
    (outside : LinkEdge → LinkTriangle)
    (houtside : ∀ e ∈ perimeter, outside e ∈ offStar)
    (hcover : ∀ σ ∈ offStar, ∃ C ∈ components, σ ∈ C)
    (hdisjoint :
      ∀ C ∈ components, ∀ D ∈ components,
        C ≠ D → ∀ σ ∈ C, σ ∉ D) :
    (∑ C ∈ components,
      (perimeter.filter (fun e => outside e ∈ C)).card) =
      perimeter.card := by
  classical
  have howner (e : LinkEdge) (he : e ∈ perimeter) :
      ∃! C : Finset LinkTriangle,
        C ∈ components ∧ outside e ∈ C := by
    obtain ⟨C, hC, heC⟩ := hcover (outside e) (houtside e he)
    refine ⟨C, ⟨hC, heC⟩, ?_⟩
    intro D hD
    by_contra hDC
    exact (hdisjoint C hC D hD.1 (Ne.symm hDC) (outside e) heC) hD.2
  have hfilter (e : LinkEdge) (he : e ∈ perimeter) :
      (components.filter (fun C => outside e ∈ C)).card = 1 := by
    obtain ⟨C, ⟨hC, heC⟩, huniq⟩ := howner e he
    have hsingle :
        components.filter (fun D => outside e ∈ D) = {C} := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        exact huniq D h
      · intro h
        subst D
        exact ⟨hC, heC⟩
    rw [hsingle]
    simp
  calc
    (∑ C ∈ components,
      (perimeter.filter (fun e => outside e ∈ C)).card) =
        ∑ C ∈ components,
          ∑ e ∈ perimeter,
            if outside e ∈ C then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      simp [Finset.sum_ite]
    _ = ∑ e ∈ perimeter,
          ∑ C ∈ components,
            if outside e ∈ C then (1 : Nat) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ perimeter, (1 : Nat) := by
      apply Finset.sum_congr rfl
      intro e he
      simpa [Finset.sum_ite] using hfilter e he
    _ = perimeter.card := by simp

end Poincare
