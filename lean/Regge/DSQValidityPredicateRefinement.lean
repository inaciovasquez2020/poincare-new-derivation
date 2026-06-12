import Regge.DSQEdgeCoordBinding

namespace Regge

/--
A predicate-refinement layer over the DSQ edge-coordinate binding.

Boundary:
- no metric-validity theorem;
- no Euclidean-realizability theorem;
- no Cayley-Menger positivity theorem;
- no volume-squared theorem;
- no Regge-geometry integration theorem.
-/
structure DSQValidityPredicateRefinement where
  binding : DSQEdgeCoordBinding
  isValidInput : binding.inputShape → Prop

def DSQ_VALIDITY_PREDICATE_REFINEMENT : Prop :=
  Nonempty DSQValidityPredicateRefinement

theorem dsq_validity_predicate_refinement_surface_open :
    DSQ_VALIDITY_PREDICATE_REFINEMENT := by
  let b : DSQEdgeCoordBinding :=
    Classical.choice dsq_edgecoord_binding_surface_open
  exact ⟨{
    binding := b
    isValidInput := fun _ => True
  }⟩

end Regge
