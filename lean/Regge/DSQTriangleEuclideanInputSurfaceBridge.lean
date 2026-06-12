import Regge.DSQEuclideanRealizabilitySurface
import Regge.DSQMetricValidityInputSurface

namespace Regge

/--
Bridge the standalone triangle Euclidean-realizability surface into the
`DSQMetricValidityInputSurface` shape.

Boundary:
- no replacement of the global theorem target;
- no proof of `DSQ_METRIC_VALIDITY_THEOREM`;
- no Cayley-Menger positivity theorem;
- no volume-squared theorem;
- no Regge-geometry integration theorem.
-/
private def DSQTriangleEuclideanEdgeCoordBinding : DSQEdgeCoordBinding :=
  {
    inputShape := DSQInputShape
    realizesDSQInputShape := rfl
    complex := {
      vertexCount := 3
      edgeCount := 3
      simplexCount := 1
    }
  }

private def DSQTriangleEuclideanPredicateRefinement :
    DSQValidityPredicateRefinement :=
  {
    binding := DSQTriangleEuclideanEdgeCoordBinding
    isValidInput := fun S => S.EdgeCoord = Fin 3
  }

/--
A triangle-realizability predicate on a `DSQInputShape`.

The edge-coordinate type is not identified by definitional equality with
`Fin 3`; instead the predicate asks for three edge coordinates whose
distance-squared values satisfy `EuclideanRealizable2`.
-/
def DSQTriangleEuclideanMetricValid
    (S : DSQInputShape)
    (_ : DSQTriangleEuclideanPredicateRefinement.isValidInput S) :
    Prop :=
  ∃ e₀ e₁ e₂ : S.EdgeCoord,
    EuclideanRealizable2 (S.dSq e₀) (S.dSq e₁) (S.dSq e₂)

/--
The triangle Euclidean-realizability metric-validity input surface.

This is a local bridge into the surface shape only. It does not replace the
existing global DSQ theorem target.
-/
def DSQTriangleEuclideanMetricValidityInputSurface :
    DSQMetricValidityInputSurface :=
  {
    refinement := DSQTriangleEuclideanPredicateRefinement
    metricValid := DSQTriangleEuclideanMetricValid
  }

structure DSQTriangleEuclideanInputSurfaceBridge where
  source : DSQEuclideanRealizabilitySurface
  target : DSQMetricValidityInputSurface
  target_is_triangle_surface :
    target = DSQTriangleEuclideanMetricValidityInputSurface

def dsqTriangleEuclideanInputSurfaceBridge :
    DSQTriangleEuclideanInputSurfaceBridge :=
  {
    source := dsqEuclideanRealizabilitySurface
    target := DSQTriangleEuclideanMetricValidityInputSurface
    target_is_triangle_surface := rfl
  }

def DSQ_TRIANGLE_EUCLIDEAN_INPUT_SURFACE_BRIDGE : Prop :=
  Nonempty DSQTriangleEuclideanInputSurfaceBridge

theorem dsq_triangle_euclidean_input_surface_bridge_open :
    DSQ_TRIANGLE_EUCLIDEAN_INPUT_SURFACE_BRIDGE := by
  exact ⟨dsqTriangleEuclideanInputSurfaceBridge⟩

end Regge
