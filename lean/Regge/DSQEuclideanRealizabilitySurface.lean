import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Regge

/--
Triangle Euclidean-realizability predicate.

Boundary:
- no DSQ metric-validity theorem;
- no Cayley-Menger positivity theorem;
- no volume-squared theorem;
- no Regge-geometry integration theorem.
-/
def EuclideanRealizable2 (a b c : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
  a < b + c ∧ b < a + c ∧ c < a + b

theorem euclideanRealizable2_equilateral :
    EuclideanRealizable2 1 1 1 := by
  unfold EuclideanRealizable2
  norm_num

theorem not_euclideanRealizable2_collinear :
    ¬ EuclideanRealizable2 1 1 2 := by
  intro h
  norm_num [EuclideanRealizable2] at h

/-- Three edge lengths for a triangle. -/
abbrev DSQTriangleEdgeLengths : Type :=
  Fin 3 → ℝ

/-- Triangle metric-validity predicate induced by `EuclideanRealizable2`. -/
def DSQTriangleMetricValid (x : DSQTriangleEdgeLengths) : Prop :=
  EuclideanRealizable2 (x 0) (x 1) (x 2)

def DSQTriangleEquilateralEdgeLengths : DSQTriangleEdgeLengths :=
  fun _ => 1

def DSQTriangleCollinearEdgeLengths : DSQTriangleEdgeLengths :=
  fun i => if i = (2 : Fin 3) then 2 else 1

theorem dsqTriangleMetricValid_equilateral :
    DSQTriangleMetricValid DSQTriangleEquilateralEdgeLengths := by
  exact euclideanRealizable2_equilateral

theorem dsqTriangleCollinearEdgeLengths_zero :
    DSQTriangleCollinearEdgeLengths 0 = 1 := by
  unfold DSQTriangleCollinearEdgeLengths
  simp [show (0 : Fin 3) ≠ 2 by decide]

theorem dsqTriangleCollinearEdgeLengths_one :
    DSQTriangleCollinearEdgeLengths 1 = 1 := by
  unfold DSQTriangleCollinearEdgeLengths
  simp [show (1 : Fin 3) ≠ 2 by decide]

theorem dsqTriangleCollinearEdgeLengths_two :
    DSQTriangleCollinearEdgeLengths 2 = 2 := by
  unfold DSQTriangleCollinearEdgeLengths
  simp

theorem not_dsqTriangleMetricValid_collinear :
    ¬ DSQTriangleMetricValid DSQTriangleCollinearEdgeLengths := by
  intro h
  unfold DSQTriangleMetricValid at h
  rw [
    dsqTriangleCollinearEdgeLengths_zero,
    dsqTriangleCollinearEdgeLengths_one,
    dsqTriangleCollinearEdgeLengths_two
  ] at h
  exact not_euclideanRealizable2_collinear h

/--
Standalone Euclidean-realizability surface.

This is intentionally not yet a `DSQMetricValidityInputSurface`, because the
canonical triangle `DSQEdgeCoordBinding` / `DSQValidityPredicateRefinement`
has not been registered.
-/
structure DSQEuclideanRealizabilitySurface where
  inputShape : Type
  metricValid : inputShape → Prop
  satisfiable : ∃ x, metricValid x
  refutable : ∃ x, ¬ metricValid x

def dsqEuclideanRealizabilitySurface :
    DSQEuclideanRealizabilitySurface :=
  {
    inputShape := DSQTriangleEdgeLengths
    metricValid := DSQTriangleMetricValid
    satisfiable := ⟨DSQTriangleEquilateralEdgeLengths, dsqTriangleMetricValid_equilateral⟩
    refutable := ⟨DSQTriangleCollinearEdgeLengths, not_dsqTriangleMetricValid_collinear⟩
  }

def DSQ_EUCLIDEAN_REALIZABILITY_SURFACE : Prop :=
  Nonempty DSQEuclideanRealizabilitySurface

theorem dsq_euclidean_realizability_surface_open :
    DSQ_EUCLIDEAN_REALIZABILITY_SURFACE := by
  exact ⟨dsqEuclideanRealizabilitySurface⟩

end Regge
