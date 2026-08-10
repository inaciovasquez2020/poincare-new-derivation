import Mathlib.Analysis.Convex.Topology
import Poincare.TriangulationTopologicalGeometricDecomposition

open Set

namespace Poincare

noncomputable local instance (K : Triangulation) :
    TopologicalSpace (triangulationTopologicalGeometricCarrier K) := by
  unfold triangulationTopologicalGeometricCarrier
  infer_instance

/--
The canonical topology-bearing realization is compact.  This follows directly
from its exact decomposition as the finite union of the convex hulls of the
finite vertex sets of the represented tetrahedra.
-/
theorem triangulationTopologicalGeometricComplex_space_isCompact
    (K : Triangulation) :
    IsCompact (triangulationTopologicalGeometricComplex K).space := by
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  apply K.tets.finite_toSet.isCompact_biUnion
  intro τ hτ
  exact
    (Finset.finite_toSet τ.verts.toFinset).image
      triangulationTopologicalGeometricVertex |>.isCompact_convexHull ℝ

/-- Compactness stated intrinsically on the realization subtype. -/
theorem triangulationTopologicalGeometricCarrier_univ_isCompact
    (K : Triangulation) :
    IsCompact
      (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) := by
  change IsCompact
    (Set.univ : Set ↥(triangulationTopologicalGeometricComplex K).space)
  letI : CompactSpace ↥(triangulationTopologicalGeometricComplex K).space :=
    isCompact_iff_compactSpace.mp
      (triangulationTopologicalGeometricComplex_space_isCompact K)
  exact isCompact_univ

end Poincare
