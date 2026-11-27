import Poincare.TriangulationTopologicalNormalizedS3

namespace Poincare

/--
The global descent hypothesis is equivalent to the statement that every
closed-core realization which is a closed connected simply connected
topological three-manifold is homeomorphic to some normalized closed core.

This equivalence isolates the actual burden of the proposed descent route:
the induction in `TriangulationTopologicalNormalizedS3` does not derive
normalization from the local move lemmas; it assumes exactly the global
property that guarantees a normalized representative.
-/
def EverySimplyConnectedCoreHasNormalizedHomeomorphicTriangulation : Prop :=
  ∀ K : Triangulation,
    ClosedTriangulationCore K →
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K →
    TriangulationRealizationSimplyConnected K →
    ∃ K' : Triangulation,
      ClosedTriangulationCore K' ∧
      normalized K' ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')

/--
Exact equivalence between global strict `PhiSupport` descent and universal
existence of a normalized homeomorphic representative.

Forward direction: use strong induction on `PhiSupport`, already proved in
`exists_normalized_homeomorphic_triangulation_of_simplyConnected_global_PhiSupport_descent`.

Reverse direction: if a normalized representative exists, its support defect
is zero; for any positive starting defect this is immediately a strict
decrease. No local-move theorem is used in this reverse direction.
-/
theorem simplyConnected_global_PhiSupport_descent_iff_every_core_has_normalized_homeomorphic_triangulation :
    SimplyConnectedGlobalPhiSupportDescent ↔
      EverySimplyConnectedCoreHasNormalizedHomeomorphicTriangulation := by
  constructor
  · intro hdescent
    intro K hcore hM hSC
    exact
      exists_normalized_homeomorphic_triangulation_of_simplyConnected_global_PhiSupport_descent
        hdescent hcore hM hSC
  · intro hnormalized
    unfold SimplyConnectedGlobalPhiSupportDescent
    intro K hcore hM hSC hpositive
    obtain ⟨K', hcore', hnorm', ⟨e⟩⟩ :=
      hnormalized K hcore hM hSC
    have hzero : PhiSupport K' = 0 := by
      change PhiSupport K' = 0 at hnorm'
      exact hnorm'
    refine ⟨K', hcore', ?_, ⟨e⟩⟩
    omega

end Poincare
