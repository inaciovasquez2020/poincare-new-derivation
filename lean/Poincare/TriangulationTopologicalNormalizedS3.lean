import Poincare.TriangulationTopologicalFourSimplexRealizationChange
import Poincare.TriangulationTopologicalS3
import Poincare.TriangulationTopologicalHomeomorphTransport
import Poincare.TriangulationTopologicalHonestConnectedness

namespace Poincare

/-- A closed, overlap-connected zero-defect triangulation has genuine
topology-bearing realization homeomorphic to the unit three-sphere. -/
theorem ClosedTriangulationCore.realizationHomeomorphicToThreeSphere_of_PhiSupport_eq_zero
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    (hconn : TetrahedronVertexOverlapConnected K)
    {tau : Tet}
    (htauK : tau ∈ K.tets)
    (htau : tau.verts.Nodup) :
    TriangulationRealizationHomeomorphicToThreeSphere K := by
  obtain ⟨hfront⟩ :=
    hcore.nonempty_homeomorph_fourSimplexFrontier hPhi hconn htauK htau
  exact ⟨hfront.trans fourSimplexFrontierHomeomorphUnitSphere⟩

/-- The normalized form of genuine three-sphere recognition. -/
theorem ClosedTriangulationCore.realizationHomeomorphicToThreeSphere_of_normalized
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hnorm : normalized K)
    (hconn : TetrahedronVertexOverlapConnected K)
    {tau : Tet}
    (htauK : tau ∈ K.tets)
    (htau : tau.verts.Nodup) :
    TriangulationRealizationHomeomorphicToThreeSphere K := by
  exact hcore.realizationHomeomorphicToThreeSphere_of_PhiSupport_eq_zero
    hnorm hconn htauK htau

/-- The single explicit global hypothesis used by the conditional Poincare
package: every positive-defect closed, connected, simply connected
three-manifold realization admits a topology-preserving strict `PhiSupport`
descent to another closed triangulation core. -/
def SimplyConnectedGlobalPhiSupportDescent : Prop :=
  ∀ K : Triangulation,
    ClosedTriangulationCore K →
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K →
    TriangulationRealizationSimplyConnected K →
    0 < PhiSupport K →
    ∃ K' : Triangulation,
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')

/-- Under the explicit global descent hypothesis, strong induction on
`PhiSupport` reaches a normalized closed core while composing the carrier
homeomorphisms along the descent chain. -/
theorem exists_normalized_homeomorphic_triangulation_of_simplyConnected_global_PhiSupport_descent
    (hdescent : SimplyConnectedGlobalPhiSupportDescent)
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hSC : TriangulationRealizationSimplyConnected K) :
    ∃ K' : Triangulation,
      ClosedTriangulationCore K' ∧
      normalized K' ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K') := by
  unfold SimplyConnectedGlobalPhiSupportDescent at hdescent
  let P : Nat → Prop := fun n =>
    ∀ L : Triangulation,
      PhiSupport L = n →
      ClosedTriangulationCore L →
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold L →
      TriangulationRealizationSimplyConnected L →
      ∃ L' : Triangulation,
        ClosedTriangulationCore L' ∧
        normalized L' ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier L ≃ₜ
            triangulationTopologicalGeometricCarrier L')
  have hP : ∀ n : Nat, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp [P]
      intro L hPhi hcoreL hML hSCL
      by_cases hn : n = 0
      · have hnorm : normalized L := by
          unfold normalized
          exact hPhi.trans hn
        exact
          ⟨L, hcoreL, hnorm,
            ⟨Homeomorph.refl
              (triangulationTopologicalGeometricCarrier L)⟩⟩
      · have hposN : 0 < n := Nat.pos_of_ne_zero hn
        have hpos : 0 < PhiSupport L := by
          rw [hPhi]
          exact hposN
        obtain ⟨L', hcore', hlt, ⟨e⟩⟩ :=
          hdescent L hcoreL hML hSCL hpos
        have hML' :
            TriangulationRealizationIsClosedConnectedTopologicalThreeManifold L' :=
          triangulationRealizationIsClosedConnectedTopologicalThreeManifold_of_homeomorph
            e hML
        have hSCL' : TriangulationRealizationSimplyConnected L' :=
          triangulationRealizationSimplyConnected_of_homeomorph e hSCL
        have hltN : PhiSupport L' < n := by
          rw [← hPhi]
          exact hlt
        have hrec := ih (PhiSupport L') hltN
        dsimp [P] at hrec
        obtain ⟨L'', hcore'', hnorm'', ⟨e'⟩⟩ :=
          hrec L' rfl hcore' hML' hSCL'
        exact ⟨L'', hcore'', hnorm'', ⟨e.trans e'⟩⟩
  have hstart := hP (PhiSupport K)
  dsimp [P] at hstart
  exact hstart K rfl hcore hM hSC

end Poincare
