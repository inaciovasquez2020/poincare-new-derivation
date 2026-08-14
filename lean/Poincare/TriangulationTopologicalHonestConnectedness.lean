import Poincare.TriangulationTopologicalEndpointPackage
import Poincare.TriangulationTopologicalManifoldVertexLinkStarConnectedness
import Poincare.TriangulationTopologicalGeometricIntersections
import Poincare.TriangulationTopologicalGeometricConnectedness
import Mathlib.Analysis.Convex.Topology

open Set

namespace Poincare

/-- Connectedness of the honest realization forces connectedness of the finite
represented-tetrahedron overlap graph. -/
theorem ClosedTriangulationCore.tetrahedronVertexOverlapConnected_of_topologicalThreeManifold
    {K : Triangulation}
    (_hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K) :
    TetrahedronVertexOverlapConnected K := by
  classical
  refine ⟨exists_represented_tetrahedron_of_topologicalThreeManifold hM, ?_⟩
  intro tau htau rho hrho
  by_contra hnpath
  let body : Tet → Set (Nat → ℝ) := fun sigma ↦
    convexHull ℝ (triangulationTopologicalGeometricVertex ''
      (↑sigma.verts.toFinset : Set Nat))
  let adjacent : Tet → Tet → Prop := fun sigma upsilon ↦
    (sigma.verts.toFinset ∩ upsilon.verts.toFinset).Nonempty ∧ sigma ∈ K.tets
  let reachable : Tet → Prop := fun sigma ↦
    Relation.ReflTransGen adjacent tau sigma
  let A : Set (Nat → ℝ) :=
    ⋃ (sigma : {s : Tet // s ∈ K.tets}) (_ : reachable sigma.1), body sigma.1
  let B : Set (Nat → ℝ) :=
    ⋃ (sigma : {s : Tet // s ∈ K.tets}) (_ : ¬ reachable sigma.1), body sigma.1
  have hAclosed : IsClosed A := by
    apply isClosed_iUnion_of_finite
    intro sigma
    apply isClosed_iUnion_of_finite
    intro _
    exact (Set.toFinite _).isClosed_convexHull ℝ
  have hBclosed : IsClosed B := by
    apply isClosed_iUnion_of_finite
    intro sigma
    apply isClosed_iUnion_of_finite
    intro _
    exact (Set.toFinite _).isClosed_convexHull ℝ
  have hcover : (triangulationTopologicalGeometricComplex K).space ⊆ A ∪ B := by
    rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
    rintro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨sigma, hsigma, hpbody⟩ := hp
    by_cases hrs : reachable sigma
    · left
      exact Set.mem_iUnion_of_mem ⟨sigma, hsigma⟩
        (Set.mem_iUnion_of_mem hrs hpbody)
    · right
      exact Set.mem_iUnion_of_mem ⟨sigma, hsigma⟩
        (Set.mem_iUnion_of_mem hrs hpbody)
  have hdisj : A ∩ B = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hpA, hpB⟩
    simp only [A, B, Set.mem_iUnion] at hpA hpB
    obtain ⟨sigma, hsigmaReach, hpsigma⟩ := hpA
    obtain ⟨upsilon, hupsilonNot, hpupsilon⟩ := hpB
    have hinter :
        p ∈ convexHull ℝ (triangulationTopologicalGeometricVertex ''
              (↑sigma.1.verts.toFinset : Set Nat)) ∩
            convexHull ℝ (triangulationTopologicalGeometricVertex ''
              (↑upsilon.1.verts.toFinset : Set Nat)) := ⟨hpsigma, hpupsilon⟩
    rw [triangulationTopologicalTetrahedron_inter_eq_commonFace K sigma.1 upsilon.1
      sigma.2 upsilon.2] at hinter
    have hcommon : (sigma.1.verts.toFinset ∩ upsilon.1.verts.toFinset).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hinter
      simpa using hinter
    exact hupsilonNot (Relation.ReflTransGen.tail hsigmaReach ⟨hcommon, sigma.2⟩)
  rcases hM with ⟨_, _, _, _, hconnected⟩
  have hcarrier : IsConnected (triangulationTopologicalGeometricComplex K).space := by
    have himage := hconnected.image
      (fun x : triangulationTopologicalGeometricCarrier K => x.1)
      continuous_subtype_val.continuousOn
    have hrange : Set.range
        (fun x : triangulationTopologicalGeometricCarrier K => x.1) =
        (triangulationTopologicalGeometricComplex K).space := by
      ext p
      simp [triangulationTopologicalGeometricCarrier]
    rw [← hrange]
    simpa only [Set.image_univ] using himage
  have hone := (isPreconnected_iff_subset_of_disjoint_closed.mp hcarrier.isPreconnected)
    A B hAclosed hBclosed hcover (by simpa [hdisj])
  rcases hone with hsubA | hsubB
  · have hpB : triangulationTopologicalGeometricVertex rho.v0 ∈ B := by
      apply Set.mem_iUnion_of_mem ⟨rho, hrho⟩
      apply Set.mem_iUnion_of_mem hnpath
      apply subset_convexHull
      exact ⟨rho.v0, by simp [Tet.verts], rfl⟩
    have hpA : triangulationTopologicalGeometricVertex rho.v0 ∈ A :=
      hsubA (by
        rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
        exact Set.mem_iUnion_of_mem rho (Set.mem_iUnion_of_mem hrho (by
          apply subset_convexHull
          exact ⟨rho.v0, by simp [Tet.verts], rfl⟩)))
    have : triangulationTopologicalGeometricVertex rho.v0 ∈ A ∩ B := ⟨hpA, hpB⟩
    rw [hdisj] at this
    exact this
  · have hpA : triangulationTopologicalGeometricVertex tau.v0 ∈ A := by
      apply Set.mem_iUnion_of_mem ⟨tau, htau⟩
      apply Set.mem_iUnion_of_mem Relation.ReflTransGen.refl
      apply subset_convexHull
      exact ⟨tau.v0, by simp [Tet.verts], rfl⟩
    have hpB : triangulationTopologicalGeometricVertex tau.v0 ∈ B :=
      hsubB (by
        rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
        exact Set.mem_iUnion_of_mem tau (Set.mem_iUnion_of_mem htau (by
          apply subset_convexHull
          exact ⟨tau.v0, by simp [Tet.verts], rfl⟩)))
    have : triangulationTopologicalGeometricVertex tau.v0 ∈ A ∩ B := ⟨hpA, hpB⟩
    rw [hdisj] at this
    exact this

end Poincare
