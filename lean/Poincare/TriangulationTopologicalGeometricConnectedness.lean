import Mathlib.Analysis.Convex.PathConnected
import Poincare.TriangulationTopologicalGeometricIntersections

open Set

namespace Poincare

noncomputable local instance connectednessDecidableEqPi :
    DecidableEq (Nat → ℝ) := Classical.decEq _

@[reducible] noncomputable local instance connectednessCarrierTopologicalSpace
    (K : Triangulation) :
    TopologicalSpace (triangulationTopologicalGeometricCarrier K) := by
  unfold triangulationTopologicalGeometricCarrier
  infer_instance

/--
The represented tetrahedra form a nonempty connected overlap graph, where an
edge means that the two tetrahedra share a vertex label.  This is purely a
condition on the information actually carried by `Triangulation`.
-/
def TetrahedronVertexOverlapConnected (K : Triangulation) : Prop :=
  (∃ τ : Tet, τ ∈ K.tets) ∧
    ∀ τ, τ ∈ K.tets → ∀ ρ, ρ ∈ K.tets →
      Relation.ReflTransGen
        (fun σ υ : Tet ↦
          (σ.verts.toFinset ∩ υ.verts.toFinset).Nonempty ∧ σ ∈ K.tets)
        τ ρ

/--
Connectedness of the represented tetrahedron overlap graph implies genuine
connectedness of the topology-bearing geometric realization.
-/
theorem triangulationTopologicalGeometricComplex_space_isConnected
    (K : Triangulation) (hK : TetrahedronVertexOverlapConnected K) :
    IsConnected (triangulationTopologicalGeometricComplex K).space := by
  let cell : Tet → Set (Nat → ℝ) := fun τ ↦
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑τ.verts.toFinset : Set Nat))
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  apply IsConnected.biUnion_of_reflTransGen
  · exact ⟨hK.1.choose, hK.1.choose_spec⟩
  · intro τ hτ
    apply (convex_convexHull ℝ _).isConnected
    refine ⟨triangulationTopologicalGeometricVertex τ.v0,
      subset_convexHull ℝ _ ?_⟩
    exact ⟨τ.v0, List.mem_toFinset.mpr (by
      change τ.v0 ∈ [τ.v0, τ.v1, τ.v2, τ.v3]
      exact List.mem_cons_self), rfl⟩
  · intro τ hτ ρ hρ
    refine (hK.2 τ hτ ρ hρ).mono ?_
    intro σ υ hσυ
    refine ⟨?_, hσυ.2⟩
    obtain ⟨v, hv⟩ := hσυ.1
    have hv' := Finset.mem_inter.mp hv
    refine ⟨triangulationTopologicalGeometricVertex v, ?_, ?_⟩
    · exact subset_convexHull ℝ _ ⟨v, hv'.1, rfl⟩
    · exact subset_convexHull ℝ _ ⟨v, hv'.2, rfl⟩

/-- The corresponding realization subtype is connected under the same exact
combinatorial hypothesis. -/
theorem triangulationTopologicalGeometricCarrier_univ_isConnected
    (K : Triangulation) (hK : TetrahedronVertexOverlapConnected K) :
    IsConnected
      (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) := by
  rw [← connectedSpace_iff_univ]
  change ConnectedSpace ↥(triangulationTopologicalGeometricComplex K).space
  exact isConnected_iff_connectedSpace.mp
    (triangulationTopologicalGeometricComplex_space_isConnected K hK)

end Poincare
