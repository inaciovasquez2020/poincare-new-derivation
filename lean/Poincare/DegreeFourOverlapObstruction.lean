import Poincare.VertexLinkConnectednessCounterexample
import Poincare.TriangulationTopologicalGeometricConnectedness
import Poincare.SupportDegreeFour

namespace Poincare

/-- Closed-core face incidence together with connectedness of the represented
tetrahedron overlap graph does not make the target-obstructed branch of a
degree-four vertex globally equal to one four-simplex boundary.  The wedge of
two such boundaries is the minimal obstruction; link connectedness (as
provided by the genuine manifold hypotheses) is additionally necessary. -/
theorem exists_overlapConnected_closedCore_degreeFour_not_PhiSupport_zero :
    ∃ K : Triangulation,
      ClosedTriangulationCore K ∧
      TetrahedronVertexOverlapConnected K ∧
      (∃ v ∈ vertexSupport K, vertexDegree K v = 4) ∧
      PhiSupport K ≠ 0 := by
  refine ⟨twoBoundaryVertexWedge, twoBoundaryVertexWedge_closedCore, ?_, ?_, ?_⟩
  · constructor
    · exact ⟨wedgeA0, by simp [twoBoundaryVertexWedge]⟩
    · intro τ hτ ρ hρ
      let R := fun σ υ : Tet ↦
        (σ.verts.toFinset ∩ υ.verts.toFinset).Nonempty ∧
          σ ∈ twoBoundaryVertexWedge.tets
      have toHub : Relation.ReflTransGen R τ wedgeA1 := by
        by_cases hB0 : τ = wedgeB0
        · subst τ
          exact Relation.ReflTransGen.tail
            (Relation.ReflTransGen.single (show R wedgeB0 wedgeB1 from ⟨by
              simp [R, wedgeB0, wedgeB1, Tet.verts], by
              simp [R, twoBoundaryVertexWedge]⟩))
            (show R wedgeB1 wedgeA1 from ⟨by
              simp [R, wedgeB1, wedgeA1, Tet.verts], by
              simp [R, twoBoundaryVertexWedge]⟩)
        · apply Relation.ReflTransGen.single
          constructor
          · simp [twoBoundaryVertexWedge] at hτ
            rcases hτ with rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl <;>
              simp_all [wedgeA0, wedgeA1, wedgeA2, wedgeA3, wedgeA4,
                wedgeB0, wedgeB1, wedgeB2, wedgeB3, wedgeB4, Tet.verts]
          · exact hτ
      have fromHub : Relation.ReflTransGen R wedgeA1 ρ := by
        by_cases hB0 : ρ = wedgeB0
        · subst ρ
          exact Relation.ReflTransGen.tail
            (Relation.ReflTransGen.single (show R wedgeA1 wedgeB1 from ⟨by
              simp [R, wedgeA1, wedgeB1, Tet.verts], by
              simp [R, twoBoundaryVertexWedge]⟩))
            (show R wedgeB1 wedgeB0 from ⟨by
              simp [R, wedgeB1, wedgeB0, Tet.verts], by
              simp [R, twoBoundaryVertexWedge]⟩)
        · apply Relation.ReflTransGen.single
          constructor
          · simp [twoBoundaryVertexWedge] at hρ
            rcases hρ with rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl <;>
              simp_all [wedgeA0, wedgeA1, wedgeA2, wedgeA3, wedgeA4,
                wedgeB0, wedgeB1, wedgeB2, wedgeB3, wedgeB4, Tet.verts]
          · simp [R, twoBoundaryVertexWedge]
      exact toHub.trans fromHub
  · exact ⟨1, by decide, by decide⟩
  · decide

end Poincare
