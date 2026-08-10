import Poincare.Move2332CrossPolytopeEscape
import Poincare.Move23GeometricCarrierHomeomorph
import Poincare.Move32GeometricCarrierHomeomorph
import Poincare.CrossPolytopeBoundarySphere

namespace Poincare

theorem crossPolytopeEscapeAfter23_closedCore :
    ClosedTriangulationCore crossPolytopeEscapeAfter23 := by
  constructor
  · intro τ hτ
    rw [crossPolytopeEscapeAfter23_tets] at hτ
    simp at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  constructor
  · rw [crossPolytopeEscapeAfter23_tets]
    decide
  · intro a b c habc hrepresented
    rcases hrepresented with ⟨τ, hτ, ha, hb, hc⟩
    rw [crossPolytopeEscapeAfter23_tets] at hτ
    simp at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Tet.verts] at ha hb hc <;>
      rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      norm_num at habc <;>
      decide

theorem crossPolytopeEscapeAfter32One_closedCore :
    ClosedTriangulationCore crossPolytopeEscapeAfter32₁ := by
  constructor
  · intro τ hτ
    rw [crossPolytopeEscapeAfter32₁_tets] at hτ
    simp at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  constructor
  · rw [crossPolytopeEscapeAfter32₁_tets]
    decide
  · intro a b c habc hrepresented
    rcases hrepresented with ⟨τ, hτ, ha, hb, hc⟩
    rw [crossPolytopeEscapeAfter32₁_tets] at hτ
    simp at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Tet.verts] at ha hb hc <;>
      rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      norm_num at habc <;>
      decide

theorem crossPolytopeEscapeFinal_closedCore :
    ClosedTriangulationCore crossPolytopeEscapeFinal := by
  have htets : crossPolytopeEscapeFinal.tets =
      [⟨3, 6, 7, 0⟩, ⟨3, 6, 7, 4⟩, ⟨1, 6, 7, 2⟩,
       ⟨1, 6, 7, 4⟩, ⟨0, 2, 6, 7⟩, ⟨0, 2, 5, 6⟩,
       ⟨0, 2, 5, 7⟩, ⟨0, 3, 5, 6⟩, ⟨0, 3, 5, 7⟩,
       ⟨1, 2, 5, 6⟩, ⟨1, 2, 5, 7⟩, ⟨1, 3, 4, 6⟩,
       ⟨1, 3, 4, 7⟩, ⟨1, 3, 5, 6⟩, ⟨1, 3, 5, 7⟩] := by
    rfl
  constructor
  · intro τ hτ
    rw [htets] at hτ
    simp at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  constructor
  · rw [htets]
    decide
  · intro a b c habc hrepresented
    rcases hrepresented with ⟨τ, hτ, ha, hb, hc⟩
    rw [htets] at hτ
    simp at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Tet.verts] at ha hb hc <;>
      rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      norm_num at habc <;>
      decide

noncomputable def crossPolytopeEscapeMove23CarrierHomeomorph :
    triangulationTopologicalGeometricCarrier crossPolytopeBoundary4 ≃ₜ
      triangulationTopologicalGeometricCarrier crossPolytopeEscapeAfter23 :=
  crossPolytopeBoundary4_closedCore.move23GeometricCarrierHomeomorph
    crossPolytopeEscapeMove23 crossPolytopeEscapeMove23_legal

noncomputable def crossPolytopeEscapeMove32OneCarrierHomeomorph :
    triangulationTopologicalGeometricCarrier crossPolytopeEscapeAfter23 ≃ₜ
      triangulationTopologicalGeometricCarrier crossPolytopeEscapeAfter32₁ :=
  crossPolytopeEscapeAfter23_closedCore.move32GeometricCarrierHomeomorph
    crossPolytopeEscapeMove32₁ crossPolytopeEscapeMove32₁_legal

noncomputable def crossPolytopeEscapeMove32TwoCarrierHomeomorph :
    triangulationTopologicalGeometricCarrier crossPolytopeEscapeAfter32₁ ≃ₜ
      triangulationTopologicalGeometricCarrier crossPolytopeEscapeFinal :=
  crossPolytopeEscapeAfter32One_closedCore.move32GeometricCarrierHomeomorph
    crossPolytopeEscapeMove32₂ crossPolytopeEscapeMove32₂_legal

noncomputable def crossPolytopeEscapeBlockGeometricCarrierHomeomorph :
    triangulationTopologicalGeometricCarrier crossPolytopeBoundary4 ≃ₜ
      triangulationTopologicalGeometricCarrier crossPolytopeEscapeFinal :=
  (crossPolytopeEscapeMove23CarrierHomeomorph.trans
    crossPolytopeEscapeMove32OneCarrierHomeomorph).trans
      crossPolytopeEscapeMove32TwoCarrierHomeomorph

theorem crossPolytopeEscapeFinal_realizationHomeomorphicToThreeSphere :
    TriangulationRealizationHomeomorphicToThreeSphere
      crossPolytopeEscapeFinal := by
  rcases crossPolytopeBoundary4_realizationHomeomorphicToThreeSphere with ⟨h⟩
  exact ⟨crossPolytopeEscapeBlockGeometricCarrierHomeomorph.symm.trans h⟩

end Poincare
