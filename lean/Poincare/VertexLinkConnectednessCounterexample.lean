import Poincare.VertexLink

namespace Poincare

instance instDecidableSameTetVerticesForCounterexample
    (τ σ : Tet) :
    Decidable (SameTetVertices τ σ) := by
  by_cases h :
      sameTetVerticesBool τ σ = true
  · exact
      isTrue
        ((sameTetVerticesBool_eq_true_iff τ σ).1 h)
  · exact
      isFalse
        (fun hs =>
          h
            ((sameTetVerticesBool_eq_true_iff τ σ).2 hs))


def wedgeA0 : Tet := ⟨1, 2, 3, 4⟩
def wedgeA1 : Tet := ⟨0, 2, 3, 4⟩
def wedgeA2 : Tet := ⟨0, 1, 3, 4⟩
def wedgeA3 : Tet := ⟨0, 1, 2, 4⟩
def wedgeA4 : Tet := ⟨0, 1, 2, 3⟩

def wedgeB0 : Tet := ⟨5, 6, 7, 8⟩
def wedgeB1 : Tet := ⟨0, 6, 7, 8⟩
def wedgeB2 : Tet := ⟨0, 5, 7, 8⟩
def wedgeB3 : Tet := ⟨0, 5, 6, 8⟩
def wedgeB4 : Tet := ⟨0, 5, 6, 7⟩


def twoBoundaryVertexWedge : Triangulation :=
  {
    tets :=
      [
        wedgeA0,
        wedgeA1,
        wedgeA2,
        wedgeA3,
        wedgeA4,
        wedgeB0,
        wedgeB1,
        wedgeB2,
        wedgeB3,
        wedgeB4
      ]
  }


theorem twoBoundaryVertexWedge_closedCore :
    ClosedTriangulationCore
      twoBoundaryVertexWedge := by

  constructor

  · intro τ hτ

    simp [twoBoundaryVertexWedge] at hτ

    rcases hτ with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
      native_decide

  constructor

  · native_decide

  · intro a b c habc hrepresented

    rcases hrepresented with
      ⟨τ, hτ, ha, hb, hc⟩

    simp [twoBoundaryVertexWedge] at hτ

    rcases hτ with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
      simp [
        wedgeA0,
        wedgeA1,
        wedgeA2,
        wedgeA3,
        wedgeA4,
        wedgeB0,
        wedgeB1,
        wedgeB2,
        wedgeB3,
        wedgeB4,
        Tet.verts
      ] at ha hb hc <;>
      rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      norm_num at habc <;>
      native_decide


theorem twoBoundaryVertexWedge_link_zero :
    vertexLinkTriangles
        twoBoundaryVertexWedge 0 =
      [
        ⟨2, 3, 4⟩,
        ⟨1, 3, 4⟩,
        ⟨1, 2, 4⟩,
        ⟨1, 2, 3⟩,
        ⟨6, 7, 8⟩,
        ⟨5, 7, 8⟩,
        ⟨5, 6, 8⟩,
        ⟨5, 6, 7⟩
      ] := by
  native_decide

end Poincare
