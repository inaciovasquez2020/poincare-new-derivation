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


def twoBoundaryVertexWedgeLeftBlock
    (σ : LinkTriangle) : Prop :=
  σ ∈
    [
      ⟨2, 3, 4⟩,
      ⟨1, 3, 4⟩,
      ⟨1, 2, 4⟩,
      ⟨1, 2, 3⟩
    ]


theorem twoBoundaryVertexWedge_adjacent_preserves_left
    (σ ρ : LinkTriangle)
    (hadj :
      VertexLinkAdjacent
        twoBoundaryVertexWedge 0 σ ρ)
    (hleft :
      twoBoundaryVertexWedgeLeftBlock σ) :
    twoBoundaryVertexWedgeLeftBlock ρ := by

  rcases hadj with
    ⟨_, hρ, hshare⟩

  simp [
    twoBoundaryVertexWedgeLeftBlock
  ] at hleft

  rw [
    twoBoundaryVertexWedge_link_zero
  ] at hρ

  simp at hρ

  rcases hleft with
      rfl | rfl | rfl | rfl <;>
    rcases hρ with
      rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl

  all_goals
    simp [
      twoBoundaryVertexWedgeLeftBlock
    ]

  all_goals
    revert hshare
    native_decide


theorem twoBoundaryVertexWedge_reflTransGen_preserves_left
    (σ ρ : LinkTriangle)
    (hpath :
      Relation.ReflTransGen
        (VertexLinkAdjacent
          twoBoundaryVertexWedge 0)
        σ ρ)
    (hleft :
      twoBoundaryVertexWedgeLeftBlock σ) :
    twoBoundaryVertexWedgeLeftBlock ρ := by

  exact
    Relation.ReflTransGen.trans_induction_on
      (motive :=
        fun {a b} _ =>
          twoBoundaryVertexWedgeLeftBlock a →
            twoBoundaryVertexWedgeLeftBlock b)
      hpath
      (fun _ ha => ha)
      (fun hstep ha =>
        twoBoundaryVertexWedge_adjacent_preserves_left
          _ _ hstep ha)
      (fun _ _ ih₁ ih₂ ha =>
        ih₂ (ih₁ ha))
      hleft


theorem twoBoundaryVertexWedge_link_zero_not_connected :
    ¬ VertexLinkConnected
        twoBoundaryVertexWedge 0 := by

  intro hconnected

  unfold VertexLinkConnected at hconnected

  let σL : LinkTriangle :=
    ⟨2, 3, 4⟩

  let σR : LinkTriangle :=
    ⟨6, 7, 8⟩

  have hσL :
      σL ∈
        vertexLinkTriangles
          twoBoundaryVertexWedge 0 := by
    rw [twoBoundaryVertexWedge_link_zero]
    simp [σL]

  have hσR :
      σR ∈
        vertexLinkTriangles
          twoBoundaryVertexWedge 0 := by
    rw [twoBoundaryVertexWedge_link_zero]
    simp [σR]

  have hpath :
      Relation.ReflTransGen
        (VertexLinkAdjacent
          twoBoundaryVertexWedge 0)
        σL σR :=
    hconnected
      σL hσL
      σR hσR

  have hleft :
      twoBoundaryVertexWedgeLeftBlock σL := by
    simp [
      twoBoundaryVertexWedgeLeftBlock,
      σL
    ]

  have hrightForcedLeft :
      twoBoundaryVertexWedgeLeftBlock σR :=
    twoBoundaryVertexWedge_reflTransGen_preserves_left
      σL σR hpath hleft

  have hrightNotLeft :
      ¬ twoBoundaryVertexWedgeLeftBlock σR := by
    simp [
      twoBoundaryVertexWedgeLeftBlock,
      σR
    ]

  exact
    hrightNotLeft hrightForcedLeft


theorem exists_closedCore_with_disconnected_vertexLink :
    ∃ K : Triangulation,
      ClosedTriangulationCore K ∧
      ∃ v ∈ vertexSupport K,
        ¬ VertexLinkConnected K v := by

  refine
    ⟨twoBoundaryVertexWedge,
     twoBoundaryVertexWedge_closedCore,
     0,
     ?_,
     twoBoundaryVertexWedge_link_zero_not_connected⟩

  native_decide

end Poincare
