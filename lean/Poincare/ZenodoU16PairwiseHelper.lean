import Poincare.ZenodoU16FirstHighFan

namespace Poincare

/-- Isolated two-tetrahedron distinction using a concrete separating vertex. -/
theorem zenodoU16_firstPair_ne :
    ¬ SameTetVertices (⟨1, 2, 3, 6⟩ : Tet) (⟨1, 2, 3, 9⟩ : Tet) := by
  intro h
  have h6 : 6 ∈ (⟨1, 2, 3, 9⟩ : Tet).verts :=
    (h 6).mp (by decide)
  exact (by decide : 6 ∉ (⟨1, 2, 3, 9⟩ : Tet).verts) h6

/-- A bounded comparison of two tetrahedra by their four vertex slots.
A separating vertex certifies nonidentity of the represented vertex sets. -/
theorem tet_not_same_of_separating_vertex
    (tau sigma : Tet) (v : Nat)
    (hmem : v ∈ tau.verts) (hnot : v ∉ sigma.verts) :
    ¬ SameTetVertices tau sigma := by
  intro h
  exact hnot ((h v).mp hmem)

/-- Quantified comparison for the two subsequent tetrahedra. -/
theorem zenodoU16_first_two_followers :
    ∀ sigma ∈ ([⟨1, 2, 3, 9⟩, ⟨1, 2, 5, 10⟩] : List Tet),
      ¬ SameTetVertices (⟨1, 2, 3, 6⟩ : Tet) sigma := by
  intro sigma hsigma
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsigma
  rcases hsigma with rfl | rfl
  · exact tet_not_same_of_separating_vertex
      ⟨1, 2, 3, 6⟩ ⟨1, 2, 3, 9⟩ 6 (by decide) (by decide)
  · exact tet_not_same_of_separating_vertex
      ⟨1, 2, 3, 6⟩ ⟨1, 2, 5, 10⟩ 6 (by decide) (by decide)

/-- Pairwise vertex-set uniqueness of a bounded three-tetrahedron batch. -/
theorem zenodoU16_firstThree_pairwise :
    ([⟨1, 2, 3, 6⟩, ⟨1, 2, 3, 9⟩, ⟨1, 2, 5, 10⟩] : List Tet).Pairwise
      (fun tau sigma => ¬ SameTetVertices tau sigma) := by
  rw [List.pairwise_cons]
  constructor
  · exact zenodoU16_first_two_followers
  · rw [List.pairwise_cons]
    constructor
    · intro sigma hsigma
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsigma
      rcases hsigma with rfl
      exact tet_not_same_of_separating_vertex
        ⟨1, 2, 3, 9⟩ ⟨1, 2, 5, 10⟩ 9 (by decide) (by decide)
    · exact List.Pairwise.cons (by simp) List.Pairwise.nil

/-- Extend a verified finite pairwise batch by one new tetrahedron. -/
theorem tet_pairwise_cons_of_distinct
    (tau : Tet) (rest : List Tet)
    (hrest : rest.Pairwise (fun a b => ¬ SameTetVertices a b))
    (hdistinct : ∀ sigma ∈ rest, ¬ SameTetVertices tau sigma) :
    (tau :: rest).Pairwise (fun a b => ¬ SameTetVertices a b) := by
  exact List.Pairwise.cons hdistinct hrest

/-- The four vertex slots suffice for testing equality of represented vertex sets. -/
def tetSameVerticesBounded (tau sigma : Tet) : Prop :=
  (∀ v ∈ tau.verts, v ∈ sigma.verts) ∧
  (∀ v ∈ sigma.verts, v ∈ tau.verts)

/-- Bounded membership is equivalent to the original extensional definition. -/
theorem tetSameVerticesBounded_iff (tau sigma : Tet) :
    tetSameVerticesBounded tau sigma ↔ SameTetVertices tau sigma := by
  constructor
  · intro h v
    exact ⟨fun hv => h.1 v hv, fun hv => h.2 v hv⟩
  · intro h
    exact ⟨fun v hv => (h v).mp hv, fun v hv => (h v).mpr hv⟩

/-- Decidability follows from searching each tetrahedron's finite vertex list. -/
instance tetSameVerticesBounded_decidable (tau sigma : Tet) :
    Decidable (tetSameVerticesBounded tau sigma) := by
  unfold tetSameVerticesBounded
  infer_instance

/-- A finite, computationally decidable pairwise certificate for three tetrahedra. -/
theorem zenodoU16_firstThree_boundedPairwise :
    ([⟨1, 2, 3, 6⟩, ⟨1, 2, 3, 9⟩, ⟨1, 2, 5, 10⟩] : List Tet).Pairwise
      (fun tau sigma => ¬ tetSameVerticesBounded tau sigma) := by
  decide

/-- Transfer a finite pairwise certificate to extensional vertex-set inequality. -/
theorem tet_boundedPairwise_implies_pairwise (ts : List Tet)
    (h : ts.Pairwise (fun a b => ¬ tetSameVerticesBounded a b)) :
    ts.Pairwise (fun a b => ¬ SameTetVertices a b) := by
  exact h.imp (by
    intro a b hab hs
    exact hab ((tetSameVerticesBounded_iff a b).mpr hs))

/-- Exhaustive finite vertex-set uniqueness check for the 104-tetrahedron fixture.
No extensional quantification over Nat is evaluated by decide. -/
theorem zenodoU16_full_boundedPairwise :
    zenodoU16Original.tets.Pairwise
      (fun tau sigma => ¬ tetSameVerticesBounded tau sigma) := by
  decide

/-- Full 104-tetrahedron vertex-set uniqueness in the original core predicate. -/
theorem zenodoU16_full_pairwise :
    zenodoU16Original.tets.Pairwise
      (fun tau sigma => ¬ SameTetVertices tau sigma) := by
  exact tet_boundedPairwise_implies_pairwise
    zenodoU16Original.tets zenodoU16_full_boundedPairwise

/-- Face incidence checked only at triples of vertices of represented tetrahedra. -/
def BoundedRepresentedFaceIncidence (K : Triangulation) : Prop :=
  ∀ tau ∈ K.tets,
    ∀ a ∈ tau.verts, ∀ b ∈ tau.verts, ∀ c ∈ tau.verts,
      [a, b, c].Nodup →
      (K.tets.filter (fun sigma =>
        a ∈ sigma.verts ∧ b ∈ sigma.verts ∧ c ∈ sigma.verts)).length = 2

/-- Finite represented-face incidence is exactly the third closed-core condition. -/
theorem boundedRepresentedFaceIncidence_iff (K : Triangulation) :
    BoundedRepresentedFaceIncidence K ↔
      (∀ a b c : Nat,
        [a, b, c].Nodup →
        (∃ tau ∈ K.tets,
          a ∈ tau.verts ∧ b ∈ tau.verts ∧ c ∈ tau.verts) →
        (K.tets.filter (fun sigma =>
          a ∈ sigma.verts ∧ b ∈ sigma.verts ∧ c ∈ sigma.verts)).length = 2) := by
  constructor
  · intro h a b c hdistinct hex
    rcases hex with ⟨tau, htau, ha, hb, hc⟩
    exact h tau htau a ha b hb c hc hdistinct
  · intro h tau htau a ha b hb c hc hdistinct
    exact h a b c hdistinct ⟨tau, htau, ha, hb, hc⟩

/-- All quantified variables are bounded by finite tetrahedron vertex lists. -/
instance boundedRepresentedFaceIncidence_decidable (K : Triangulation) :
    Decidable (BoundedRepresentedFaceIncidence K) := by
  unfold BoundedRepresentedFaceIncidence
  infer_instance

/-- First bounded batch: exact incidence counts for the four distinct
faces of the first U(16) tetrahedron ⟨1,2,3,6⟩. -/
theorem zenodoU16_firstTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 3 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 6 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 6 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 6 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Second bounded batch: exact incidence for the four triangular faces
of U(16) tetrahedron ⟨1,2,3,9⟩. -/
theorem zenodoU16_secondTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 3 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Third finite batch: the four triangular faces of U(16) tet ⟨1,2,5,10⟩. -/
theorem zenodoU16_thirdTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 5 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      2 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Fourth finite batch: the four triangular faces of U(16) tet ⟨1,2,5,16⟩. -/
theorem zenodoU16_fourthTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 5 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      2 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Fifth finite batch: the four triangular faces of U(16) tet ⟨1,2,6,8⟩. -/
theorem zenodoU16_fifthTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 6 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      2 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Sixth finite batch: the four triangular faces of U(16) tet ⟨1,2,8,16⟩. -/
theorem zenodoU16_sixthTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      2 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Seventh finite batch: four faces of U(16) tet ⟨1,2,9,10⟩. -/
theorem zenodoU16_seventhTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 2 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      2 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Eighth finite batch: four faces of U(16) tet ⟨1,3,6,13⟩. -/
theorem zenodoU16_eighthTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 6 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      3 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Ninth finite batch: four faces of U(16) tet ⟨1,3,9,12⟩. -/
theorem zenodoU16_ninthTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      3 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Poincare
