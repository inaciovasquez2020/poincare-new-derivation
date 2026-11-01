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

/-- Tenth finite batch: four faces of U(16) tet ⟨1,3,12,13⟩. -/
theorem zenodoU16_tenthTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      3 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Eleventh finite batch: four faces of U(16) tet ⟨1,4,9,11⟩. -/
theorem zenodoU16_eleventhTet_faceIncidence :
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      1 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau =>
      4 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 12. -/
theorem zenodoU16_faceBatch_12 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 13. -/
theorem zenodoU16_faceBatch_13 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 14. -/
theorem zenodoU16_faceBatch_14 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 15. -/
theorem zenodoU16_faceBatch_15 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 16. -/
theorem zenodoU16_faceBatch_16 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 17. -/
theorem zenodoU16_faceBatch_17 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 18. -/
theorem zenodoU16_faceBatch_18 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 19. -/
theorem zenodoU16_faceBatch_19 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 20. -/
theorem zenodoU16_faceBatch_20 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 21. -/
theorem zenodoU16_faceBatch_21 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 22. -/
theorem zenodoU16_faceBatch_22 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 23. -/
theorem zenodoU16_faceBatch_23 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 24. -/
theorem zenodoU16_faceBatch_24 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 25. -/
theorem zenodoU16_faceBatch_25 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 26. -/
theorem zenodoU16_faceBatch_26 :
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 1 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 12 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 27. -/
theorem zenodoU16_faceBatch_27 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 4 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 28. -/
theorem zenodoU16_faceBatch_28 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 4 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 29. -/
theorem zenodoU16_faceBatch_29 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 6 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 30. -/
theorem zenodoU16_faceBatch_30 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 31. -/
theorem zenodoU16_faceBatch_31 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 3 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 32. -/
theorem zenodoU16_faceBatch_32 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 33. -/
theorem zenodoU16_faceBatch_33 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 34. -/
theorem zenodoU16_faceBatch_34 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 35. -/
theorem zenodoU16_faceBatch_35 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 36. -/
theorem zenodoU16_faceBatch_36 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 37. -/
theorem zenodoU16_faceBatch_37 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 38. -/
theorem zenodoU16_faceBatch_38 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 39. -/
theorem zenodoU16_faceBatch_39 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 40. -/
theorem zenodoU16_faceBatch_40 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 41. -/
theorem zenodoU16_faceBatch_41 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 42. -/
theorem zenodoU16_faceBatch_42 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 43. -/
theorem zenodoU16_faceBatch_43 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 44. -/
theorem zenodoU16_faceBatch_44 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 11 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 45. -/
theorem zenodoU16_faceBatch_45 :
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 2 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 13 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 46. -/
theorem zenodoU16_faceBatch_46 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 5 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 47. -/
theorem zenodoU16_faceBatch_47 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 5 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 48. -/
theorem zenodoU16_faceBatch_48 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 49. -/
theorem zenodoU16_faceBatch_49 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 50. -/
theorem zenodoU16_faceBatch_50 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 4 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 51. -/
theorem zenodoU16_faceBatch_51 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 52. -/
theorem zenodoU16_faceBatch_52 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 53. -/
theorem zenodoU16_faceBatch_53 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 54. -/
theorem zenodoU16_faceBatch_54 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 55. -/
theorem zenodoU16_faceBatch_55 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 56. -/
theorem zenodoU16_faceBatch_56 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 57. -/
theorem zenodoU16_faceBatch_57 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 58. -/
theorem zenodoU16_faceBatch_58 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 59. -/
theorem zenodoU16_faceBatch_59 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 60. -/
theorem zenodoU16_faceBatch_60 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 11 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 61. -/
theorem zenodoU16_faceBatch_61 :
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 3 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 14 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 62. -/
theorem zenodoU16_faceBatch_62 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 6 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 63. -/
theorem zenodoU16_faceBatch_63 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 6 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 64. -/
theorem zenodoU16_faceBatch_64 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 65. -/
theorem zenodoU16_faceBatch_65 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 66. -/
theorem zenodoU16_faceBatch_66 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 5 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 67. -/
theorem zenodoU16_faceBatch_67 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 68. -/
theorem zenodoU16_faceBatch_68 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 69. -/
theorem zenodoU16_faceBatch_69 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 70. -/
theorem zenodoU16_faceBatch_70 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 71. -/
theorem zenodoU16_faceBatch_71 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 72. -/
theorem zenodoU16_faceBatch_72 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 11 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 73. -/
theorem zenodoU16_faceBatch_73 :
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 4 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 12 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 74. -/
theorem zenodoU16_faceBatch_74 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 75. -/
theorem zenodoU16_faceBatch_75 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 7 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 76. -/
theorem zenodoU16_faceBatch_76 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 77. -/
theorem zenodoU16_faceBatch_77 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 78. -/
theorem zenodoU16_faceBatch_78 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 6 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 79. -/
theorem zenodoU16_faceBatch_79 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 80. -/
theorem zenodoU16_faceBatch_80 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 81. -/
theorem zenodoU16_faceBatch_81 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 82. -/
theorem zenodoU16_faceBatch_82 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 12 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 83. -/
theorem zenodoU16_faceBatch_83 :
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 5 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 13 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 84. -/
theorem zenodoU16_faceBatch_84 :
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 85. -/
theorem zenodoU16_faceBatch_85 :
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 8 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 86. -/
theorem zenodoU16_faceBatch_86 :
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 87. -/
theorem zenodoU16_faceBatch_87 :
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 88. -/
theorem zenodoU16_faceBatch_88 :
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 7 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 89. -/
theorem zenodoU16_faceBatch_89 :
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 90. -/
theorem zenodoU16_faceBatch_90 :
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 91. -/
theorem zenodoU16_faceBatch_91 :
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 6 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 14 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 92. -/
theorem zenodoU16_faceBatch_92 :
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 93. -/
theorem zenodoU16_faceBatch_93 :
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 9 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 94. -/
theorem zenodoU16_faceBatch_94 :
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 95. -/
theorem zenodoU16_faceBatch_95 :
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 96. -/
theorem zenodoU16_faceBatch_96 :
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 8 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 15 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 97. -/
theorem zenodoU16_faceBatch_97 :
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 7 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 11 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 98. -/
theorem zenodoU16_faceBatch_98 :
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 99. -/
theorem zenodoU16_faceBatch_99 :
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 10 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 100. -/
theorem zenodoU16_faceBatch_100 :
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 9 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 8 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 101. -/
theorem zenodoU16_faceBatch_101 :
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 11 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 102. -/
theorem zenodoU16_faceBatch_102 :
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 14 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 10 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 9 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 14 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 103. -/
theorem zenodoU16_faceBatch_103 :
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 12 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 11 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 10 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 11 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 15 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Finite face batch 104. -/
theorem zenodoU16_faceBatch_104 :
    (zenodoU16Original.tets.filter (fun tau => 11 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 13 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 11 ∈ tau.verts ∧ 12 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 11 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 ∧
    (zenodoU16Original.tets.filter (fun tau => 12 ∈ tau.verts ∧ 13 ∈ tau.verts ∧ 16 ∈ tau.verts)).length = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Assembly base case: quantify the four vertex slots of the first U(16)
tetrahedron, rather than checking only four ordered face triples. -/
theorem zenodoU16_firstTet_quantifiedFaceIncidence :
    ∀ a ∈ (⟨1, 2, 3, 6⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 2, 3, 6⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 2, 3, 6⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧ b ∈ sigma.verts ∧ c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 2. -/
theorem zenodoU16_quantifiedFaceBatch_2 :
    ∀ a ∈ (⟨1, 2, 3, 9⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 2, 3, 9⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 2, 3, 9⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 3. -/
theorem zenodoU16_quantifiedFaceBatch_3 :
    ∀ a ∈ (⟨1, 2, 5, 10⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 2, 5, 10⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 2, 5, 10⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 4. -/
theorem zenodoU16_quantifiedFaceBatch_4 :
    ∀ a ∈ (⟨1, 2, 5, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 2, 5, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 2, 5, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 5. -/
theorem zenodoU16_quantifiedFaceBatch_5 :
    ∀ a ∈ (⟨1, 2, 6, 8⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 2, 6, 8⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 2, 6, 8⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 6. -/
theorem zenodoU16_quantifiedFaceBatch_6 :
    ∀ a ∈ (⟨1, 2, 8, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 2, 8, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 2, 8, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 7. -/
theorem zenodoU16_quantifiedFaceBatch_7 :
    ∀ a ∈ (⟨1, 2, 9, 10⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 2, 9, 10⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 2, 9, 10⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 8. -/
theorem zenodoU16_quantifiedFaceBatch_8 :
    ∀ a ∈ (⟨1, 3, 6, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 3, 6, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 3, 6, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 9. -/
theorem zenodoU16_quantifiedFaceBatch_9 :
    ∀ a ∈ (⟨1, 3, 9, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 3, 9, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 3, 9, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 10. -/
theorem zenodoU16_quantifiedFaceBatch_10 :
    ∀ a ∈ (⟨1, 3, 12, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 3, 12, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 3, 12, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 11. -/
theorem zenodoU16_quantifiedFaceBatch_11 :
    ∀ a ∈ (⟨1, 4, 9, 11⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 4, 9, 11⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 4, 9, 11⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 12. -/
theorem zenodoU16_quantifiedFaceBatch_12 :
    ∀ a ∈ (⟨1, 4, 9, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 4, 9, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 4, 9, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 13. -/
theorem zenodoU16_quantifiedFaceBatch_13 :
    ∀ a ∈ (⟨1, 4, 11, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 4, 11, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 4, 11, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 14. -/
theorem zenodoU16_quantifiedFaceBatch_14 :
    ∀ a ∈ (⟨1, 4, 15, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 4, 15, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 4, 15, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 15. -/
theorem zenodoU16_quantifiedFaceBatch_15 :
    ∀ a ∈ (⟨1, 5, 7, 10⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 5, 7, 10⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 5, 7, 10⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 16. -/
theorem zenodoU16_quantifiedFaceBatch_16 :
    ∀ a ∈ (⟨1, 5, 7, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 5, 7, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 5, 7, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 17. -/
theorem zenodoU16_quantifiedFaceBatch_17 :
    ∀ a ∈ (⟨1, 6, 8, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 6, 8, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 6, 8, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 18. -/
theorem zenodoU16_quantifiedFaceBatch_18 :
    ∀ a ∈ (⟨1, 6, 13, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 6, 13, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 6, 13, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 19. -/
theorem zenodoU16_quantifiedFaceBatch_19 :
    ∀ a ∈ (⟨1, 7, 10, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 7, 10, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 7, 10, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 20. -/
theorem zenodoU16_quantifiedFaceBatch_20 :
    ∀ a ∈ (⟨1, 7, 15, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 7, 15, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 7, 15, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 21. -/
theorem zenodoU16_quantifiedFaceBatch_21 :
    ∀ a ∈ (⟨1, 8, 9, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 8, 9, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 8, 9, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 22. -/
theorem zenodoU16_quantifiedFaceBatch_22 :
    ∀ a ∈ (⟨1, 8, 9, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 8, 9, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 8, 9, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 23. -/
theorem zenodoU16_quantifiedFaceBatch_23 :
    ∀ a ∈ (⟨1, 8, 12, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 8, 12, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 8, 12, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 24. -/
theorem zenodoU16_quantifiedFaceBatch_24 :
    ∀ a ∈ (⟨1, 9, 10, 11⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 9, 10, 11⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 9, 10, 11⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 25. -/
theorem zenodoU16_quantifiedFaceBatch_25 :
    ∀ a ∈ (⟨1, 10, 11, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 10, 11, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 10, 11, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 26. -/
theorem zenodoU16_quantifiedFaceBatch_26 :
    ∀ a ∈ (⟨1, 12, 13, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨1, 12, 13, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨1, 12, 13, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 27. -/
theorem zenodoU16_quantifiedFaceBatch_27 :
    ∀ a ∈ (⟨2, 3, 4, 7⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 3, 4, 7⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 3, 4, 7⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 28. -/
theorem zenodoU16_quantifiedFaceBatch_28 :
    ∀ a ∈ (⟨2, 3, 4, 10⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 3, 4, 10⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 3, 4, 10⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 29. -/
theorem zenodoU16_quantifiedFaceBatch_29 :
    ∀ a ∈ (⟨2, 3, 6, 11⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 3, 6, 11⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 3, 6, 11⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 30. -/
theorem zenodoU16_quantifiedFaceBatch_30 :
    ∀ a ∈ (⟨2, 3, 7, 9⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 3, 7, 9⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 3, 7, 9⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 31. -/
theorem zenodoU16_quantifiedFaceBatch_31 :
    ∀ a ∈ (⟨2, 3, 10, 11⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 3, 10, 11⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 3, 10, 11⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 32. -/
theorem zenodoU16_quantifiedFaceBatch_32 :
    ∀ a ∈ (⟨2, 4, 7, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 4, 7, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 4, 7, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 33. -/
theorem zenodoU16_quantifiedFaceBatch_33 :
    ∀ a ∈ (⟨2, 4, 10, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 4, 10, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 4, 10, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 34. -/
theorem zenodoU16_quantifiedFaceBatch_34 :
    ∀ a ∈ (⟨2, 4, 13, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 4, 13, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 4, 13, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 35. -/
theorem zenodoU16_quantifiedFaceBatch_35 :
    ∀ a ∈ (⟨2, 5, 10, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 5, 10, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 5, 10, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 36. -/
theorem zenodoU16_quantifiedFaceBatch_36 :
    ∀ a ∈ (⟨2, 5, 12, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 5, 12, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 5, 12, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 37. -/
theorem zenodoU16_quantifiedFaceBatch_37 :
    ∀ a ∈ (⟨2, 6, 8, 11⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 6, 8, 11⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 6, 8, 11⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 38. -/
theorem zenodoU16_quantifiedFaceBatch_38 :
    ∀ a ∈ (⟨2, 7, 9, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 7, 9, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 7, 9, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 39. -/
theorem zenodoU16_quantifiedFaceBatch_39 :
    ∀ a ∈ (⟨2, 7, 14, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 7, 14, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 7, 14, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 40. -/
theorem zenodoU16_quantifiedFaceBatch_40 :
    ∀ a ∈ (⟨2, 8, 11, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 8, 11, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 8, 11, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 41. -/
theorem zenodoU16_quantifiedFaceBatch_41 :
    ∀ a ∈ (⟨2, 9, 10, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 9, 10, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 9, 10, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 42. -/
theorem zenodoU16_quantifiedFaceBatch_42 :
    ∀ a ∈ (⟨2, 9, 13, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 9, 13, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 9, 13, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 43. -/
theorem zenodoU16_quantifiedFaceBatch_43 :
    ∀ a ∈ (⟨2, 10, 11, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 10, 11, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 10, 11, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 44. -/
theorem zenodoU16_quantifiedFaceBatch_44 :
    ∀ a ∈ (⟨2, 11, 12, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 11, 12, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 11, 12, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 45. -/
theorem zenodoU16_quantifiedFaceBatch_45 :
    ∀ a ∈ (⟨2, 13, 14, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨2, 13, 14, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨2, 13, 14, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 46. -/
theorem zenodoU16_quantifiedFaceBatch_46 :
    ∀ a ∈ (⟨3, 4, 5, 8⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 4, 5, 8⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 4, 5, 8⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 47. -/
theorem zenodoU16_quantifiedFaceBatch_47 :
    ∀ a ∈ (⟨3, 4, 5, 11⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 4, 5, 11⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 4, 5, 11⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 48. -/
theorem zenodoU16_quantifiedFaceBatch_48 :
    ∀ a ∈ (⟨3, 4, 7, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 4, 7, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 4, 7, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 49. -/
theorem zenodoU16_quantifiedFaceBatch_49 :
    ∀ a ∈ (⟨3, 4, 8, 10⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 4, 8, 10⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 4, 8, 10⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 50. -/
theorem zenodoU16_quantifiedFaceBatch_50 :
    ∀ a ∈ (⟨3, 4, 11, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 4, 11, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 4, 11, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 51. -/
theorem zenodoU16_quantifiedFaceBatch_51 :
    ∀ a ∈ (⟨3, 5, 8, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 5, 8, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 5, 8, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 52. -/
theorem zenodoU16_quantifiedFaceBatch_52 :
    ∀ a ∈ (⟨3, 5, 11, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 5, 11, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 5, 11, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 53. -/
theorem zenodoU16_quantifiedFaceBatch_53 :
    ∀ a ∈ (⟨3, 5, 14, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 5, 14, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 5, 14, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 54. -/
theorem zenodoU16_quantifiedFaceBatch_54 :
    ∀ a ∈ (⟨3, 6, 11, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 6, 11, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 6, 11, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 55. -/
theorem zenodoU16_quantifiedFaceBatch_55 :
    ∀ a ∈ (⟨3, 7, 9, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 7, 9, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 7, 9, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 56. -/
theorem zenodoU16_quantifiedFaceBatch_56 :
    ∀ a ∈ (⟨3, 8, 10, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 8, 10, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 8, 10, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 57. -/
theorem zenodoU16_quantifiedFaceBatch_57 :
    ∀ a ∈ (⟨3, 8, 15, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 8, 15, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 8, 15, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 58. -/
theorem zenodoU16_quantifiedFaceBatch_58 :
    ∀ a ∈ (⟨3, 10, 11, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 10, 11, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 10, 11, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 59. -/
theorem zenodoU16_quantifiedFaceBatch_59 :
    ∀ a ∈ (⟨3, 10, 14, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 10, 14, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 10, 14, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 60. -/
theorem zenodoU16_quantifiedFaceBatch_60 :
    ∀ a ∈ (⟨3, 11, 12, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 11, 12, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 11, 12, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 61. -/
theorem zenodoU16_quantifiedFaceBatch_61 :
    ∀ a ∈ (⟨3, 14, 15, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨3, 14, 15, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨3, 14, 15, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 62. -/
theorem zenodoU16_quantifiedFaceBatch_62 :
    ∀ a ∈ (⟨4, 5, 6, 9⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 5, 6, 9⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 5, 6, 9⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 63. -/
theorem zenodoU16_quantifiedFaceBatch_63 :
    ∀ a ∈ (⟨4, 5, 6, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 5, 6, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 5, 6, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 64. -/
theorem zenodoU16_quantifiedFaceBatch_64 :
    ∀ a ∈ (⟨4, 5, 8, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 5, 8, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 5, 8, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 65. -/
theorem zenodoU16_quantifiedFaceBatch_65 :
    ∀ a ∈ (⟨4, 5, 9, 11⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 5, 9, 11⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 5, 9, 11⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 66. -/
theorem zenodoU16_quantifiedFaceBatch_66 :
    ∀ a ∈ (⟨4, 5, 12, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 5, 12, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 5, 12, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 67. -/
theorem zenodoU16_quantifiedFaceBatch_67 :
    ∀ a ∈ (⟨4, 6, 9, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 6, 9, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 6, 9, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 68. -/
theorem zenodoU16_quantifiedFaceBatch_68 :
    ∀ a ∈ (⟨4, 6, 12, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 6, 12, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 6, 12, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 69. -/
theorem zenodoU16_quantifiedFaceBatch_69 :
    ∀ a ∈ (⟨4, 6, 15, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 6, 15, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 6, 15, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 70. -/
theorem zenodoU16_quantifiedFaceBatch_70 :
    ∀ a ∈ (⟨4, 7, 12, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 7, 12, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 7, 12, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 71. -/
theorem zenodoU16_quantifiedFaceBatch_71 :
    ∀ a ∈ (⟨4, 8, 10, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 8, 10, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 8, 10, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 72. -/
theorem zenodoU16_quantifiedFaceBatch_72 :
    ∀ a ∈ (⟨4, 11, 12, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 11, 12, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 11, 12, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 73. -/
theorem zenodoU16_quantifiedFaceBatch_73 :
    ∀ a ∈ (⟨4, 12, 13, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨4, 12, 13, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨4, 12, 13, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 74. -/
theorem zenodoU16_quantifiedFaceBatch_74 :
    ∀ a ∈ (⟨5, 6, 7, 10⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 6, 7, 10⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 6, 7, 10⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 75. -/
theorem zenodoU16_quantifiedFaceBatch_75 :
    ∀ a ∈ (⟨5, 6, 7, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 6, 7, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 6, 7, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 76. -/
theorem zenodoU16_quantifiedFaceBatch_76 :
    ∀ a ∈ (⟨5, 6, 9, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 6, 9, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 6, 9, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 77. -/
theorem zenodoU16_quantifiedFaceBatch_77 :
    ∀ a ∈ (⟨5, 6, 10, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 6, 10, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 6, 10, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 78. -/
theorem zenodoU16_quantifiedFaceBatch_78 :
    ∀ a ∈ (⟨5, 6, 13, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 6, 13, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 6, 13, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 79. -/
theorem zenodoU16_quantifiedFaceBatch_79 :
    ∀ a ∈ (⟨5, 7, 13, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 7, 13, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 7, 13, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 80. -/
theorem zenodoU16_quantifiedFaceBatch_80 :
    ∀ a ∈ (⟨5, 8, 13, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 8, 13, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 8, 13, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 81. -/
theorem zenodoU16_quantifiedFaceBatch_81 :
    ∀ a ∈ (⟨5, 9, 11, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 9, 11, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 9, 11, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 82. -/
theorem zenodoU16_quantifiedFaceBatch_82 :
    ∀ a ∈ (⟨5, 12, 13, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 12, 13, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 12, 13, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 83. -/
theorem zenodoU16_quantifiedFaceBatch_83 :
    ∀ a ∈ (⟨5, 13, 14, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨5, 13, 14, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨5, 13, 14, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 84. -/
theorem zenodoU16_quantifiedFaceBatch_84 :
    ∀ a ∈ (⟨6, 7, 8, 11⟩ : Tet).verts,
      ∀ b ∈ (⟨6, 7, 8, 11⟩ : Tet).verts,
        ∀ c ∈ (⟨6, 7, 8, 11⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 85. -/
theorem zenodoU16_quantifiedFaceBatch_85 :
    ∀ a ∈ (⟨6, 7, 8, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨6, 7, 8, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨6, 7, 8, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 86. -/
theorem zenodoU16_quantifiedFaceBatch_86 :
    ∀ a ∈ (⟨6, 7, 10, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨6, 7, 10, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨6, 7, 10, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 87. -/
theorem zenodoU16_quantifiedFaceBatch_87 :
    ∀ a ∈ (⟨6, 7, 11, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨6, 7, 11, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨6, 7, 11, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 88. -/
theorem zenodoU16_quantifiedFaceBatch_88 :
    ∀ a ∈ (⟨6, 7, 14, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨6, 7, 14, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨6, 7, 14, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 89. -/
theorem zenodoU16_quantifiedFaceBatch_89 :
    ∀ a ∈ (⟨6, 9, 14, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨6, 9, 14, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨6, 9, 14, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 90. -/
theorem zenodoU16_quantifiedFaceBatch_90 :
    ∀ a ∈ (⟨6, 10, 12, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨6, 10, 12, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨6, 10, 12, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 91. -/
theorem zenodoU16_quantifiedFaceBatch_91 :
    ∀ a ∈ (⟨6, 14, 15, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨6, 14, 15, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨6, 14, 15, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 92. -/
theorem zenodoU16_quantifiedFaceBatch_92 :
    ∀ a ∈ (⟨7, 8, 9, 12⟩ : Tet).verts,
      ∀ b ∈ (⟨7, 8, 9, 12⟩ : Tet).verts,
        ∀ c ∈ (⟨7, 8, 9, 12⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 93. -/
theorem zenodoU16_quantifiedFaceBatch_93 :
    ∀ a ∈ (⟨7, 8, 9, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨7, 8, 9, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨7, 8, 9, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 94. -/
theorem zenodoU16_quantifiedFaceBatch_94 :
    ∀ a ∈ (⟨7, 8, 11, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨7, 8, 11, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨7, 8, 11, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 95. -/
theorem zenodoU16_quantifiedFaceBatch_95 :
    ∀ a ∈ (⟨7, 8, 12, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨7, 8, 12, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨7, 8, 12, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 96. -/
theorem zenodoU16_quantifiedFaceBatch_96 :
    ∀ a ∈ (⟨7, 8, 15, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨7, 8, 15, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨7, 8, 15, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 97. -/
theorem zenodoU16_quantifiedFaceBatch_97 :
    ∀ a ∈ (⟨7, 11, 13, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨7, 11, 13, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨7, 11, 13, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 98. -/
theorem zenodoU16_quantifiedFaceBatch_98 :
    ∀ a ∈ (⟨8, 9, 10, 13⟩ : Tet).verts,
      ∀ b ∈ (⟨8, 9, 10, 13⟩ : Tet).verts,
        ∀ c ∈ (⟨8, 9, 10, 13⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 99. -/
theorem zenodoU16_quantifiedFaceBatch_99 :
    ∀ a ∈ (⟨8, 9, 10, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨8, 9, 10, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨8, 9, 10, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 100. -/
theorem zenodoU16_quantifiedFaceBatch_100 :
    ∀ a ∈ (⟨8, 9, 13, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨8, 9, 13, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨8, 9, 13, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 101. -/
theorem zenodoU16_quantifiedFaceBatch_101 :
    ∀ a ∈ (⟨9, 10, 11, 14⟩ : Tet).verts,
      ∀ b ∈ (⟨9, 10, 11, 14⟩ : Tet).verts,
        ∀ c ∈ (⟨9, 10, 11, 14⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 102. -/
theorem zenodoU16_quantifiedFaceBatch_102 :
    ∀ a ∈ (⟨9, 10, 14, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨9, 10, 14, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨9, 10, 14, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 103. -/
theorem zenodoU16_quantifiedFaceBatch_103 :
    ∀ a ∈ (⟨10, 11, 12, 15⟩ : Tet).verts,
      ∀ b ∈ (⟨10, 11, 12, 15⟩ : Tet).verts,
        ∀ c ∈ (⟨10, 11, 12, 15⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Quantified face-incidence certificate for U(16) tetrahedron 104. -/
theorem zenodoU16_quantifiedFaceBatch_104 :
    ∀ a ∈ (⟨11, 12, 13, 16⟩ : Tet).verts,
      ∀ b ∈ (⟨11, 12, 13, 16⟩ : Tet).verts,
        ∀ c ∈ (⟨11, 12, 13, 16⟩ : Tet).verts,
          [a, b, c].Nodup →
          (zenodoU16Original.tets.filter (fun sigma =>
            a ∈ sigma.verts ∧
            b ∈ sigma.verts ∧
            c ∈ sigma.verts)).length = 2 := by
  decide

/-- Assembly of the 104 independently verified quantified face certificates.
This proves only the finite represented-face incidence property. -/
theorem zenodoU16_boundedFaceIncidence :
    BoundedRepresentedFaceIncidence zenodoU16Original := by
  intro tau htau
  simp only [zenodoU16Original, List.mem_cons, List.mem_nil_iff, or_false] at htau
  rcases htau with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact zenodoU16_firstTet_quantifiedFaceIncidence
  · exact zenodoU16_quantifiedFaceBatch_2
  · exact zenodoU16_quantifiedFaceBatch_3
  · exact zenodoU16_quantifiedFaceBatch_4
  · exact zenodoU16_quantifiedFaceBatch_5
  · exact zenodoU16_quantifiedFaceBatch_6
  · exact zenodoU16_quantifiedFaceBatch_7
  · exact zenodoU16_quantifiedFaceBatch_8
  · exact zenodoU16_quantifiedFaceBatch_9
  · exact zenodoU16_quantifiedFaceBatch_10
  · exact zenodoU16_quantifiedFaceBatch_11
  · exact zenodoU16_quantifiedFaceBatch_12
  · exact zenodoU16_quantifiedFaceBatch_13
  · exact zenodoU16_quantifiedFaceBatch_14
  · exact zenodoU16_quantifiedFaceBatch_15
  · exact zenodoU16_quantifiedFaceBatch_16
  · exact zenodoU16_quantifiedFaceBatch_17
  · exact zenodoU16_quantifiedFaceBatch_18
  · exact zenodoU16_quantifiedFaceBatch_19
  · exact zenodoU16_quantifiedFaceBatch_20
  · exact zenodoU16_quantifiedFaceBatch_21
  · exact zenodoU16_quantifiedFaceBatch_22
  · exact zenodoU16_quantifiedFaceBatch_23
  · exact zenodoU16_quantifiedFaceBatch_24
  · exact zenodoU16_quantifiedFaceBatch_25
  · exact zenodoU16_quantifiedFaceBatch_26
  · exact zenodoU16_quantifiedFaceBatch_27
  · exact zenodoU16_quantifiedFaceBatch_28
  · exact zenodoU16_quantifiedFaceBatch_29
  · exact zenodoU16_quantifiedFaceBatch_30
  · exact zenodoU16_quantifiedFaceBatch_31
  · exact zenodoU16_quantifiedFaceBatch_32
  · exact zenodoU16_quantifiedFaceBatch_33
  · exact zenodoU16_quantifiedFaceBatch_34
  · exact zenodoU16_quantifiedFaceBatch_35
  · exact zenodoU16_quantifiedFaceBatch_36
  · exact zenodoU16_quantifiedFaceBatch_37
  · exact zenodoU16_quantifiedFaceBatch_38
  · exact zenodoU16_quantifiedFaceBatch_39
  · exact zenodoU16_quantifiedFaceBatch_40
  · exact zenodoU16_quantifiedFaceBatch_41
  · exact zenodoU16_quantifiedFaceBatch_42
  · exact zenodoU16_quantifiedFaceBatch_43
  · exact zenodoU16_quantifiedFaceBatch_44
  · exact zenodoU16_quantifiedFaceBatch_45
  · exact zenodoU16_quantifiedFaceBatch_46
  · exact zenodoU16_quantifiedFaceBatch_47
  · exact zenodoU16_quantifiedFaceBatch_48
  · exact zenodoU16_quantifiedFaceBatch_49
  · exact zenodoU16_quantifiedFaceBatch_50
  · exact zenodoU16_quantifiedFaceBatch_51
  · exact zenodoU16_quantifiedFaceBatch_52
  · exact zenodoU16_quantifiedFaceBatch_53
  · exact zenodoU16_quantifiedFaceBatch_54
  · exact zenodoU16_quantifiedFaceBatch_55
  · exact zenodoU16_quantifiedFaceBatch_56
  · exact zenodoU16_quantifiedFaceBatch_57
  · exact zenodoU16_quantifiedFaceBatch_58
  · exact zenodoU16_quantifiedFaceBatch_59
  · exact zenodoU16_quantifiedFaceBatch_60
  · exact zenodoU16_quantifiedFaceBatch_61
  · exact zenodoU16_quantifiedFaceBatch_62
  · exact zenodoU16_quantifiedFaceBatch_63
  · exact zenodoU16_quantifiedFaceBatch_64
  · exact zenodoU16_quantifiedFaceBatch_65
  · exact zenodoU16_quantifiedFaceBatch_66
  · exact zenodoU16_quantifiedFaceBatch_67
  · exact zenodoU16_quantifiedFaceBatch_68
  · exact zenodoU16_quantifiedFaceBatch_69
  · exact zenodoU16_quantifiedFaceBatch_70
  · exact zenodoU16_quantifiedFaceBatch_71
  · exact zenodoU16_quantifiedFaceBatch_72
  · exact zenodoU16_quantifiedFaceBatch_73
  · exact zenodoU16_quantifiedFaceBatch_74
  · exact zenodoU16_quantifiedFaceBatch_75
  · exact zenodoU16_quantifiedFaceBatch_76
  · exact zenodoU16_quantifiedFaceBatch_77
  · exact zenodoU16_quantifiedFaceBatch_78
  · exact zenodoU16_quantifiedFaceBatch_79
  · exact zenodoU16_quantifiedFaceBatch_80
  · exact zenodoU16_quantifiedFaceBatch_81
  · exact zenodoU16_quantifiedFaceBatch_82
  · exact zenodoU16_quantifiedFaceBatch_83
  · exact zenodoU16_quantifiedFaceBatch_84
  · exact zenodoU16_quantifiedFaceBatch_85
  · exact zenodoU16_quantifiedFaceBatch_86
  · exact zenodoU16_quantifiedFaceBatch_87
  · exact zenodoU16_quantifiedFaceBatch_88
  · exact zenodoU16_quantifiedFaceBatch_89
  · exact zenodoU16_quantifiedFaceBatch_90
  · exact zenodoU16_quantifiedFaceBatch_91
  · exact zenodoU16_quantifiedFaceBatch_92
  · exact zenodoU16_quantifiedFaceBatch_93
  · exact zenodoU16_quantifiedFaceBatch_94
  · exact zenodoU16_quantifiedFaceBatch_95
  · exact zenodoU16_quantifiedFaceBatch_96
  · exact zenodoU16_quantifiedFaceBatch_97
  · exact zenodoU16_quantifiedFaceBatch_98
  · exact zenodoU16_quantifiedFaceBatch_99
  · exact zenodoU16_quantifiedFaceBatch_100
  · exact zenodoU16_quantifiedFaceBatch_101
  · exact zenodoU16_quantifiedFaceBatch_102
  · exact zenodoU16_quantifiedFaceBatch_103
  · exact zenodoU16_quantifiedFaceBatch_104

end Poincare
