import Poincare.GlobalMove32WitnessedSourceFaceReentry
import Poincare.Move32SurvivorClassification
import Mathlib.Tactic

namespace Poincare

/--
For a realized Move32 site whose shared edge has ambient tetrahedron
incidence exactly three, those three tetrahedra are precisely the three
represented Move32 target tetrahedra, up to `SameTetVertices`.

Unlike the older survivor-classification theorem, this statement requires
only `RealizedIn` and `SharedEdgeExactlyThree`; source-face absence and full
Move32 legality are irrelevant to this saturation fact.
-/
theorem
    ClosedTriangulationCore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hthree : s.SharedEdgeExactlyThree K)
    {tau : Tet}
    (htau : tau ∈ K.tets)
    (hd : s.d ∈ tau.verts)
    (he : s.e ∈ tau.verts) :
    SameTetVertices tau s.targetTet₀ ∨
      SameTetVertices tau s.targetTet₁ ∨
        SameTetVertices tau s.targetTet₂ := by
  classical

  rcases hrealized with
    ⟨⟨t0, ht0, hs0⟩,
      ⟨t1, ht1, hs1⟩,
      ⟨t2, ht2, hs2⟩⟩

  have hrealized' :
      s.RealizedIn K :=
    ⟨⟨t0, ht0, hs0⟩,
      ⟨t1, ht1, hs1⟩,
      ⟨t2, ht2, hs2⟩⟩

  have hfive :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct
      s
      hrealized'

  let edgeTets :=
    K.tets.filter
      (fun rho =>
        s.d ∈ rho.verts ∧
        s.e ∈ rho.verts)

  have memEdge
      {rho : Tet}
      (hr : rho ∈ K.tets)
      (hs :
        SameTetVertices rho s.targetTet₀ ∨
          SameTetVertices rho s.targetTet₁ ∨
            SameTetVertices rho s.targetTet₂) :
      rho ∈ edgeTets := by
    simp only [
      edgeTets,
      List.mem_filter,
      decide_eq_true_eq
    ]

    refine ⟨hr, ?_⟩

    rcases hs with
      hs | hs | hs

    · constructor
      · apply (hs _).2
        simp [
          Move32Site.targetTet₀,
          Tet.verts
        ]
      · apply (hs _).2
        simp [
          Move32Site.targetTet₀,
          Tet.verts
        ]

    · constructor
      · apply (hs _).2
        simp [
          Move32Site.targetTet₁,
          Tet.verts
        ]
      · apply (hs _).2
        simp [
          Move32Site.targetTet₁,
          Tet.verts
        ]

    · constructor
      · apply (hs _).2
        simp [
          Move32Site.targetTet₂,
          Tet.verts
        ]
      · apply (hs _).2
        simp [
          Move32Site.targetTet₂,
          Tet.verts
        ]

  have hm0 :
      t0 ∈ edgeTets :=
    memEdge
      ht0
      (Or.inl hs0)

  have hm1 :
      t1 ∈ edgeTets :=
    memEdge
      ht1
      (Or.inr (Or.inl hs1))

  have hm2 :
      t2 ∈ edgeTets :=
    memEdge
      ht2
      (Or.inr (Or.inr hs2))

  have h01 :
      t0 ≠ t1 := by
    intro h
    subst t1

    exact
      s.targetTet₀_not_same_targetTet₁
        hfive
        (sameTetVertices_trans
          (sameTetVertices_symm hs0)
          hs1)

  have h02 :
      t0 ≠ t2 := by
    intro h
    subst t2

    exact
      s.targetTet₀_not_same_targetTet₂
        hfive
        (sameTetVertices_trans
          (sameTetVertices_symm hs0)
          hs2)

  have h12 :
      t1 ≠ t2 := by
    intro h
    subst t2

    exact
      s.targetTet₁_not_same_targetTet₂
        hfive
        (sameTetVertices_trans
          (sameTetVertices_symm hs1)
          hs2)

  have htauEdge :
      tau ∈ edgeTets := by
    simp only [
      edgeTets,
      List.mem_filter,
      decide_eq_true_eq
    ]

    exact
      ⟨htau,
        hd,
        he⟩

  have hlen :
      edgeTets.length = 3 := by
    simpa [
      edgeTets,
      Move32Site.SharedEdgeExactlyThree
    ] using hthree

  have hwhich :
      tau = t0 ∨
        tau = t1 ∨
          tau = t2 :=
    eq_one_of_three_of_mem_of_length_eq_three
      hlen
      hm0
      hm1
      hm2
      h01
      h02
      h12
      htauEdge

  rcases hwhich with
    h0 | h1 | h2

  · subst tau
    exact
      Or.inl hs0

  · subst tau
    exact
      Or.inr
        (Or.inl hs1)

  · subst tau
    exact
      Or.inr
        (Or.inr hs2)

end Poincare
