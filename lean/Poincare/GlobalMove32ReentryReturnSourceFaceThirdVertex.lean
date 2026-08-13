import Poincare.GlobalMove32ReentryReturnSourceFaceOverlap
import Mathlib.Tactic

namespace Poincare

private theorem exists_third_vertex_of_three
    {a b c u v : Nat}
    (hnodup : [a, b, c].Nodup)
    (hu : u ∈ [a, b, c])
    (hv : v ∈ [a, b, c])
    (huv : u ≠ v) :
    ∃ p,
      p ∈ [a, b, c] ∧
      p ≠ u ∧
      p ≠ v ∧
      ∀ z,
        z ∈ [a, b, c] ↔
          z = u ∨ z = v ∨ z = p := by
  have hab : a ≠ b := by
    intro h
    subst b
    simpa using hnodup

  have hac : a ≠ c := by
    intro h
    subst c
    simpa using hnodup

  have hbc : b ≠ c := by
    intro h
    subst c
    simpa using hnodup

  simp only [
    List.mem_cons,
    List.not_mem_nil,
    or_false
  ] at hu hv

  rcases hu with
    rfl | rfl | rfl <;>
  rcases hv with
    rfl | rfl | rfl

  · exact
      (huv rfl).elim

  · refine
      ⟨c,
        ?_,
        Ne.symm hac,
        Ne.symm hbc,
        ?_⟩
    · simp
    · intro z
      simp only [
        List.mem_cons,
        List.not_mem_nil,
        or_false
      ]

  · refine
      ⟨b,
        ?_,
        Ne.symm hab,
        hbc,
        ?_⟩
    · simp
    · intro z
      simp only [
        List.mem_cons,
        List.not_mem_nil,
        or_false
      ]
      aesop

  · refine
      ⟨c,
        ?_,
        Ne.symm hbc,
        Ne.symm hac,
        ?_⟩
    · simp
    · intro z
      simp only [
        List.mem_cons,
        List.not_mem_nil,
        or_false
      ]
      aesop

  · exact
      (huv rfl).elim

  · refine
      ⟨a,
        ?_,
        hab,
        hac,
        ?_⟩
    · simp
    · intro z
      simp only [
        List.mem_cons,
        List.not_mem_nil,
        or_false
      ]
      aesop

  · refine
      ⟨b,
        ?_,
        hbc,
        Ne.symm hab,
        ?_⟩
    · simp
    · intro z
      simp only [
        List.mem_cons,
        List.not_mem_nil,
        or_false
      ]
      aesop

  · refine
      ⟨a,
        ?_,
        hac,
        hab,
        ?_⟩
    · simp
    · intro z
      simp only [
        List.mem_cons,
        List.not_mem_nil,
        or_false
      ]
      aesop

  · exact
      (huv rfl).elim

/--
At a recurrent shared-edge return, the previously proved two common
source-face vertices determine a unique remaining third vertex on each side.

Thus the anchor source face has the exact unordered support `{u,v,p}` and the
return source face has the exact unordered support `{u,v,q}`, with `p` and
`q` each distinct from the common pair.

This theorem intentionally does not decide whether `p = q`.
That equality/disequality split is the next recurrent-cycle obstruction.
-/
theorem
    ClosedTriangulationCore.exists_common_pair_and_third_sourceFace_vertices_of_return_target
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hretRealized : ret.RealizedIn K)
    (hretThree : ret.SharedEdgeExactlyThree K)
    {sigma : Tet}
    (hsigmaK : sigma ∈ K.tets)
    (hretD : ret.d ∈ sigma.verts)
    (hretE : ret.e ∈ sigma.verts)
    (hreturnEdge :
      (ret.d = anchor.d ∧
       ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧
       ret.e = anchor.d))
    (hanchorTarget :
      SameTetVertices sigma anchor.targetTet₀ ∨
      SameTetVertices sigma anchor.targetTet₁ ∨
      SameTetVertices sigma anchor.targetTet₂) :
    ∃ u v p q,
      u ≠ v ∧
      p ≠ u ∧
      p ≠ v ∧
      q ≠ u ∧
      q ≠ v ∧
      p ∈ [anchor.a, anchor.b, anchor.c] ∧
      q ∈ [ret.a, ret.b, ret.c] ∧
      (∀ z,
        z ∈ [anchor.a, anchor.b, anchor.c] ↔
          z = u ∨ z = v ∨ z = p) ∧
      ∀ z,
        z ∈ [ret.a, ret.b, ret.c] ↔
          z = u ∨ z = v ∨ z = q := by
  classical

  obtain
      ⟨u,
        v,
        huv,
        huAnchor,
        hvAnchor,
        huRet,
        hvRet⟩ :=
    hcore.exists_two_common_sourceFace_vertices_of_return_target
      anchor
      ret
      hanchorRealized
      hretRealized
      hretThree
      hsigmaK
      hretD
      hretE
      hreturnEdge
      hanchorTarget

  have hanchorFaceNodup :
      [anchor.a, anchor.b, anchor.c].Nodup := by
    have hfive :=
      hcore.move32Site_distinct
        anchor
        hanchorRealized

    simp only [
      List.nodup_cons,
      List.mem_cons,
      List.not_mem_nil,
      not_or
    ] at hfive ⊢

    aesop

  have hretFaceNodup :
      [ret.a, ret.b, ret.c].Nodup := by
    have hfive :=
      hcore.move32Site_distinct
        ret
        hretRealized

    simp only [
      List.nodup_cons,
      List.mem_cons,
      List.not_mem_nil,
      not_or
    ] at hfive ⊢

    aesop

  obtain
      ⟨p,
        hpAnchor,
        hpu,
        hpv,
        hanchorExact⟩ :=
    exists_third_vertex_of_three
      hanchorFaceNodup
      huAnchor
      hvAnchor
      huv

  obtain
      ⟨q,
        hqRet,
        hqu,
        hqv,
        hretExact⟩ :=
    exists_third_vertex_of_three
      hretFaceNodup
      huRet
      hvRet
      huv

  exact
    ⟨u,
      v,
      p,
      q,
      huv,
      hpu,
      hpv,
      hqu,
      hqv,
      hpAnchor,
      hqRet,
      hanchorExact,
      hretExact⟩

end Poincare
