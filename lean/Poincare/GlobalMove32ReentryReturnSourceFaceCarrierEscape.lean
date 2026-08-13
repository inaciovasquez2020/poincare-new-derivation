import Poincare.GlobalMove32ReentryReturnSourceFaceSameSupport
import Mathlib.Tactic

namespace Poincare

/--
At a recurrent return to the same shared edge, the existing common-pair /
third-vertex classification can be sharpened.

Either the anchor and returned source faces have the same unordered support,
or their common pair `u,v` has distinct third vertices `p,q` and the returned
third vertex `q` lies outside the entire five-vertex carrier of the anchor.

Thus the `p ≠ q` branch is a genuine carrier escape rather than merely a
different labeling of a face inside the same five vertices.

No cycle-impossibility or termination conclusion is asserted here.
-/
theorem
    ClosedTriangulationCore.sourceFace_support_eq_or_distinct_third_vertex_outside_anchor_carrier_of_return_target
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
      (ret.d = anchor.d ∧ ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧ ret.e = anchor.d))
    (hanchorTarget :
      SameTetVertices sigma anchor.targetTet₀ ∨
      SameTetVertices sigma anchor.targetTet₁ ∨
      SameTetVertices sigma anchor.targetTet₂) :
    (∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] ↔
        z ∈ [ret.a, ret.b, ret.c]) ∨
      ∃ u v p q,
        u ≠ v ∧
        p ≠ u ∧
        p ≠ v ∧
        q ≠ u ∧
        q ≠ v ∧
        p ∈ [anchor.a, anchor.b, anchor.c] ∧
        q ∈ [ret.a, ret.b, ret.c] ∧
        (∀ z : Nat,
          z ∈ [anchor.a, anchor.b, anchor.c] ↔
          z = u ∨ z = v ∨ z = p) ∧
        (∀ z : Nat,
          z ∈ [ret.a, ret.b, ret.c] ↔
          z = u ∨ z = v ∨ z = q) ∧
        p ≠ q ∧
        q ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by

  obtain hsame | hdistinct :=
    hcore.sourceFace_support_eq_or_distinct_third_vertices_of_return_target
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

  · exact Or.inl hsame

  · right

    obtain
        ⟨u, v, p, q,
          huv,
          hpu,
          hpv,
          hqu,
          hqv,
          hpAnchor,
          hqRet,
          hanchorExact,
          hretExact,
          hpq⟩ :=
      hdistinct

    have hqAnchorSource :
        q ∉ [anchor.a, anchor.b, anchor.c] := by
      intro hqAnchor
      have hcases :
          q = u ∨ q = v ∨ q = p :=
        (hanchorExact q).mp hqAnchor
      rcases hcases with hqu' | hqv' | hqp
      · exact hqu hqu'
      · exact hqv hqv'
      · exact hpq hqp.symm

    have hretFive :
        [ret.a, ret.b, ret.c, ret.d, ret.e].Nodup :=
      hcore.move32Site_distinct ret hretRealized

    have hqRetD :
        q ≠ ret.d := by
      intro hqd
      have hdIn :
          ret.d ∈ [ret.a, ret.b, ret.c] := by
        simpa [hqd] using hqRet
      have hf := hretFive
      simp at hf hdIn
      omega

    have hqRetE :
        q ≠ ret.e := by
      intro hqe
      have heIn :
          ret.e ∈ [ret.a, ret.b, ret.c] := by
        simpa [hqe] using hqRet
      have hf := hretFive
      simp at hf heIn
      omega

    have hqAnchorD :
        q ≠ anchor.d := by
      intro hqd
      rcases hreturnEdge with hdirect | hreverse
      · exact hqRetD (hqd.trans hdirect.1.symm)
      · exact hqRetE (hqd.trans hreverse.2.symm)

    have hqAnchorE :
        q ≠ anchor.e := by
      intro hqe
      rcases hreturnEdge with hdirect | hreverse
      · exact hqRetE (hqe.trans hdirect.2.symm)
      · exact hqRetD (hqe.trans hreverse.1.symm)

    have hqOutside :
        q ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
      intro hqCarrier
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hqCarrier
      rcases hqCarrier with hqa | hqb | hqc | hqd | hqe

      · apply hqAnchorSource
        simp [hqa]

      · apply hqAnchorSource
        simp [hqb]

      · apply hqAnchorSource
        simp [hqc]

      · exact hqAnchorD hqd
      · exact hqAnchorE hqe

    exact
      ⟨u, v, p, q,
        huv,
        hpu,
        hpv,
        hqu,
        hqv,
        hpAnchor,
        hqRet,
        hanchorExact,
        hretExact,
        hpq,
        hqOutside⟩

end Poincare
