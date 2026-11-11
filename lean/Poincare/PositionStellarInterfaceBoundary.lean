import Poincare.HeadStellarNormalForm

namespace Poincare

/-- Literal insertion at a selected tetrahedron position, retaining its
unchanged prefix and suffix. This construction does not by itself certify
closed-core preservation or a `CertifiedPachnerStep`. -/
def Move41Site.insertFreshAt
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (_hsource : K.tets = before ++ s.targetTet :: after)
    (_hfresh : s.e ∉ vertexSupport K) : Triangulation :=
  { tets := before ++ s.sourceTets ++ after }

/-- Position-preserving insertion is exact as an ordered list. -/
theorem Move41Site.insertFreshAt_tets
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hfresh : s.e ∉ vertexSupport K) :
    (s.insertFreshAt K before after hsource hfresh).tets =
      before ++ s.sourceTets ++ after := by
  rfl

/-- The repository's exact inverse 4→1 replacement always inserts the
target tetrahedron at the head, irrespective of its input list order. -/
theorem Move41Site.replace_target_at_head
    (s : Move41Site) (P : Triangulation) :
    (s.replace P).tets = s.targetTet :: s.unchangedTets P := by
  rfl

/-- A source whose first tetrahedron differs from the selected target
cannot be literally equal to a 4→1 replacement at that site.
This is an exact-label/order obstruction, not a topological obstruction. -/
theorem Move41Site.nonhead_not_exact_inverse
    (s : Move41Site) (K P : Triangulation)
    (headTet : Tet) (tail : List Tet)
    (hK : K.tets = headTet :: tail)
    (hneq : headTet ≠ s.targetTet) :
    K ≠ s.replace P := by
  intro h
  have htets := congrArg Triangulation.tets h
  rw [hK, s.replace_target_at_head P] at htets
  exact hneq (List.cons.inj htets).1

end Poincare
