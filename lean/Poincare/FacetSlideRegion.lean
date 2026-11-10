import Poincare.PhiSupportEulerCount

namespace Poincare

/-!
# Facet-slide set-level and defect-count certificates

This isolates the universal **set-theoretic** bookkeeping for the local
1→4 / 2→3 / 3→2 facet transport. There are nine distinct local tetrahedron
labels and an arbitrary disjoint exterior. The labels correspond to:

* `0` = abcd, `1` = abce, `2` = abcx,
* `3` = abdx, `4` = acdx, `5` = bcdx,
* `6` = abex, `7` = acex, `8` = bcex.

The type `β ⊕ Fin 9` makes the required disjointness and local-label
distinctness explicit instead of silently assuming them about lists of
vertex tuples. The theorem below does **not** prove legality of actual
Pachner sites or arbitrary fresh 1→4 existence in a closed triangulation.
-/

section SetCertificate

variable {β : Type*} [DecidableEq β]

private def exterior (R : Finset β) : Finset (Sum β (Fin 9)) :=
  R.image Sum.inl

private def localTet (i : Fin 9) : Sum β (Fin 9) :=
  Sum.inr i

/-- Exact set identity for the two local exchanges following fresh
subdivision of `abcd`. The arbitrary exterior `R` is unchanged. -/
theorem facetSlide_encodedRegion_identity (R : Finset β) :
    (((((exterior R ∪
        {localTet 1, localTet 2, localTet 3, localTet 4, localTet 5}) \
        {localTet 1, localTet 2}) ∪
        {localTet 6, localTet 7, localTet 8}) \
        {localTet 3, localTet 4, localTet 5}) ∪
        {localTet 0, localTet 2}) =
      exterior R ∪ {localTet 0, localTet 2, localTet 6, localTet 7, localTet 8} := by
  classical
  ext t
  rcases t with t | t
  · simp [exterior, localTet]
  · fin_cases t <;> simp [exterior, localTet]

end SetCertificate

/-- An arithmetic audit boundary: a closed-core endpoint with exactly
three extra tetrahedra and one extra supported vertex has `PhiSupport`
increased by eight. The numerical count hypotheses are explicit; this
statement does not construct a Pachner path. -/
theorem ClosedTriangulationCore.PhiSupport_add_eight_of_facetSlide_counts
    {K L : Triangulation}
    (hK : ClosedTriangulationCore K)
    (hL : ClosedTriangulationCore L)
    (hKcount : (vertexSupport K).length ≤ K.tets.length)
    (hTet : L.tets.length = K.tets.length + 3)
    (hVert : (vertexSupport L).length = (vertexSupport K).length + 1) :
    PhiSupport L = PhiSupport K + 8 := by
  have hPhiK := hK.PhiSupport_eq_four_mul_tets_sub_vertices
  have hPhiL := hL.PhiSupport_eq_four_mul_tets_sub_vertices
  omega

end Poincare
