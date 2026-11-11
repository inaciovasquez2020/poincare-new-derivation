import Poincare.PositionStellarInterfaceBoundary

namespace Poincare

/-- The local face-incidence count of an arbitrary-position stellar insertion
is exactly that of a head stellar insertion with the same exterior tetrahedra.
This statement is about raw list multiplicities, not closed-core legality. -/
theorem Move41Site.insertFreshAt_filter_length
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hfresh : s.e ∉ vertexSupport K)
    (p : Tet → Prop) :
    ((s.insertFreshAt K before after hsource hfresh).tets.filter p).length =
      ((s.headStellar (before ++ after)).tets.filter p).length := by
  change ((before ++ s.sourceTets ++ after).filter p).length =
    ((s.sourceTets ++ (before ++ after)).filter p).length
  simp only [List.filter_append, List.length_append]
  omega

/-- The source's old face multiplicities are similarly independent of
whether the selected target tetrahedron occurs at the head or later. -/
theorem Move41Site.selected_source_filter_length
    (s : Move41Site) (before after : List Tet) (p : Tet → Prop) :
    ((before ++ s.targetTet :: after).filter p).length =
      ((s.targetTet :: (before ++ after)).filter p).length := by
  simp only [List.filter_append, List.length_append, List.filter_cons,
    List.length_cons]
  split <;> simp [List.filter_append, List.length_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Poincare
