import Poincare.Move41DegreeSupportBalance

namespace Poincare

/-- A genuine legal `4 → 1` move is a strict `PhiSupport` descent as soon as
one outer vertex has positive defect.  The conclusion packages the preserved
closed core and the actual glued carrier homeomorphism. -/
theorem exists_closedCore_homeomorphic_PhiSupport_lt_of_move41
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move41Site)
    (hlegal : s.LegalIn K)
    (hdegree :
      6 ≤ vertexDegree K s.a ∧
      6 ≤ vertexDegree K s.b ∧
      6 ≤ vertexDegree K s.c ∧
      6 ≤ vertexDegree K s.d) :
    ∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K') := by
  have houter := hcore.move41Site_replace_outer_vertexDegree s hlegal
  have hcenter := hcore.move41Site_center_vertexDegree_eq_four s hlegal
  have hbalance := hcore.move41Site_replace_PhiSupport_balance s hlegal
  have defect_drop {v : Nat}
      (hdeg : vertexDegree K v = vertexDegree (s.replace K) v + 2)
      (hsix : 6 ≤ vertexDegree K v) :
      vertexDefect (s.replace K) v < vertexDefect K v := by
    unfold vertexDefect targetDegree
    rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega),
      Int.natAbs_natCast_sub_natCast_of_ge (by omega)]
    omega
  have hstrict : PhiSupport (s.replace K) < PhiSupport K := by
    have ha := defect_drop houter.1 hdegree.1
    have hb := defect_drop houter.2.1 hdegree.2.1
    have hc := defect_drop houter.2.2.1 hdegree.2.2.1
    have hd := defect_drop houter.2.2.2 hdegree.2.2.2
    simp [vertexDefect, targetDegree, hcenter] at hbalance
    omega
  exact ⟨s.replace K,
    hcore.move41Site_replace_closedCore s hlegal,
    hstrict,
    ⟨hcore.move41GeometricCarrierHomeomorph s hlegal⟩⟩

end Poincare
