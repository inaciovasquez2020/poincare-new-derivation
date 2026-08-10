import Poincare.Move2332CrossPolytopeEscapeTopology

namespace Poincare

theorem move2332Block_PhiSupport_balance
    {K0 : Triangulation}
    (m23 : Move23Site) (h23 : m23.LegalIn K0)
    (m32₁ : Move32Site)
    (h32₁ : m32₁.LegalIn (m23.replace K0))
    (hcore1 : ClosedTriangulationCore (m23.replace K0))
    (m32₂ : Move32Site)
    (h32₂ : m32₂.LegalIn (m32₁.replace (m23.replace K0)))
    (hcore2 : ClosedTriangulationCore (m32₁.replace (m23.replace K0))) :
    PhiSupport K0 +
        (vertexDefect (m23.replace K0) m23.d +
          vertexDefect (m23.replace K0) m23.e) +
        (vertexDefect (m32₁.replace (m23.replace K0)) m32₁.d +
          vertexDefect (m32₁.replace (m23.replace K0)) m32₁.e) +
        (vertexDefect
            (m32₂.replace (m32₁.replace (m23.replace K0))) m32₂.d +
          vertexDefect
            (m32₂.replace (m32₁.replace (m23.replace K0))) m32₂.e) =
      PhiSupport (m32₂.replace (m32₁.replace (m23.replace K0))) +
        (vertexDefect K0 m23.d + vertexDefect K0 m23.e) +
        (vertexDefect (m23.replace K0) m32₁.d +
          vertexDefect (m23.replace K0) m32₁.e) +
        (vertexDefect (m32₁.replace (m23.replace K0)) m32₂.d +
          vertexDefect (m32₁.replace (m23.replace K0)) m32₂.e) := by
  have hb23 := m23.replace_PhiSupport_balance K0 h23
  have hb32₁ := hcore1.move32Site_replace_PhiSupport_balance m32₁ h32₁
  have hb32₂ := hcore2.move32Site_replace_PhiSupport_balance m32₂ h32₂
  omega

theorem move2332Block_PhiSupport_lt_of_local_degree_conditions
    {K0 : Triangulation}
    (m23 : Move23Site) (h23 : m23.LegalIn K0)
    (m32₁ : Move32Site)
    (h32₁ : m32₁.LegalIn (m23.replace K0))
    (hcore1 : ClosedTriangulationCore (m23.replace K0))
    (m32₂ : Move32Site)
    (h32₂ : m32₂.LegalIn (m32₁.replace (m23.replace K0)))
    (hcore2 : ClosedTriangulationCore (m32₁.replace (m23.replace K0)))
    (hlocal :
      (vertexDefect (m23.replace K0) m23.d +
          vertexDefect (m23.replace K0) m23.e) +
        (vertexDefect (m32₁.replace (m23.replace K0)) m32₁.d +
          vertexDefect (m32₁.replace (m23.replace K0)) m32₁.e) +
        (vertexDefect
            (m32₂.replace (m32₁.replace (m23.replace K0))) m32₂.d +
          vertexDefect
            (m32₂.replace (m32₁.replace (m23.replace K0))) m32₂.e) <
      (vertexDefect K0 m23.d + vertexDefect K0 m23.e) +
        (vertexDefect (m23.replace K0) m32₁.d +
          vertexDefect (m23.replace K0) m32₁.e) +
        (vertexDefect (m32₁.replace (m23.replace K0)) m32₂.d +
          vertexDefect (m32₁.replace (m23.replace K0)) m32₂.e)) :
    PhiSupport (m32₂.replace (m32₁.replace (m23.replace K0))) <
      PhiSupport K0 := by
  have hbalance := move2332Block_PhiSupport_balance m23 h23 m32₁ h32₁
    hcore1 m32₂ h32₂ hcore2
  omega

theorem crossPolytopeBoundary4_move2332Block_PhiSupport_lt_of_local_degree_conditions :
    PhiSupport crossPolytopeEscapeFinal < PhiSupport crossPolytopeBoundary4 := by
  apply move2332Block_PhiSupport_lt_of_local_degree_conditions
    crossPolytopeEscapeMove23 crossPolytopeEscapeMove23_legal
    crossPolytopeEscapeMove32₁ crossPolytopeEscapeMove32₁_legal
    crossPolytopeEscapeAfter23_closedCore
    crossPolytopeEscapeMove32₂ crossPolytopeEscapeMove32₂_legal
    crossPolytopeEscapeAfter32One_closedCore
  decide

end Poincare
