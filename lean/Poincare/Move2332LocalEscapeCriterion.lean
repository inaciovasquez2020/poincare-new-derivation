import Poincare.Move2332CrossPolytopeEscapeTopology
import Poincare.GlobalPhiSupportDegreeGap

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

theorem move2332Block_PhiSupport_add_four_eq
    {K0 : Triangulation}
    (hcore0 : ClosedTriangulationCore K0)
    (m23 : Move23Site) (h23 : m23.LegalIn K0)
    (m32₁ : Move32Site)
    (h32₁ : m32₁.LegalIn (m23.replace K0))
    (hcore1 : ClosedTriangulationCore (m23.replace K0))
    (m32₂ : Move32Site)
    (h32₂ : m32₂.LegalIn (m32₁.replace (m23.replace K0)))
    (hcore2 : ClosedTriangulationCore (m32₁.replace (m23.replace K0)))
    (hcore3 :
      ClosedTriangulationCore
        (m32₂.replace (m32₁.replace (m23.replace K0)))) :
    PhiSupport (m32₂.replace (m32₁.replace (m23.replace K0))) + 4 =
      PhiSupport K0 := by
  have h23realized : m23.RealizedIn K0 := h23.1
  rcases h23realized with
    ⟨⟨τd, hτd, hτdMatch⟩, ⟨τe, hτe, hτeMatch⟩⟩

  have hd0Support : m23.d ∈ vertexSupport K0 := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨τd, hτd, (hτdMatch m23.d).2 (by
      simp [Move23Site.leftTet, Tet.verts])⟩

  have he0Support : m23.e ∈ vertexSupport K0 := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨τe, hτe, (hτeMatch m23.e).2 (by
      simp [Move23Site.rightTet, Tet.verts])⟩

  have hd0 : 4 ≤ vertexDegree K0 m23.d :=
    hcore0.vertexDegree_ge_four_of_mem_vertexSupport hd0Support
  have he0 : 4 ≤ vertexDegree K0 m23.e :=
    hcore0.vertexDegree_ge_four_of_mem_vertexSupport he0Support

  rcases m23.replace_vertexDegree_site K0 h23 with
    ⟨_, _, _, hd23, he23⟩

  have hdDef23 :
      vertexDefect (m23.replace K0) m23.d =
        vertexDefect K0 m23.d + 2 :=
    (vertexDefect_of_degree_add_two
      K0 (m23.replace K0) m23.d hd23).2.2 hd0

  have heDef23 :
      vertexDefect (m23.replace K0) m23.e =
        vertexDefect K0 m23.e + 2 :=
    (vertexDefect_of_degree_add_two
      K0 (m23.replace K0) m23.e he23).2.2 he0

  have hb23 := m23.replace_PhiSupport_balance K0 h23

  have hPhi23 :
      PhiSupport (m23.replace K0) = PhiSupport K0 + 4 := by
    omega

  have hmove32 :
      ∀ {J : Triangulation}
        (hJ : ClosedTriangulationCore J)
        (s : Move32Site)
        (hs : s.LegalIn J)
        (hpost : ClosedTriangulationCore (s.replace J)),
        PhiSupport (s.replace J) + 4 = PhiSupport J := by
    intro J hJ s hs hpost

    have hrealized : s.RealizedIn J := hs.1
    rcases hrealized with ⟨⟨τ, hτ, hmatch⟩, _, _⟩

    have hdSupport : s.d ∈ vertexSupport J := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨τ, hτ, (hmatch s.d).2 (by
        simp [Move32Site.targetTet₀, Tet.verts])⟩

    have heSupport : s.e ∈ vertexSupport J := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨τ, hτ, (hmatch s.e).2 (by
        simp [Move32Site.targetTet₀, Tet.verts])⟩

    have hdPostSupport : s.d ∈ vertexSupport (s.replace J) :=
      (hJ.move32Site_replace_vertexSupport_mem_iff s hs s.d).2 hdSupport
    have hePostSupport : s.e ∈ vertexSupport (s.replace J) :=
      (hJ.move32Site_replace_vertexSupport_mem_iff s hs s.e).2 heSupport

    have hdPost : 4 ≤ vertexDegree (s.replace J) s.d :=
      hpost.vertexDegree_ge_four_of_mem_vertexSupport hdPostSupport
    have hePost : 4 ≤ vertexDegree (s.replace J) s.e :=
      hpost.vertexDegree_ge_four_of_mem_vertexSupport hePostSupport

    rcases hJ.move32Site_replace_vertexDegree_site s hs with
      ⟨_, _, _, hd32, he32⟩

    have hdDef32 :
        vertexDefect J s.d = vertexDefect (s.replace J) s.d + 2 :=
      (vertexDefect_of_degree_add_two
        (s.replace J) J s.d hd32).2.2 hdPost

    have heDef32 :
        vertexDefect J s.e = vertexDefect (s.replace J) s.e + 2 :=
      (vertexDefect_of_degree_add_two
        (s.replace J) J s.e he32).2.2 hePost

    have hb32 := hJ.move32Site_replace_PhiSupport_balance s hs
    omega

  have hPhi32₁ := hmove32 hcore1 m32₁ h32₁ hcore2
  have hPhi32₂ := hmove32 hcore2 m32₂ h32₂ hcore3
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
