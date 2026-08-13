import Poincare.GlobalMove32IncidenceThreeComposition
import Poincare.ComplementVertex
import Poincare.Move23SimpleBistellarData

namespace Poincare

/--
A realized `3 → 2` candidate whose source face is already represented has
an exact local alternative.

Take one tetrahedron on the obstructing source face and the unique other
closed-core tetrahedron across that face.  Their complementary vertices are
distinct.  If the complementary edge is absent, those two tetrahedra form a
genuine legal `2 → 3` site on the obstructing face.  Otherwise the
complementary edge is explicitly represented.
-/
theorem
    ClosedTriangulationCore.exists_legal_move23_or_complementEdge_of_move32_sourceFace_obstruction
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hobstruction :
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts) :
    (∃ m : Move23Site,
      m.a = s.a ∧
      m.b = s.b ∧
      m.c = s.c ∧
      m.LegalIn K) ∨
    (∃ tau rho x y sigma,
      tau ∈ K.tets ∧
      rho ∈ K.tets ∧
      ¬ SameTetVertices tau rho ∧
      s.a ∈ tau.verts ∧
      s.b ∈ tau.verts ∧
      s.c ∈ tau.verts ∧
      s.a ∈ rho.verts ∧
      s.b ∈ rho.verts ∧
      s.c ∈ rho.verts ∧
      x ∈ tau.verts ∧
      x ∉ [s.a, s.b, s.c] ∧
      y ∈ rho.verts ∧
      y ∉ [s.a, s.b, s.c] ∧
      x ≠ y ∧
      sigma ∈ K.tets ∧
      x ∈ sigma.verts ∧
      y ∈ sigma.verts) := by
  classical

  have hfiveS :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hrealized

  have habc : [s.a, s.b, s.c].Nodup := by
    have h := hfiveS
    simp at h ⊢
    aesop

  rcases hobstruction with
    ⟨tau, htauK, haTau, hbTau, hcTau⟩

  rcases
      hcore.exists_other_tet_across_triangle
        habc
        htauK
        haTau
        hbTau
        hcTau with
    ⟨rho, hrhoK, hne, haRho, hbRho, hcRho⟩

  have htauNodup : tau.verts.Nodup :=
    hcore.1 tau htauK

  have hrhoNodup : rho.verts.Nodup :=
    hcore.1 rho hrhoK

  rcases
      Tet.exists_distinct_complement_vertices
        tau
        rho
        htauNodup
        hrhoNodup
        habc
        haTau
        hbTau
        hcTau
        haRho
        hbRho
        hcRho
        hne with
    ⟨x, y,
      hxTau, hxABC,
      hyRho, hyABC,
      hxy,
      hTauCover,
      hRhoCover⟩

  have hsameTau :
      SameTetVertices tau
        (⟨s.a, s.b, s.c, x⟩ : Tet) := by
    intro v
    constructor
    · intro hv
      rcases hTauCover v hv with h | h | h | h
      · subst v
        simp [Tet.verts]
      · subst v
        simp [Tet.verts]
      · subst v
        simp [Tet.verts]
      · subst v
        simp [Tet.verts]
    · intro hv
      simp [Tet.verts] at hv
      rcases hv with h | h | h | h
      · subst v
        exact haTau
      · subst v
        exact hbTau
      · subst v
        exact hcTau
      · subst v
        exact hxTau

  have hsameRho :
      SameTetVertices rho
        (⟨s.a, s.b, s.c, y⟩ : Tet) := by
    intro v
    constructor
    · intro hv
      rcases hRhoCover v hv with h | h | h | h
      · subst v
        simp [Tet.verts]
      · subst v
        simp [Tet.verts]
      · subst v
        simp [Tet.verts]
      · subst v
        simp [Tet.verts]
    · intro hv
      simp [Tet.verts] at hv
      rcases hv with h | h | h | h
      · subst v
        exact haRho
      · subst v
        exact hbRho
      · subst v
        exact hcRho
      · subst v
        exact hyRho

  by_cases hedge :
      ∃ sigma ∈ K.tets,
        x ∈ sigma.verts ∧
        y ∈ sigma.verts

  · rcases hedge with
      ⟨sigma, hsigmaK, hxSigma, hySigma⟩

    exact Or.inr
      ⟨tau, rho, x, y, sigma,
        htauK,
        hrhoK,
        hne,
        haTau,
        hbTau,
        hcTau,
        haRho,
        hbRho,
        hcRho,
        hxTau,
        hxABC,
        hyRho,
        hyABC,
        hxy,
        hsigmaK,
        hxSigma,
        hySigma⟩

  · have hnewEdge :
        ∀ sigma ∈ K.tets,
          ¬ (x ∈ sigma.verts ∧ y ∈ sigma.verts) := by
      intro sigma hsigmaK hxySigma
      exact hedge
        ⟨sigma, hsigmaK, hxySigma⟩

    have hfive :
        [s.a, s.b, s.c, x, y].Nodup :=
      hcore.fiveVertexNodup_of_move23_rawData
        s.a
        s.b
        s.c
        x
        y
        ⟨tau, htauK, hsameTau⟩
        ⟨rho, hrhoK, hsameRho⟩
        hnewEdge

    let m : Move23Site :=
      {
        a := s.a
        b := s.b
        c := s.c
        d := x
        e := y
        distinct := hfive
      }

    have hshared :
        m.SharedFaceExactlyTwo K := by
      have hlength :=
        hcore.2.2
          s.a
          s.b
          s.c
          habc
          ⟨tau, htauK, haTau, hbTau, hcTau⟩
      simpa [m, Move23Site.SharedFaceExactlyTwo] using hlength

    have hmRealized :
        m.RealizedIn K := by
      constructor
      · refine ⟨tau, htauK, ?_⟩
        simpa [m, Move23Site.leftTet] using hsameTau
      · refine ⟨rho, hrhoK, ?_⟩
        simpa [m, Move23Site.rightTet] using hsameRho

    have hmNewEdge :
        m.NewEdgeAbsent K := by
      simpa [m, Move23Site.NewEdgeAbsent] using hnewEdge

    exact Or.inl
      ⟨m, rfl, rfl, rfl,
        hmRealized,
        hshared,
        hmNewEdge⟩

end Poincare
