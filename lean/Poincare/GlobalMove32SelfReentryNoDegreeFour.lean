import Poincare.GlobalMove32BothSourcesNoDegreeFour
import Poincare.ComplementVertex
import Mathlib.Tactic

namespace Poincare

/--
In the no-degree-four branch, the two complementary vertices of a represented
Move32 source face cannot be exactly the original shared-edge endpoints.

If the complementary pair is `(d,e)` or `(e,d)`, the two tetrahedra across
the represented source face are exactly representatives of `sourceTet₀` and
`sourceTet₁`.  The already-certified both-sources contradiction then closes
the branch.
-/
theorem
    ClosedTriangulationCore.not_move32_complementEdge_self_reentry_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn :
      TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    {tau rho : Tet}
    {x y : Nat}
    (htauK : tau ∈ K.tets)
    (hrhoK : rho ∈ K.tets)
    (hne :
      ¬ SameTetVertices tau rho)
    (haTau : s.a ∈ tau.verts)
    (hbTau : s.b ∈ tau.verts)
    (hcTau : s.c ∈ tau.verts)
    (haRho : s.a ∈ rho.verts)
    (hbRho : s.b ∈ rho.verts)
    (hcRho : s.c ∈ rho.verts)
    (hxTau : x ∈ tau.verts)
    (hxABC : x ∉ [s.a, s.b, s.c])
    (hyRho : y ∈ rho.verts)
    (hyABC : y ∉ [s.a, s.b, s.c])
    (hself :
      (x = s.d ∧ y = s.e) ∨
      (x = s.e ∧ y = s.d)) :
    False := by
  classical

  have hfive :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct
      s hrealized

  have habc :
      [s.a, s.b, s.c].Nodup := by
    have h := hfive
    simp at h ⊢
    aesop

  have htauNodup :
      tau.verts.Nodup :=
    hcore.1 tau htauK

  have hrhoNodup :
      rho.verts.Nodup :=
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
    ⟨u, v,
      huTau, huABC,
      hvRho, hvABC,
      huv,
      hTauCover,
      hRhoCover⟩

  have hxu :
      x = u := by
    have hcover :=
      hTauCover x hxTau
    have hxABC' := hxABC
    simp at hxABC'
    aesop

  have hyv :
      y = v := by
    have hcover :=
      hRhoCover y hyRho
    have hyABC' := hyABC
    simp at hyABC'
    aesop

  subst u
  subst v

  have hsameTauX :
      SameTetVertices
        tau
        (⟨s.a, s.b, s.c, x⟩ : Tet) := by
    intro z
    constructor

    · intro hz
      rcases hTauCover z hz with
        h | h | h | h

      · subst z
        simp [Tet.verts]

      · subst z
        simp [Tet.verts]

      · subst z
        simp [Tet.verts]

      · subst z
        simp [Tet.verts]

    · intro hz
      simp [Tet.verts] at hz

      rcases hz with
        h | h | h | h

      · subst z
        exact haTau

      · subst z
        exact hbTau

      · subst z
        exact hcTau

      · subst z
        exact hxTau

  have hsameRhoY :
      SameTetVertices
        rho
        (⟨s.a, s.b, s.c, y⟩ : Tet) := by
    intro z
    constructor

    · intro hz
      rcases hRhoCover z hz with
        h | h | h | h

      · subst z
        simp [Tet.verts]

      · subst z
        simp [Tet.verts]

      · subst z
        simp [Tet.verts]

      · subst z
        simp [Tet.verts]

    · intro hz
      simp [Tet.verts] at hz

      rcases hz with
        h | h | h | h

      · subst z
        exact haRho

      · subst z
        exact hbRho

      · subst z
        exact hcRho

      · subst z
        exact hyRho

  rcases hself with
    hdirect | hreverse

  · rcases hdirect with
      ⟨hxd, hye⟩

    have hsource0 :
        ∃ t ∈ K.tets,
          SameTetVertices
            t
            s.sourceTet₀ := by
      refine ⟨tau, htauK, ?_⟩
      simpa [
        Move32Site.sourceTet₀,
        hxd
      ] using hsameTauX

    have hsource1 :
        ∃ t ∈ K.tets,
          SameTetVertices
            t
            s.sourceTet₁ := by
      refine ⟨rho, hrhoK, ?_⟩
      simpa [
        Move32Site.sourceTet₁,
        hye
      ] using hsameRhoY

    exact
      hcore.not_both_move32_sources_represented_of_no_degree_four
        hlinks
        hconn
        hNoFour
        s
        hrealized
        hsource0
        hsource1

  · rcases hreverse with
      ⟨hxe, hyd⟩

    have hsource0 :
        ∃ t ∈ K.tets,
          SameTetVertices
            t
            s.sourceTet₀ := by
      refine ⟨rho, hrhoK, ?_⟩
      simpa [
        Move32Site.sourceTet₀,
        hyd
      ] using hsameRhoY

    have hsource1 :
        ∃ t ∈ K.tets,
          SameTetVertices
            t
            s.sourceTet₁ := by
      refine ⟨tau, htauK, ?_⟩
      simpa [
        Move32Site.sourceTet₁,
        hxe
      ] using hsameTauX

    exact
      hcore.not_both_move32_sources_represented_of_no_degree_four
        hlinks
        hconn
        hNoFour
        s
        hrealized
        hsource0
        hsource1

end Poincare
