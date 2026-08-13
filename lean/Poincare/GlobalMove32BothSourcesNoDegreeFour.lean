import Poincare.GlobalFiveTetNoDegreeFourContradiction
import Poincare.GlobalDegreeFourTargetPresentSaturation
import Poincare.DegreeFourConnectedLinkClassification
import Poincare.Move32CombinatorialFoundation

namespace Poincare

/--
In a closed core with connected represented vertex links and connected
tetrahedron-overlap graph, a realized `3 → 2` configuration cannot have both
of its source tetrahedra represented when degree four is globally excluded.

Indeed the three realized targets together with the two represented sources
form the five tetrahedra of the corresponding `4 → 1` boundary cluster.
Connectedness makes that cluster global, forcing a degree-four vertex.
-/
theorem
    ClosedTriangulationCore.not_both_move32_sources_represented_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hsource0 :
      ∃ tau ∈ K.tets,
        SameTetVertices tau s.sourceTet₀)
    (hsource1 :
      ∃ tau ∈ K.tets,
        SameTetVertices tau s.sourceTet₁) :
    False := by
  classical

  have hfive :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hrealized

  rcases hrealized with
    ⟨htarget0, htarget1, htarget2⟩

  let m : Move41Site :=
    {
      a := s.a
      b := s.b
      c := s.c
      d := s.d
      e := s.e
      distinct := hfive
    }

  have representedExactlyOnce
      (source : Tet)
      (hex :
        ∃ tau ∈ K.tets,
          SameTetVertices tau source) :
      (K.tets.filter
        (fun tau =>
          sameTetVerticesBool tau source)).length = 1 := by

    obtain ⟨tau, htauK, hsame⟩ := hex

    have hunique :=
      hcore.existsUnique_sameTetVertices
        ⟨tau, htauK, hsame⟩

    let L :=
      K.tets.filter
        (fun rho =>
          sameTetVerticesBool rho source)

    have htauL : tau ∈ L := by
      simp [
        L,
        htauK,
        sameTetVerticesBool_eq_true_iff,
        hsame
      ]

    have hmem :
        ∀ rho,
          rho ∈ L ↔ rho = tau := by
      intro rho
      constructor

      · intro hrho
        have hrho' :
            rho ∈ K.tets ∧
              SameTetVertices rho source := by
          simpa [
            L,
            sameTetVerticesBool_eq_true_iff
          ] using hrho

        exact
          hunique.unique
            hrho'
            ⟨htauK, hsame⟩

      · rintro rfl
        exact htauL

    have hfinset :
        L.toFinset = {tau} := by
      ext rho
      simp only [
        List.mem_toFinset,
        Finset.mem_singleton
      ]
      exact hmem rho

    have hnodupK :
        K.tets.Nodup :=
      hcore.2.1.imp
        (fun hnot heq =>
          hnot
            (by
              subst heq
              exact sameTetVertices_refl _))

    have hnodupL :
        L.Nodup := by
      exact hnodupK.filter _

    change L.length = 1

    rw [
      ← List.toFinset_card_of_nodup hnodupL,
      hfinset
    ]

    simp

  have hsourcesRepresented :
      ∀ source ∈ m.sourceTets,
        ∃ tau ∈ K.tets,
          SameTetVertices tau source := by
    intro source hsource

    simp [m, Move41Site.sourceTets] at hsource

    rcases hsource with
      rfl | rfl | rfl | rfl

    · simpa [
        m,
        Move41Site.sourceTet₀,
        Move32Site.sourceTet₁
      ] using hsource1

    · simpa [
        m,
        Move41Site.sourceTet₁,
        Move32Site.targetTet₀
      ] using htarget0

    · simpa [
        m,
        Move41Site.sourceTet₂,
        Move32Site.targetTet₁
      ] using htarget1

    · simpa [
        m,
        Move41Site.sourceTet₃,
        Move32Site.targetTet₂
      ] using htarget2

  have hsources :
      ∀ source ∈ m.sourceTets,
        (K.tets.filter
          (fun tau =>
            sameTetVerticesBool tau source)).length = 1 := by
    intro source hsource
    exact
      representedExactlyOnce
        source
        (hsourcesRepresented source hsource)

  have htarget :
      ∃ tau ∈ K.tets,
        SameTetVertices tau m.targetTet := by
    simpa [
      m,
      Move41Site.targetTet,
      Move32Site.sourceTet₀
    ] using hsource0

  obtain
    ⟨tau0, tau1, tau2, tau3, target,
      htau0K, htau0,
      htau1K, htau1,
      htau2K, htau2,
      htau3K, htau3,
      htargetK, htargetMatch,
      hnodup⟩ :=
    m.exists_represented_fiveTetCluster_nodup_of_targetPresent
      hsources
      htarget

  let C : Tet → Prop :=
    fun rho =>
      rho = tau0 ∨
      rho = tau1 ∨
      rho = tau2 ∨
      rho = tau3 ∨
      rho = target

  have hstarRaw :=
    Move41Site.represented_fiveTetCluster_vertexStarClosed_of_connectedLinks
      hcore
      hlinks
      m
      htau0K
      htau0
      htau1K
      htau1
      htau2K
      htau2
      htau3K
      htau3
      htargetK
      htargetMatch
      hnodup

  have hstar :
      ∀ v,
        ∀ alpha ∈ K.tets,
          C alpha →
            v ∈ alpha.verts →
              ∀ beta ∈ K.tets,
                v ∈ beta.verts →
                  C beta := by
    intro v alpha halphaK halphaC hvalpha
      beta hbetaK hvbeta

    have hout :=
      hstarRaw
        alpha
        halphaK
        (by simpa [C] using halphaC)
        v
        hvalpha
        beta
        hbetaK
        hvbeta

    simpa [C] using hout

  have hseed :
      ∃ tau ∈ K.tets,
        C tau := by
    exact
      ⟨tau0, htau0K, by
        simp [C]⟩

  have hglobalC :
      ∀ rho ∈ K.tets,
        C rho :=
    Move41Site.targetPresent_fiveTetCluster_global_of_vertexStarClosed
      hconn
      m
      C
      hseed
      hstar

  have hglobal :
      ∀ rho ∈ K.tets,
        rho = tau0 ∨
        rho = tau1 ∨
        rho = tau2 ∨
        rho = tau3 ∨
        rho = target := by
    intro rho hrhoK
    simpa [C] using hglobalC rho hrhoK

  exact
    hcore.not_global_fiveTet_cover_of_no_degree_four
      hNoFour
      m
      htau0K
      htau0
      hglobal

end Poincare
