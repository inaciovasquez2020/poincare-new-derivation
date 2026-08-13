import Poincare.GlobalDegreeFourMove41OrFiveTet
import Poincare.GlobalPhiSupportDegreeGap
import Poincare.VertexIncidenceCounting
import Mathlib.Tactic

namespace Poincare

/--
If every represented tetrahedron belongs to one fixed five-tetrahedron
Move41 boundary cluster, then the Move41 center has degree exactly four.

The argument deliberately avoids an exact manual enumeration of the four
center-containing members.  The global five-tetrahedron cover bounds the
entire tetrahedron list by five.  Hence the center has degree at most five.
It is represented by the first source tetrahedron, while the closed-core
degree gap forces every represented vertex to have degree four or at least
six.  The latter alternative is impossible.
-/
theorem
    ClosedTriangulationCore.vertexDegree_eq_four_of_global_fiveTet_cover
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move41Site)
    {tau0 tau1 tau2 tau3 target : Tet}
    (htau0K : tau0 ∈ K.tets)
    (htau0 :
      SameTetVertices tau0 s.sourceTet₀)
    (hglobal :
      ∀ rho ∈ K.tets,
        rho = tau0 ∨
        rho = tau1 ∨
        rho = tau2 ∨
        rho = tau3 ∨
        rho = target) :
    vertexDegree K s.e = 4 := by
  classical

  have hKtetsNodup :
      K.tets.Nodup := by
    exact
      hcore.2.1.imp
        (by
          intro sigma rho hne hEq
          apply hne
          subst rho
          intro v
          rfl)

  let C : Finset Tet :=
    {tau0, tau1, tau2, tau3, target}

  have hsubset :
      K.tets.toFinset ⊆ C := by
    intro rho hrho
    have hrhoK :
        rho ∈ K.tets :=
      List.mem_toFinset.mp hrho

    rcases hglobal rho hrhoK with
      rfl | rfl | rfl | rfl | rfl <;>
      simp [C]

  have hcard0 :
      C.card ≤
        ({tau1, tau2, tau3, target} : Finset Tet).card + 1 := by
    simpa [C] using
      Finset.card_insert_le
        tau0
        ({tau1, tau2, tau3, target} : Finset Tet)

  have hcard1 :
      ({tau1, tau2, tau3, target} : Finset Tet).card ≤
        ({tau2, tau3, target} : Finset Tet).card + 1 := by
    exact
      Finset.card_insert_le
        tau1
        ({tau2, tau3, target} : Finset Tet)

  have hcard2 :
      ({tau2, tau3, target} : Finset Tet).card ≤
        ({tau3, target} : Finset Tet).card + 1 := by
    exact
      Finset.card_insert_le
        tau2
        ({tau3, target} : Finset Tet)

  have hcard3 :
      ({tau3, target} : Finset Tet).card ≤
        ({target} : Finset Tet).card + 1 := by
    exact
      Finset.card_insert_le
        tau3
        ({target} : Finset Tet)

  have hsingle :
      ({target} : Finset Tet).card = 1 := by
    simp

  have hCcard :
      C.card ≤ 5 := by
    omega

  have hKcard :
      K.tets.toFinset.card ≤ C.card :=
    Finset.card_le_card hsubset

  have htoFinset :
      K.tets.toFinset.card =
        K.tets.length :=
    List.toFinset_card_of_nodup
      hKtetsNodup

  have hKlength :
      K.tets.length ≤ 5 := by
    omega

  have heSource :
      s.e ∈ s.sourceTet₀.verts := by
    simp [
      Move41Site.sourceTet₀,
      Tet.verts
    ]

  have heTau0 :
      s.e ∈ tau0.verts :=
    (htau0 s.e).2 heSource

  have heSupport :
      s.e ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    apply List.mem_flatMap.mpr
    exact
      ⟨tau0, htau0K, heTau0⟩

  have hfilter :
      (K.tets.filter
        (fun tau =>
          s.e ∈ tau.verts)).length ≤
        K.tets.length :=
    List.length_filter_le
      (fun tau =>
        s.e ∈ tau.verts)
      K.tets

  have hdegreeCount :
      vertexDegree K s.e =
        (K.tets.filter
          (fun tau =>
            s.e ∈ tau.verts)).length :=
    hcore.vertexDegree_eq_incidentTetCount
      s.e

  have hdegreeLe :
      vertexDegree K s.e ≤ 5 := by
    omega

  rcases
      hcore.vertexDegree_eq_four_or_ge_six_of_mem_vertexSupport
        heSupport with
    hfour | hsix

  · exact hfour

  · omega

end Poincare
