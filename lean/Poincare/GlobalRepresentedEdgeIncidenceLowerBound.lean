import Poincare.GlobalEdgeIncidenceStarCount
import Mathlib.Tactic

namespace Poincare

/--
Every positively represented ambient edge of a closed triangulation has
tetrahedron incidence at least three.

The proof passes to the corresponding represented vertex in a vertex link.
Closed-core face incidence gives degree two in the link star.  Starting with
one represented star triangle, degree two supplies two further pairwise
distinct star triangles.  Hence the star has at least three elements, and the
certified star-count/ambient-incidence identity transfers that lower bound
back to the ambient edge.
-/
theorem
    ClosedTriangulationCore.edgeIncidence_three_le_of_pos
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hpos :
      0 <
        (K.tets.filter
          (fun tau =>
            v ∈ tau.verts ∧
            x ∈ tau.verts)).length) :
    3 ≤
      (K.tets.filter
        (fun tau =>
          v ∈ tau.verts ∧
          x ∈ tau.verts)).length := by
  classical

  have hrep :
      VertexLinkVertexRepresented K v x :=
    hcore.vertexLinkVertexRepresented_of_edgeIncidence_pos
      v x hvx hpos

  obtain ⟨sigma, hsigma⟩ :=
    (vertexLinkVertexRepresented_iff_star_nonempty K v x).1 hrep

  have hdeg :
      VertexLinkStarDegreeTwo K v x :=
    hcore.vertexLinkStarDegreeTwo hrep

  obtain
      ⟨rho1, rho2,
        hrho1_ne_sigma,
        hrho2_ne_sigma,
        hrho12,
        hadj1,
        hadj2,
        _hunique⟩ :=
    hdeg sigma hsigma

  have hrho1 :
      rho1 ∈ vertexLinkStarTriangles K v x :=
    hadj1.2.1

  have hrho2 :
      rho2 ∈ vertexLinkStarTriangles K v x :=
    hadj2.2.1

  have hnodup :
      (vertexLinkStarTriangles K v x).Nodup := by
    unfold vertexLinkStarTriangles
    apply List.Nodup.filter
    exact vertexLinkTriangles_nodup K hcore v

  let S : Finset LinkTriangle :=
    {sigma, rho1, rho2}

  have hsubset :
      S ⊆
        (vertexLinkStarTriangles K v x).toFinset := by
    intro q hq
    simp only [
      S,
      Finset.mem_insert,
      Finset.mem_singleton
    ] at hq

    rcases hq with hq | hq | hq

    · subst q
      exact List.mem_toFinset.mpr hsigma

    · subst q
      exact List.mem_toFinset.mpr hrho1

    · subst q
      exact List.mem_toFinset.mpr hrho2

  have hScard :
      S.card = 3 := by
    simp [
      S,
      hrho1_ne_sigma,
      hrho2_ne_sigma,
      hrho12,
      Ne.symm hrho1_ne_sigma,
      Ne.symm hrho2_ne_sigma,
      Ne.symm hrho12
    ]

  have hcard :
      S.card ≤
        (vertexLinkStarTriangles K v x).toFinset.card :=
    Finset.card_le_card hsubset

  have htoFinset :
      (vertexLinkStarTriangles K v x).toFinset.card =
        (vertexLinkStarTriangles K v x).length :=
    List.toFinset_card_of_nodup hnodup

  rw [hScard, htoFinset] at hcard

  rw [
    hcore.vertexLinkStarTriangles_length_eq_edgeIncidence
      v x hvx
  ] at hcard

  exact hcard

end Poincare
