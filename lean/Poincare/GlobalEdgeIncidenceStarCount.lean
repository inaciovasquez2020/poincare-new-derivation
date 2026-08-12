import Poincare.GlobalMove32IncidenceThreeSplit
import Mathlib.Tactic

namespace Poincare

private theorem
    vertexLinkStarTriangles_length_eq_edgeIncidence_aux
    (v x : Nat)
    (hvx : v ≠ x) :
    ∀ tets : List Tet,
      (∀ τ ∈ tets, τ.verts.Nodup) →
      (((tets.filterMap
          (fun τ => τ.linkTriangleAt? v)).filter
          (fun σ => x ∈ σ.verts)).length =
        (tets.filter
          (fun τ =>
            v ∈ τ.verts ∧
            x ∈ τ.verts)).length) := by

  intro tets hnodup

  induction tets with

  | nil =>
      simp

  | cons τ rest ih =>

      have hτNodup :
          τ.verts.Nodup :=
        hnodup τ (by simp)

      have hrest :
          ∀ ρ ∈ rest,
            ρ.verts.Nodup := by
        intro ρ hρ
        exact
          hnodup ρ (by simp [hρ])

      have ih' :=
        ih hrest

      cases hopt :
          τ.linkTriangleAt? v with

      | none =>

          have hvNot :
              v ∉ τ.verts :=
            (τ.linkTriangleAt?_eq_none_iff v).1
              hopt

          simp [
            hopt,
            hvNot,
            ih'
          ]

      | some σ =>

          have hvTet :
              v ∈ τ.verts := by
            rw [
              ← τ.linkTriangleAt?_isSome_iff v
            ]
            simp [hopt]

          have hxIff :
              x ∈ σ.verts ↔
                x ∈ τ.verts :=
            τ.mem_linkTriangleAt?_iff
              v x σ
              hopt
              hvx.symm

          by_cases hxTet :
              x ∈ τ.verts

          · have hxSigma :
                x ∈ σ.verts :=
              hxIff.2 hxTet

            simp [
              hopt,
              hvTet,
              hxTet,
              hxSigma,
              ih'
            ]

          · have hxSigma :
                x ∉ σ.verts := by
              intro hx
              exact
                hxTet
                  (hxIff.1 hx)

            simp [
              hopt,
              hvTet,
              hxTet,
              hxSigma,
              ih'
            ]

/--
For two distinct labels `v,x` in a closed triangulation core, the number
of represented link triangles in the star of `x` inside `Lk(v)` equals
the number of ambient tetrahedra containing both `v` and `x`.
-/
theorem
    ClosedTriangulationCore.vertexLinkStarTriangles_length_eq_edgeIncidence
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x) :
    (vertexLinkStarTriangles K v x).length =
      (K.tets.filter
        (fun τ =>
          v ∈ τ.verts ∧
          x ∈ τ.verts)).length := by

  simpa [
    vertexLinkStarTriangles,
    vertexLinkTriangles
  ] using
    vertexLinkStarTriangles_length_eq_edgeIncidence_aux
      v x hvx
      K.tets
      hcore.1

/--
An ambient edge of tetrahedron-incidence exactly three therefore appears
as a three-triangle represented vertex-link star.
-/
theorem
    ClosedTriangulationCore.vertexLinkStarTriangles_length_eq_three_of_edgeIncidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hthree :
      (K.tets.filter
        (fun τ =>
          v ∈ τ.verts ∧
          x ∈ τ.verts)).length = 3) :
    (vertexLinkStarTriangles K v x).length = 3 := by

  rw [
    hcore.vertexLinkStarTriangles_length_eq_edgeIncidence
      v x hvx
  ]

  exact hthree

/--
Positive ambient edge incidence also makes the second endpoint represented
as a vertex of the first endpoint's link.
-/
theorem
    ClosedTriangulationCore.vertexLinkVertexRepresented_of_edgeIncidence_pos
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hpos :
      0 <
        (K.tets.filter
          (fun τ =>
            v ∈ τ.verts ∧
            x ∈ τ.verts)).length) :
    VertexLinkVertexRepresented K v x := by

  have hstarPos :
      0 <
        (vertexLinkStarTriangles
          K v x).length := by
    rw [
      hcore.vertexLinkStarTriangles_length_eq_edgeIncidence
        v x hvx
    ]
    exact hpos

  apply
    (vertexLinkVertexRepresented_iff_star_nonempty
      K v x).2

  cases hstar :
      vertexLinkStarTriangles K v x with

  | nil =>
      simp [hstar] at hstarPos

  | cons σ rest =>
      exact
        ⟨σ, by simp⟩

/--
Incidence three supplies both the represented link vertex and its exact
three-triangle star.
-/
theorem
    ClosedTriangulationCore.vertexLinkVertexRepresented_and_star_length_three_of_edgeIncidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hthree :
      (K.tets.filter
        (fun τ =>
          v ∈ τ.verts ∧
          x ∈ τ.verts)).length = 3) :
    VertexLinkVertexRepresented K v x ∧
      (vertexLinkStarTriangles K v x).length = 3 := by

  have hpos :
      0 <
        (K.tets.filter
          (fun τ =>
            v ∈ τ.verts ∧
            x ∈ τ.verts)).length := by
    omega

  exact
    ⟨hcore.vertexLinkVertexRepresented_of_edgeIncidence_pos
        v x hvx hpos,
      hcore.vertexLinkStarTriangles_length_eq_three_of_edgeIncidence_three
        v x hvx hthree⟩

end Poincare
