import Mathlib

namespace Poincare

section Fixed43ResourceBounds
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

private abbrev Edge12 := Fin 12 × Fin 12
private abbrev Triangle12 := Fin 12 × Fin 12 × Fin 12

private def triangleBoundaryEdges
    (t : Triangle12) : List Edge12 :=
  [(t.1, t.2.1), (t.1, t.2.2), (t.2.1, t.2.2)]

private def edgeCoefficient
    (chain : List Edge12) (edge : Edge12) : ZMod 2 :=
  (chain.map fun x =>
    if x = edge then (1 : ZMod 2) else 0).sum

private theorem weightedSum_eq_coefficientSum
    (w : Edge12 → ZMod 2) (chain : List Edge12) :
    (chain.map w).sum =
      ∑ edge : Edge12,
        edgeCoefficient chain edge * w edge := by
  classical
  induction chain with
  | nil =>
      simp [edgeCoefficient]
  | cons x xs ih =>
      calc
        ((x :: xs).map w).sum =
            w x + (xs.map w).sum := rfl
        _ = w x + ∑ edge : Edge12,
              edgeCoefficient xs edge * w edge := by
              rw [ih]
        _ = ∑ edge : Edge12,
              edgeCoefficient (x :: xs) edge * w edge := by
              simp [edgeCoefficient, add_mul,
                Finset.sum_add_distrib]

private theorem edge_coefficients_determine_pairing
    (cycle boundary : List Edge12)
    (hcoeff : ∀ edge : Edge12,
      edgeCoefficient cycle edge =
      edgeCoefficient boundary edge)
    (w : Edge12 → ZMod 2) :
    (cycle.map w).sum = (boundary.map w).sum := by
  calc
    (cycle.map w).sum =
        ∑ edge : Edge12,
          edgeCoefficient cycle edge * w edge :=
            weightedSum_eq_coefficientSum w cycle
    _ = ∑ edge : Edge12,
          edgeCoefficient boundary edge * w edge := by
          apply Finset.sum_congr rfl
          intro edge _
          rw [hcoeff edge]
    _ = (boundary.map w).sum :=
          (weightedSum_eq_coefficientSum w boundary).symm

private theorem closed_cocycle_boundary_pairing_zero
    (w : Edge12 → ZMod 2) :
    ∀ chain : List Triangle12,
      (∀ t ∈ chain,
        w (t.1, t.2.1) +
        w (t.1, t.2.2) +
        w (t.2.1, t.2.2) = 0) →
      ((chain.flatMap triangleBoundaryEdges).map w).sum = 0 := by
  intro chain
  induction chain with
  | nil =>
      intro _
      simp
  | cons t ts ih =>
      intro hclosed
      have ht :
          w (t.1, t.2.1) +
          w (t.1, t.2.2) +
          w (t.2.1, t.2.2) = 0 := by
        exact hclosed t (by simp)
      have hts :
          ∀ u ∈ ts,
            w (u.1, u.2.1) +
            w (u.1, u.2.2) +
            w (u.2.1, u.2.2) = 0 := by
        intro u hu
        exact hclosed u (by simp [hu])
      calc
        (((t :: ts).flatMap triangleBoundaryEdges).map w).sum =
            ((triangleBoundaryEdges t).map w).sum +
            ((ts.flatMap triangleBoundaryEdges).map w).sum := by
            simp
        _ = 0 + 0 := by
          have hfirst :
              ((triangleBoundaryEdges t).map w).sum = 0 := by
            simpa [triangleBoundaryEdges, add_assoc] using ht
          rw [hfirst, ih hts]
        _ = 0 := by
          simp

private theorem finite_nonboundary_of_mod2_edge_coefficients
    (w : Edge12 → ZMod 2)
    (cycle : List Edge12)
    (faces : List Triangle12)
    (hclosed : ∀ t ∈ faces,
      w (t.1, t.2.1) +
      w (t.1, t.2.2) +
      w (t.2.1, t.2.2) = 0)
    (hodd : (cycle.map w).sum = 1) :
    ¬ ∃ chain : List Triangle12,
      (∀ t ∈ chain, t ∈ faces) ∧
      (∀ edge : Edge12,
        edgeCoefficient cycle edge =
        edgeCoefficient
          (chain.flatMap triangleBoundaryEdges) edge) := by
  rintro ⟨chain, hsubset, hcoeff⟩

  have hchainClosed :
      ∀ t ∈ chain,
        w (t.1, t.2.1) +
        w (t.1, t.2.2) +
        w (t.2.1, t.2.2) = 0 := by
    intro t ht
    exact hclosed t (hsubset t ht)

  have hzero :
      ((chain.flatMap triangleBoundaryEdges).map w).sum = 0 :=
    closed_cocycle_boundary_pairing_zero
      w chain hchainClosed

  have hequal :
      (cycle.map w).sum =
      ((chain.flatMap triangleBoundaryEdges).map w).sum :=
    edge_coefficients_determine_pairing
      cycle (chain.flatMap triangleBoundaryEdges) hcoeff w

  have hcontradiction : (1 : ZMod 2) = 0 := by
    calc
      (1 : ZMod 2) = (cycle.map w).sum := hodd.symm
      _ = ((chain.flatMap triangleBoundaryEdges).map w).sum :=
        hequal
      _ = 0 := hzero

  norm_num at hcontradiction

private theorem forall_mem_of_listForall
    {α : Type} {p : α → Prop} {xs : List α}
    (h : List.Forall p xs) :
    ∀ x ∈ xs, p x := by
  exact List.forall_iff_forall_mem.mp h

private def certifiedFaces : List Triangle12 := [
  (0, 1, 4),
  (0, 1, 6),
  (0, 1, 7),
  (0, 2, 3),
  (0, 2, 4),
  (0, 2, 6),
  (0, 2, 7),
  (0, 2, 8),
  (0, 2, 9),
  (0, 2, 10),
  (0, 2, 11),
  (0, 3, 5),
  (0, 3, 8),
  (0, 3, 9),
  (0, 4, 6),
  (0, 4, 7),
  (0, 4, 8),
  (0, 4, 9),
  (0, 5, 8),
  (0, 5, 9),
  (0, 6, 7),
  (0, 6, 8),
  (0, 6, 10),
  (0, 8, 9),
  (0, 8, 10),
  (0, 8, 11),
  (0, 10, 11),
  (1, 2, 5),
  (1, 2, 10),
  (1, 2, 11),
  (1, 3, 4),
  (1, 3, 5),
  (1, 3, 6),
  (1, 3, 7),
  (1, 3, 9),
  (1, 3, 10),
  (1, 3, 11),
  (1, 4, 6),
  (1, 4, 7),
  (1, 5, 6),
  (1, 5, 7),
  (1, 5, 9),
  (1, 5, 10),
  (1, 5, 11),
  (1, 6, 7),
  (1, 6, 9),
  (1, 7, 10),
  (1, 10, 11),
  (2, 3, 8),
  (2, 3, 9),
  (2, 4, 5),
  (2, 4, 6),
  (2, 4, 7),
  (2, 4, 8),
  (2, 4, 9),
  (2, 4, 10),
  (2, 4, 11),
  (2, 5, 10),
  (2, 5, 11),
  (2, 6, 7),
  (2, 6, 10),
  (2, 8, 9),
  (2, 8, 11),
  (2, 10, 11),
  (3, 4, 6),
  (3, 4, 7),
  (3, 5, 7),
  (3, 5, 8),
  (3, 5, 9),
  (3, 5, 10),
  (3, 5, 11),
  (3, 6, 7),
  (3, 6, 8),
  (3, 6, 9),
  (3, 7, 8),
  (3, 7, 9),
  (3, 7, 10),
  (3, 8, 9),
  (3, 10, 11),
  (4, 5, 10),
  (4, 5, 11),
  (4, 6, 7),
  (4, 6, 8),
  (4, 6, 10),
  (4, 6, 11),
  (4, 8, 9),
  (4, 8, 10),
  (4, 8, 11),
  (4, 10, 11),
  (5, 6, 7),
  (5, 6, 8),
  (5, 6, 9),
  (5, 7, 8),
  (5, 7, 9),
  (5, 7, 10),
  (5, 8, 9),
  (5, 10, 11),
  (6, 7, 8),
  (6, 7, 9),
  (6, 7, 11),
  (6, 8, 9),
  (6, 8, 10),
  (6, 8, 11),
  (6, 9, 10),
  (6, 9, 11),
  (6, 10, 11),
  (7, 8, 9),
  (7, 8, 11),
  (7, 9, 11),
  (8, 9, 10),
  (8, 9, 11),
  (8, 10, 11),
  (9, 10, 11)
]
private def certifiedCocycle : List Edge12 := [
  (1, 2),
  (1, 10),
  (1, 11),
  (2, 5),
  (3, 10),
  (3, 11),
  (4, 5),
  (5, 10),
  (5, 11),
  (7, 10)
]
private def detectingCycle : List Edge12 := [
  (0, 1),
  (0, 2),
  (1, 2)
]

private def edgeWeight (e : Edge12) : ZMod 2 :=
  if e ∈ certifiedCocycle then 1 else 0

private theorem certifiedFaces_closed :
    ∀ t ∈ certifiedFaces,
      edgeWeight (t.1, t.2.1) +
      edgeWeight (t.1, t.2.2) +
      edgeWeight (t.2.1, t.2.2) = 0 := by
  have hall :
      List.Forall
        (fun t : Triangle12 =>
          edgeWeight (t.1, t.2.1) +
          edgeWeight (t.1, t.2.2) +
          edgeWeight (t.2.1, t.2.2) = 0)
        certifiedFaces := by
    decide
  exact forall_mem_of_listForall hall

private theorem detectingCycle_odd :
    (detectingCycle.map edgeWeight).sum = 1 := by
  decide

/--
The explicit detecting cycle is nonboundary relative to the literal
finite list `certifiedFaces`. This statement alone does not identify that
list with the face set of the fixed 43-tetrahedron triangulation or prove
a global Pachner-descent or Poincare-recognition theorem.
-/
theorem fixedPrefix_detectingCycle_nonboundary :
    ¬ ∃ chain : List Triangle12,
      (∀ t ∈ chain, t ∈ certifiedFaces) ∧
      (∀ edge : Edge12,
        edgeCoefficient detectingCycle edge =
        edgeCoefficient
          (chain.flatMap triangleBoundaryEdges) edge) := by
  exact finite_nonboundary_of_mod2_edge_coefficients
    edgeWeight detectingCycle certifiedFaces
    certifiedFaces_closed detectingCycle_odd

#print axioms fixedPrefix_detectingCycle_nonboundary

end Fixed43ResourceBounds
end Poincare
