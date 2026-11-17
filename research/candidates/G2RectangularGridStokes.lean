import Mathlib

/-!
# Universal rectangular mod-two grid Stokes identity

The summation statement has no geometric assumptions; the translation of
triangular cocycle relations into individual square relations and the precise
boundary trace of a carrier edge loop remain independent obligations.
-/

namespace Poincare.G2GridStokes

private theorem double_zero (a : ZMod 2) : a + a = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  calc
    a + a = (2 : ZMod 2) * a := by ring
    _ = 0 := by rw [htwo]; ring

/-- One-dimensional mod-two telescoping over arbitrary finite sequences. -/
private theorem sum_successor_pairs
    (f : Nat → ZMod 2) (n : Nat) :
    (∑ i ∈ Finset.range n, (f i + f (i + 1))) = f 0 + f n := by
  induction n with
  | zero =>
      simp [double_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      calc
        f 0 + f n + (f n + f (n + 1)) =
            (f 0 + f (n + 1)) + (f n + f n) := by abel
        _ = f 0 + f (n + 1) := by rw [double_zero]; simp

/-- If every elementary rectangle has zero mod-two edge sum, the
    perimeter of the entire grid has zero edge sum. -/
theorem rectangle_perimeter_zero
    (n m : Nat)
    (horizontal vertical : Nat → Nat → ZMod 2)
    (hsquare : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range m,
      horizontal i j + vertical (i + 1) j +
      horizontal i (j + 1) + vertical i j = 0) :
    (∑ i ∈ Finset.range n, horizontal i 0) +
    (∑ i ∈ Finset.range n, horizontal i m) +
    (∑ j ∈ Finset.range m, vertical 0 j) +
    (∑ j ∈ Finset.range m, vertical n j) = 0 := by
  let sq : Nat → Nat → ZMod 2 := fun i j =>
    (horizontal i j + horizontal i (j + 1)) +
    (vertical i j + vertical (i + 1) j)
  have hsq (i : Nat) (hi : i ∈ Finset.range n)
      (j : Nat) (hj : j ∈ Finset.range m) : sq i j = 0 := by
    change (horizontal i j + horizontal i (j + 1)) +
      (vertical i j + vertical (i + 1) j) = 0
    calc
      _ = horizontal i j + vertical (i + 1) j +
            horizontal i (j + 1) + vertical i j := by abel
      _ = 0 := hsquare i hi j hj
  have hzero : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, sq i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    exact hsq i hi j hj
  have hrow (i : Nat) :
      (∑ j ∈ Finset.range m, sq i j) =
      (horizontal i 0 + horizontal i m) +
      (∑ j ∈ Finset.range m,
        (vertical i j + vertical (i + 1) j)) := by
    calc
      _ = (∑ j ∈ Finset.range m,
             (horizontal i j + horizontal i (j + 1))) +
          (∑ j ∈ Finset.range m,
             (vertical i j + vertical (i + 1) j)) := by
          simp only [sq, Finset.sum_add_distrib]
      _ = _ := by rw [sum_successor_pairs]
  have hrectangle :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, sq i j) =
      (∑ i ∈ Finset.range n, (horizontal i 0 + horizontal i m)) +
      (∑ j ∈ Finset.range m, (vertical 0 j + vertical n j)) := by
    calc
      _ = ∑ i ∈ Finset.range n,
        ((horizontal i 0 + horizontal i m) +
          ∑ j ∈ Finset.range m,
            (vertical i j + vertical (i + 1) j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hrow i
      _ = (∑ i ∈ Finset.range n, (horizontal i 0 + horizontal i m)) +
          (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
             (vertical i j + vertical (i + 1) j)) := by
          rw [Finset.sum_add_distrib]
      _ = _ := by
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          exact sum_successor_pairs (fun i => vertical i j) n
  rw [hrectangle] at hzero
  simpa only [Finset.sum_add_distrib, add_assoc] using hzero


/-- Four vertices lying in a common represented tetrahedron have zero
    quadrilateral edge-cocycle sum. The two triangular relations correspond to
    the triangles (a,b,c) and (a,c,d) in that tetrahedron. -/
theorem tetrahedron_quad_parity_zero
    {Vertex Tet : Type*}
    (incident : Vertex → Tet → Prop)
    (w : Vertex → Vertex → ZMod 2)
    (hsym : ∀ u v, w u v = w v u)
    (htri : ∀ t a b c, incident a t → incident b t →
      incident c t → w a b + w b c + w c a = 0)
    (t : Tet) (a b c d : Vertex)
    (ha : incident a t) (hb : incident b t)
    (hc : incident c t) (hd : incident d t) :
    w a b + w b c + w c d + w d a = 0 := by
  have h₁ := htri t a b c ha hb hc
  have h₂ := htri t a c d ha hc hd
  rw [hsym c a] at h₁
  linear_combination h₁ + h₂

/-- An actual common-tetrahedron witness supplies the local square relation.
    The exterior rectangular cancellation is already rectangle_perimeter_zero.
    Geometric boundary matching is not assumed here. -/
theorem quad_parity_zero_of_common_tetrahedron
    {Vertex Tet : Type*}
    (incident : Vertex → Tet → Prop)
    (w : Vertex → Vertex → ZMod 2)
    (hsym : ∀ u v, w u v = w v u)
    (htri : ∀ t a b c, incident a t → incident b t →
      incident c t → w a b + w b c + w c a = 0)
    (a b c d : Vertex)
    (hcommon : ∃ t : Tet, incident a t ∧ incident b t ∧
      incident c t ∧ incident d t) :
    w a b + w b c + w c d + w d a = 0 := by
  obtain ⟨t, ha, hb, hc, hd⟩ := hcommon
  exact tetrahedron_quad_parity_zero incident w hsym htri t
    a b c d ha hb hc hd

#print axioms rectangle_perimeter_zero
#print axioms tetrahedron_quad_parity_zero
#print axioms quad_parity_zero_of_common_tetrahedron

end Poincare.G2GridStokes
