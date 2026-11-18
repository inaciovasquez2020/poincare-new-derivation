import Mathlib
import Poincare.GlobalMove32ReentryDyadicGridVertices
import Poincare.G2GridStokes

/-!
# Actual carrier grid: mod-two Stokes from positive coordinate labels

The common-tetrahedron hypothesis at four grid cells sharing each
grid corner is proved in GlobalMove32ReentryDyadicGridVertices.
This module connects that geometric source to the previously verified
mod-two rectangular Stokes theorem.

The perimeter-to-original-edge-walk identification remains open.
-/

namespace Poincare

open Poincare.G2GridStokes

/-- A cocycle evaluated on adjacent positive-coordinate grid-cell labels has
zero total grid perimeter, whenever each elementary dual-grid quadrilateral
is assigned a common represented tetrahedron. The actual carrier grid
supplies precisely this hypothesis via the common-point lemma. -/
theorem carrier_grid_cocycle_perimeter_zero_of_common_tet
    {K : Triangulation}
    (w : Nat → Nat → ZMod 2)
    (hsym : ∀ u v, w u v = w v u)
    (htri : ∀ tau : Tet, ∀ a b c : Nat,
      a ∈ tau.verts → b ∈ tau.verts → c ∈ tau.verts →
      w a b + w b c + w c a = 0)
    (n : Nat)
    (label : Nat → Nat → Nat)
    (hcommon : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      ∃ tau : Tet, tau ∈ K.tets ∧
        label i j ∈ tau.verts ∧
        label (i + 1) j ∈ tau.verts ∧
        label (i + 1) (j + 1) ∈ tau.verts ∧
        label i (j + 1) ∈ tau.verts) :
    (∑ i ∈ Finset.range n, w (label i 0) (label (i+1) 0)) +
    (∑ i ∈ Finset.range n, w (label i n) (label (i+1) n)) +
    (∑ j ∈ Finset.range n, w (label 0 j) (label 0 (j+1))) +
    (∑ j ∈ Finset.range n, w (label n j) (label n (j+1))) = 0 := by
  apply rectangle_perimeter_zero n n
    (fun i j => w (label i j) (label (i+1) j))
    (fun i j => w (label i j) (label i (j+1)))
  intro i hi j hj
  obtain ⟨tau, _, ha, hb, hc, hd⟩ := hcommon i hi j hj
  exact tetrahedron_quad_parity_zero
    (fun v tau => v ∈ tau.verts) w hsym htri tau
    (label i j) (label (i+1) j)
    (label (i+1) (j+1)) (label i (j+1))
    ha hb hc hd

#print axioms carrier_grid_cocycle_perimeter_zero_of_common_tet

end Poincare
