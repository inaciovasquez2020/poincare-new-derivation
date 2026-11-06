import Mathlib.Tactic

namespace Poincare

private def fixedForcedTets : List (List Nat) := [
  [0, 1, 4, 6],
  [0, 1, 4, 7],
  [0, 1, 6, 7],
  [0, 2, 3, 6],
  [0, 2, 3, 8],
  [0, 2, 7, 8],
  [0, 4, 6, 8],
  [0, 5, 6, 8],
  [1, 2, 7, 8],
  [2, 3, 6, 8],
  [2, 4, 5, 7],
  [2, 4, 5, 8],
  [2, 4, 6, 7],
  [3, 4, 6, 7],
  [4, 5, 7, 8]
]

private def fixedLinkEdge (a b : Nat) : Bool :=
  fixedForcedTets.any
    (fun t => t.contains 6 && t.contains a && t.contains b)

theorem fixedPattern_forces_K33_link :
    ∀ a ∈ ([0, 7, 8] : List Nat),
      ∀ b ∈ ([2, 3, 4] : List Nat),
        fixedLinkEdge a b = true := by
  intro a ha b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl
  all_goals rcases hb with rfl | rfl | rfl
  all_goals decide


/--
The Euler equation and bipartite-face incidence inequality
for a spherical embedding of K3,3 are incompatible.

This arithmetic result does not establish the existence of
a spherical embedding or derive the face equations.
-/
theorem fixedPattern_K33_spherical_face_count_impossible
    (F : Nat)
    (hEuler : 6 + F = 9 + 2)
    (hFaceIncidence : 4 * F ≤ 2 * 9) :
    False := by
  omega

end Poincare
