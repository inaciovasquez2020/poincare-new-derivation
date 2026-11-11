import Poincare.PositionalStellarSpokeBlocker
import Poincare.PositionStellarFaceCount
import Mathlib.Tactic

namespace Poincare

/-- Exact local incidence of an edge between distinct old vertices in a
fresh stellar subdivision. No new tetrahedron contains an old edge outside
the selected tetrahedron; an old edge inside occurs twice in its four
stellar children. -/
theorem Move41Site.sourceTets_old_edge_count
    (s : Move41Site) (u v : Nat)
    (hu : u ≠ s.e) (hv : v ≠ s.e) (huv : u ≠ v) :
    (s.sourceTets.filter (fun τ =>
      decide (u ∈ τ.verts ∧ v ∈ τ.verts))).length =
      if u ∈ s.targetTet.verts ∧ v ∈ s.targetTet.verts then 2 else 0 := by
  have hd := s.distinct
  simp at hd
  by_cases hua : u = s.a
  all_goals by_cases hub : u = s.b
  all_goals by_cases huc : u = s.c
  all_goals by_cases hud : u = s.d
  all_goals by_cases hva : v = s.a
  all_goals by_cases hvb : v = s.b
  all_goals by_cases hvc : v = s.c
  all_goals by_cases hvd : v = s.d
  all_goals simp_all [Move41Site.sourceTets, Move41Site.targetTet,
    Move41Site.sourceTet₀, Move41Site.sourceTet₁,
    Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]

end Poincare
