import Mathlib.Combinatorics.SimpleGraph.Subgraph
import TwoLift

open TwoLift

namespace TwoLift

variable {N R : ℕ} [Fact (2 ≤ N)]

def ballSubgraph (G : SimpleGraph ((Fin N) × Fin 2)) (v : (Fin N) × Fin 2) : SimpleGraph ((Fin N) × Fin 2) := G

theorem G₁_G₂_local_ball_iso :
  ∀ v : (Fin N) × Fin 2, Nonempty (RootedIso
    { α := ((Fin N) × Fin 2), G := ballSubgraph (G₁ (N := N)) v, root := v }
    { α := ((Fin N) × Fin 2), G := ballSubgraph (G₂ (N := N)) v, root := v }) := by
  intro v
  sorry

end TwoLift
