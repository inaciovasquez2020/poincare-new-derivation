import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import TwoLift
import TwoLift.connectivity

open TwoLift

namespace TwoLift

variable {N : ℕ} [Fintype (Fin N)] [Fact (2 ≤ N)]

theorem I_G₁_ne_I_G₂ :
  I (G₁ (N := N)) ≠ I (G₂ (N := N)) := by
  intro h
  have h1 : Fintype.card (G₁ (N := N)).ConnectedComponent = 2 := G₁_two_components
  have h2 : Fintype.card (G₂ (N := N)).ConnectedComponent = 1 := G₂_connected
  have : (2 : ZMod 2) = 1 := by
    simpa [I, rankGraph, h1, h2] using h
  decide

end TwoLift
