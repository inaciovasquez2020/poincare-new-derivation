import Poincare.Move32DegreeSupportBalance
import Poincare.VertexLinkConnectednessCounterexample

namespace Poincare

def crossPolytopeBoundary4 : Triangulation :=
  { tets :=
      [⟨0, 2, 4, 6⟩, ⟨0, 2, 4, 7⟩, ⟨0, 2, 5, 6⟩, ⟨0, 2, 5, 7⟩,
       ⟨0, 3, 4, 6⟩, ⟨0, 3, 4, 7⟩, ⟨0, 3, 5, 6⟩, ⟨0, 3, 5, 7⟩,
       ⟨1, 2, 4, 6⟩, ⟨1, 2, 4, 7⟩, ⟨1, 2, 5, 6⟩, ⟨1, 2, 5, 7⟩,
       ⟨1, 3, 4, 6⟩, ⟨1, 3, 4, 7⟩, ⟨1, 3, 5, 6⟩, ⟨1, 3, 5, 7⟩] }

theorem crossPolytopeBoundary4_closedCore :
    ClosedTriangulationCore crossPolytopeBoundary4 := by
  constructor
  · intro τ hτ
    simp [crossPolytopeBoundary4] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  constructor
  · decide
  · intro a b c habc hrepresented
    rcases hrepresented with ⟨τ, hτ, ha, hb, hc⟩
    simp [crossPolytopeBoundary4] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Tet.verts] at ha hb hc <;>
      rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      norm_num at habc <;> decide

theorem crossPolytopeBoundary4_vertexSupport :
    vertexSupport crossPolytopeBoundary4 = [0, 2, 4, 6, 7, 5, 3, 1] := by
  rfl

theorem crossPolytopeBoundary4_vertexDegree (v : Nat) (hv : v < 8) :
    vertexDegree crossPolytopeBoundary4 v = 8 := by
  interval_cases v <;> native_decide

theorem crossPolytopeBoundary4_PhiSupport : PhiSupport crossPolytopeBoundary4 = 32 := by
  native_decide

theorem crossPolytopeBoundary4_PhiSupport_pos : 0 < PhiSupport crossPolytopeBoundary4 := by
  decide

theorem crossPolytopeBoundary4_edgeIncidence_ne_three (d e : Nat) :
    (crossPolytopeBoundary4.tets.filter
      (fun τ => d ∈ τ.verts ∧ e ∈ τ.verts)).length ≠ 3 := by
  by_cases hd : d < 8
  · by_cases he : e < 8
    · interval_cases d <;> interval_cases e <;> decide
    · have he' : 8 ≤ e := by omega
      have he0 : e ≠ 0 := by omega
      have he1 : e ≠ 1 := by omega
      have he2 : e ≠ 2 := by omega
      have he3 : e ≠ 3 := by omega
      have he4 : e ≠ 4 := by omega
      have he5 : e ≠ 5 := by omega
      have he6 : e ≠ 6 := by omega
      have he7 : e ≠ 7 := by omega
      simp [crossPolytopeBoundary4, Tet.verts, he0, he1, he2, he3, he4, he5, he6, he7]
  · have hd' : 8 ≤ d := by omega
    have hd0 : d ≠ 0 := by omega
    have hd1 : d ≠ 1 := by omega
    have hd2 : d ≠ 2 := by omega
    have hd3 : d ≠ 3 := by omega
    have hd4 : d ≠ 4 := by omega
    have hd5 : d ≠ 5 := by omega
    have hd6 : d ≠ 6 := by omega
    have hd7 : d ≠ 7 := by omega
    simp [crossPolytopeBoundary4, Tet.verts, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7]

theorem crossPolytopeBoundary4_no_legal_move32 :
    ¬ ∃ s : Move32Site, s.LegalIn crossPolytopeBoundary4 := by
  rintro ⟨s, _hrealized, hthree, _habsent⟩
  exact crossPolytopeBoundary4_edgeIncidence_ne_three s.d s.e hthree

theorem crossPolytopeBoundary4_no_strict_move32 :
    ¬ ∃ s : Move32Site, s.LegalIn crossPolytopeBoundary4 ∧
      PhiSupport (s.replace crossPolytopeBoundary4) < PhiSupport crossPolytopeBoundary4 := by
  rintro ⟨s, hs, _⟩
  exact crossPolytopeBoundary4_no_legal_move32 ⟨s, hs⟩

end Poincare
