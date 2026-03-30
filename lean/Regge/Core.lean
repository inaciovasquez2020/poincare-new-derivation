import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

universe u

abbrev Edge (V : Type u) := V × V
abbrev Tet  (V : Type u) := V × V × V × V

variable {V : Type u} [DecidableEq V]

def tEdges (t : Tet V) : Finset (Edge V) :=
  let ⟨a,b,c,d⟩ := t
  Finset.fromList [
    (a,b),(a,c),(a,d),
    (b,c),(b,d),(c,d)
  ]

structure SimplicialComplex where
  V : Type u
  [decV : DecidableEq V]
  E : Finset (Edge V)
  T : Finset (Tet V)
  length : Edge V → ℝ
  dihedralAngle : Edge V → Tet V → ℝ
  Faces : Set (List V)

attribute [instance] SimplicialComplex.decV

def incidentTets (M : SimplicialComplex) (e : Edge M.V) : Finset (Tet M.V) :=
  M.T.filter (fun t => e ∈ tEdges t)

def total_angle (M : SimplicialComplex) (e : Edge M.V) : ℝ :=
  ∑ t in incidentTets M e, M.dihedralAngle e t

def regge_action (M : SimplicialComplex) : ℝ :=
  ∑ e in M.E, M.length e * (2 * Real.pi - total_angle M e)
