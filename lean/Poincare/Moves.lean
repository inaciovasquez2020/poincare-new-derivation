import Poincare.Triangulation

namespace Poincare

inductive PachnerMove where
| move23
| move32
| move14
| move41


structure Move23Site where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  distinct :
    [a, b, c, d, e].Nodup

def Move23Site.leftTet (s : Move23Site) : Tet :=
  ⟨s.a, s.b, s.c, s.d⟩

def Move23Site.rightTet (s : Move23Site) : Tet :=
  ⟨s.a, s.b, s.c, s.e⟩

def Move23Site.newTet₀ (s : Move23Site) : Tet :=
  ⟨s.a, s.b, s.d, s.e⟩

def Move23Site.newTet₁ (s : Move23Site) : Tet :=
  ⟨s.a, s.c, s.d, s.e⟩

def Move23Site.newTet₂ (s : Move23Site) : Tet :=
  ⟨s.b, s.c, s.d, s.e⟩


def SameTetVertices (τ σ : Tet) : Prop :=
  ∀ v : Nat, v ∈ τ.verts ↔ v ∈ σ.verts

def Move23Site.RealizedIn (s : Move23Site) (K : Triangulation) : Prop :=
  (∃ τ ∈ K.tets, SameTetVertices τ s.leftTet) ∧
  (∃ τ ∈ K.tets, SameTetVertices τ s.rightTet)

def applyMove (T : Triangulation) (_ : PachnerMove) : Triangulation := T
def selectMove (_T : Triangulation) : PachnerMove := PachnerMove.move23

end Poincare
