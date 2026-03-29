import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic

namespace Poincare

abbrev Vertex := Nat
abbrev Tet := Fin 4 → Vertex

instance : DecidableEq Tet := inferInstance

def tetVerts (τ : Tet) : Finset Vertex :=
  Finset.univ.image τ

structure Triangulation where
  tets : Finset Tet

def vertices (K : Triangulation) : Finset Vertex :=
  K.tets.biUnion tetVerts

def vertexDegree (K : Triangulation) (v : Vertex) : Nat :=
  (K.tets.filter fun τ => v ∈ tetVerts τ).card

def targetDegree : Nat := 4

def vertexDefect (K : Triangulation) (v : Vertex) : Nat :=
  Int.natAbs ((vertexDegree K v : Int) - targetDegree)

def Phi (K : Triangulation) : Nat :=
  (vertices K).fold (fun acc v => acc + vertexDefect K v) 0

def normalized (K : Triangulation) : Prop :=
  Phi K = 0

def S3 (K : Triangulation) : Prop :=
  normalized K

end Poincare
