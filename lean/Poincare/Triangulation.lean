namespace Poincare

abbrev Vertex := Nat
abbrev Tet := Vertex × Vertex × Vertex × Vertex

structure Triangulation where
  tets : List Tet

def vertices (K : Triangulation) : List Vertex :=
  K.tets.bind (fun ⟨a,b,c,d⟩ => [a,b,c,d])

def vertexDegree (K : Triangulation) (v : Vertex) : Nat :=
  (vertices K).count v

def targetDegree : Nat := 4

def vertexDefect (K : Triangulation) (v : Vertex) : Nat :=
  Nat.abs (vertexDegree K v - targetDegree)

def Phi : Triangulation → Nat
| ⟨tets⟩ =>
  (tets.bind (fun ⟨a,b,c,d⟩ => [a,b,c,d])).foldl
    (fun acc v => acc + Nat.abs (((tets.bind (fun ⟨a,b,c,d⟩ => [a,b,c,d])).count v) - targetDegree))
    0

def normalized (K : Triangulation) : Prop :=
  Phi K = 0

def S3 (K : Triangulation) : Prop :=
  normalized K

end Poincare
