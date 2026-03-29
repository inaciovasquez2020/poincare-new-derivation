namespace Poincare

abbrev Vertex := Nat

structure Tet where
  v0 v1 v2 v3 : Vertex

structure Triangulation where
  tets : List Tet

def Tet.verts (τ : Tet) : List Vertex :=
  [τ.v0, τ.v1, τ.v2, τ.v3]

def allVerts (K : Triangulation) : List Vertex :=
  K.tets.flatMap Tet.verts

def vertexDegree (K : Triangulation) (v : Vertex) : Nat :=
  (allVerts K).count v

def targetDegree : Nat := 4

def vertexDefect (K : Triangulation) (v : Vertex) : Int :=
  (vertexDegree K v : Int) - (targetDegree : Int)

def Phi (K : Triangulation) : Nat :=
  (allVerts K).foldl (fun acc v => acc + (vertexDefect K v).natAbs) 0

def normalized (K : Triangulation) : Prop := Phi K = 0

def S3 (K : Triangulation) : Prop := normalized K

end Poincare
