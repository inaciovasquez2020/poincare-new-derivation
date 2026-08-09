namespace Poincare

structure Tet where
  v0 : Nat
  v1 : Nat
  v2 : Nat
  v3 : Nat

structure Triangulation where
  tets : List Tet

def Tet.verts (τ : Tet) : List Nat :=
  [τ.v0, τ.v1, τ.v2, τ.v3]

def allVerts (K : Triangulation) : List Nat :=
  K.tets.flatMap Tet.verts

def vertexSupport (K : Triangulation) : List Nat :=
  (allVerts K).eraseDups

theorem mem_vertexSupport_iff (K : Triangulation) (v : Nat) :
    v ∈ vertexSupport K ↔ v ∈ allVerts K := by
  simp [vertexSupport]

def vertexDegree (K : Triangulation) (v : Nat) : Nat :=
  (allVerts K).count v

def targetDegree : Nat := 4

def vertexDefect (K : Triangulation) (v : Nat) : Nat :=
  Int.natAbs ((vertexDegree K v : Int) - (targetDegree : Int))

def Phi (K : Triangulation) : Nat :=
  (allVerts K).foldl (fun acc v => acc + vertexDefect K v) 0

def normalized (K : Triangulation) : Prop :=
  Phi K = 0

def S3 (K : Triangulation) : Prop :=
  normalized K

end Poincare
