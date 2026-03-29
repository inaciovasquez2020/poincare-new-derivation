import Poincare.Triangulation

namespace Poincare

inductive PachnerMove where
| move23
| move32
| move14
| move41
deriving DecidableEq, Repr

def baseTet (a b c d : Vertex) : Tet
| ⟨0, _⟩ => a
| ⟨1, _⟩ => b
| ⟨2, _⟩ => c
| ⟨3, _⟩ => d

def splitTetAtFresh (K : Triangulation) (τ : Tet) : Finset Tet :=
  let w := freshVertex K.tets
  { baseTet (τ 0) (τ 1) (τ 2) w,
    baseTet (τ 0) (τ 1) (τ 3) w,
    baseTet (τ 0) (τ 2) (τ 3) w,
    baseTet (τ 1) (τ 2) (τ 3) w }

def contractTetAtFresh (_K : Triangulation) (τ : Tet) : Finset Tet :=
  { baseTet (τ 0) (τ 1) (τ 2) (τ 3) }

def chooseTet? (K : Triangulation) : Option Tet :=
  K.tets.max? (fun τ => tetVerts τ |>.sup fun v => vertexDegree K v)

def applyMoveOnTet (K : Triangulation) (m : PachnerMove) (τ : Tet) : Triangulation :=
  match m with
  | PachnerMove.move14 =>
      ⟨(K.tets.erase τ) ∪ splitTetAtFresh K τ⟩
  | PachnerMove.move41 =>
      ⟨(K.tets.erase τ) ∪ contractTetAtFresh K τ⟩
  | PachnerMove.move23 =>
      ⟨K.tets.erase τ⟩
  | PachnerMove.move32 =>
      ⟨K.tets.erase τ⟩

def applyMove (K : Triangulation) (m : PachnerMove) : Triangulation :=
  match chooseTet? K with
  | some τ => applyMoveOnTet K m τ
  | none => K

def defectPivotVertex? (K : Triangulation) : Option Vertex :=
  K.vertices.max? fun v => vertexDefect K v

def selectMove (K : Triangulation) : PachnerMove :=
  match defectPivotVertex? K with
  | none => PachnerMove.move23
  | some v =>
      if h : vertexDegree K v > targetDegree then PachnerMove.move32
      else if h' : vertexDegree K v < targetDegree then PachnerMove.move14
      else PachnerMove.move23

end Poincare
