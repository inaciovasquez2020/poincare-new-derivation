namespace Poincare

abbrev Vertex := Nat

structure Edge where
  a : Vertex
  b : Vertex
deriving DecidableEq, Repr

structure Face where
  a : Vertex
  b : Vertex
  c : Vertex
deriving DecidableEq, Repr

structure Tetra where
  a : Vertex
  b : Vertex
  c : Vertex
  d : Vertex
deriving DecidableEq, Repr

def Tetra.vertices (t : Tetra) : Finset Vertex :=
  {t.a, t.b, t.c, t.d}

def Tetra.faces (t : Tetra) : Finset Face :=
  {
    ⟨t.a, t.b, t.c⟩,
    ⟨t.a, t.b, t.d⟩,
    ⟨t.a, t.c, t.d⟩,
    ⟨t.b, t.c, t.d⟩
  }

structure Triangulation where
  tetrahedra : Finset Tetra
deriving Repr

def Triangulation.vertices (K : Triangulation) : Finset Vertex :=
  K.tetrahedra.biUnion Tetra.vertices

def Triangulation.faces (K : Triangulation) : Finset Face :=
  K.tetrahedra.biUnion Tetra.faces

end Poincare
