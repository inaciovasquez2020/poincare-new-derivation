import Regge.Core

structure PachnerMove (M M' : SimplicialComplex) : Prop where
  localSupport : Finset (Edge M.V)

def IsRealizablePath (M M' : SimplicialComplex) : Prop := True
