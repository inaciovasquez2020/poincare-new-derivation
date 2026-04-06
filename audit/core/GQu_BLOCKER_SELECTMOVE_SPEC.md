# GQu blocker: exact missing constructive object

## Closed non-new-math lemma

theorem vertexDefect_pos_implies_Phi_pos
  (T : Triangulation) (v : Nat)
  (hv : v ∈ allVerts T)
  (hpos : vertexDefect T v > 0) :
  Phi T > 0

## Frontier new-proof obligation

theorem selectMoveImplGreedy_spec
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K

## Exact blocking sublemmas

theorem positive_vertexDefect_exists
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ v ∈ allVerts K, vertexDefect K v > 0

theorem positive_vertexDefect_yields_flippable_edge
  (K : Triangulation)
  {v : Nat}
  (hv : v ∈ allVerts K)
  (hdef : vertexDefect K v > 0) :
  ∃ e : Edge, Flippable K e

theorem flippable_edge_gives_strict_drop
  (K : Triangulation)
  {e : Edge}
  (hflip : Flippable K e) :
  let m := PachnerMove.ofEdge e
  in Phi (applyMoveImpl K m) < Phi K
