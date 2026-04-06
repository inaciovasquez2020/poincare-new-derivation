# GQu blocker: exact missing constructive object

## Closed non-new-math lemma

```lean
theorem vertexDefect_pos_implies_Phi_pos
  (T : Triangulation) (v : Nat)
  (hv : v ∈ allVerts T)
  (hpos : vertexDefect T v > 0) :
  Phi T > 0
````

Proof target:

* unfold `Phi`
* use fold/sum decomposition over `allVerts T`
* use nonnegativity of all summands
* isolate the positive summand at `v`

## Frontier new-proof obligation

```lean
theorem selectMoveImplGreedy_spec
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K
```

This reduces to the constructive existence theorem

```lean
theorem exists_strict_descent_move
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ m : PachnerMove, Phi (applyMoveImpl K m) < Phi K
```

plus selector correctness

```lean
theorem selectMoveImplGreedy_returns_descent
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  let m := selectMoveImplGreedy K
  in Phi (applyMoveImpl K m) < Phi K
```

## Exact blocking sublemmas

```lean
theorem positive_vertexDefect_exists
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ v ∈ allVerts K, vertexDefect K v > 0
```

```lean
theorem positive_vertexDefect_yields_flippable_edge
  (K : Triangulation)
  {v : Nat}
  (hv : v ∈ allVerts K)
  (hdef : vertexDefect K v > 0) :
  ∃ e : Edge, Flippable K e
```

```lean
theorem flippable_edge_gives_strict_drop
  (K : Triangulation)
  {e : Edge}
  (hflip : Flippable K e) :
  let m := PachnerMove.ofEdge e
  in Phi (applyMoveImpl K m) < Phi K
```

## Repository normalization

Delete one duplicate declaration of
`vertexDefect_pos_implies_Phi_pos`
and import the surviving source everywhere.
