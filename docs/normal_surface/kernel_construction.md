# Normal Surface Matching Matrix and Kernel Lift Construction

## Tetrahedron labeling and quadrilateral indices

For each tetrahedron τ:
V(τ) = {0,1,2,3}

Quadrilateral types:
Q(τ) = {
  q_{01|23},
  q_{02|13},
  q_{03|12}
}

## Face-gluing maps

For each glued face f = (τ,i) ~ (τ',j):
π_f : {0,1,2,3} \ {i} → {0,1,2,3} \ {j} is a bijection.

## Coordinate space

x ∈ ℤ^{7t}:

x = (t_{τ,0}, t_{τ,1}, t_{τ,2}, t_{τ,3},
     q_{τ,01|23}, q_{τ,02|13}, q_{τ,03|12}) over all τ.

## Matching matrix A

For each glued face f and each edge e ⊂ f:

Σ_{τ ⊃ f} sgn(τ,f) · x_{τ,e} = 0

where x_{τ,e} is the number of normal arcs intersecting edge e.

## Lift map γ

For a dual cycle c:

γ(c) = Σ_{f ∈ c} sgn(f,c) · δ_f

where δ_f is the elementary kernel vector induced by face traversal via π_f.

## Bounded-degree assumption

deg(G*) ≤ Δ = O(1)

## Admissibility predicate

P_{χ=2} = {
  x ∈ ℤ_{≥0}^{7t} :
  A x = 0,
  ∀τ, at most one quadrilateral type is nonzero,
  χ(x) = 2
}

## Euler characteristic

χ(x) =
  Σ_{τ} Σ_i t_{τ,i}
  − Σ_{faces} (# arcs)
  + Σ_{edges} (# intersections)

