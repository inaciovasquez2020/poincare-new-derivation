# Graver / Kernel Decomposition — Formal Version

## Assumptions

- Dual graph G* has bounded degree Δ.
- Fundamental cycle lifts γ(c_e) have bounded support:
  
  |supp(γ(c_e))| ≤ C

- Supports are R-separated:

  dist(supp(g_i), supp(g_j)) > 2R  for i ≠ j

- Quadrilateral locality:

  ∀τ, |supp(g_i) ∩ Q(τ)| ≤ 1

## Conformal decomposition

For any g ∈ ker(A):

  g = Σ_{i=1}^k g_i

with:

  g_i = γ(c_{e_i})

  sign(g_i(j)) = sign(g(j)) whenever g_i(j) ≠ 0

## Local admissibility

If x ∈ P_{χ=2}, then for each i:

  x + g_i ∈ P_{χ=2}

## Packing bound

Since supports are disjoint and bounded:

  k · C ≤ O(t)

⇒

  k = O(t)

## Potential function

Φ(x) = Σ_{j∈S} |x_j| + |{j : x_j ≠ 0}|

## Descent

If g ≠ 0 and sign-compatible:

  ∃ i such that:

    ∃ j ∈ supp(g_i) ∩ supp(x)
    |x_j + g_i(j)| < |x_j|

⇒

  Φ(x + g_i) < Φ(x)

## Consequence

- Existence of strictly decreasing sequence
- Termination in O(t) steps
- dim ker(A) = O(t)

