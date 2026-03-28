# Coefficients, Independence, and Φ-Descent

## Arc-to-coordinate coefficients

For each tetrahedron τ and edge e:

a_{e,i} =
  1 if triangle t_{τ,i} intersects edge e,
  0 otherwise.

b_{e,q} =
  1 if quadrilateral q intersects edge e,
  0 otherwise.

## Edge-disjoint supports

There exists E' ⊆ E(G*) with |E'| = Ω(t) such that:

  supp(γ(c_e)) ∩ supp(γ(c_{e'})) = ∅  for e ≠ e'.

## Linear independence

If

  Σ_{e ∈ E'} λ_e γ(c_e) = 0,

then

  ∀e, λ_e = 0.

## Φ-descent certificate

Φ(x) = ||x||₁ + |supp(x)|

There exists e such that:

  Φ(x - sgn(x_j) γ(c_e)) < Φ(x)

## Lean skeleton

