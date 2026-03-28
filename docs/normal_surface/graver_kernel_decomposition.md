# Graver / Kernel Decomposition Layer

## Local cycle decomposition

For the matching matrix A of a triangulation with t tetrahedra:

Every kernel vector g ∈ ker(A) admits a decomposition

  g = Σ_{e ∈ E(G*)} λ_e γ(c_e)

with λ_e ∈ ℤ and each γ(c_e) supported on a bounded-radius neighborhood.

## Bounded support

There exists C = O(1) such that

  ∀e, |supp(γ(c_e))| ≤ C

## Sign-compatible decomposition

For any admissible x ∈ P_{χ=2}:

  g = Σ_i g_i  (sign-compatible)

such that each g_i = γ(c_{e_i}) and

  x + g_i ∈ P_{χ=2}

## Φ-descent

For non-minimal x:

  ∃e such that
  x' = x - sgn(x_j) γ(c_e)

satisfies

  Φ(x') < Φ(x)

## Rank bound

There exists E' ⊆ E(G*) with |E'| = Ω(t) such that

  {γ(c_e)}_{e∈E'} are linearly independent

⇒ rank(A) ≥ c·t

## Consequence

dim ker(A) = O(t)

