# Termination Theorem for Φ-Descent

## Well-foundedness

Let S be a finite support set. Define:

  Φ(x) = Σ_{j∈S} |x_j| + |{j ∈ S : x_j ≠ 0}|

Then:

  Φ(x) ∈ ℕ and Φ(x) ≥ 0

⇒ No infinite strictly decreasing sequence exists.

## Termination bound

If

  Φ(x_{k+1}) < Φ(x_k)

then

  Φ(x_k) ≤ Φ(x_0) - k

⇒

  k ≤ Φ(x_0)

## Φ-minimal ⇔ Graver-optimal

x is Φ-minimal iff:

  ∀ g ∈ ker(A), sign-compatible,
  Φ(x + g) ≥ Φ(x)

## Finite terminal class

Since S is finite:

  |{x : Φ(x) ≤ Φ(x_0)}| < ∞

## Consequence

- Descent terminates in O(t) steps
- Terminal configurations are finite
- Kernel reduction is complete

