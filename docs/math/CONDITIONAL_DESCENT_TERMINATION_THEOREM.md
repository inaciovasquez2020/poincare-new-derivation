# Conditional Descent Termination Theorem

Status: CLOSED repository-scope conditional theorem.
Theorem ID: PND-CDT-1.

## Statement

Let `X` be a state space and let `h : X -> N` be a nonnegative integer height. Let `R` be an allowed transition relation on `X`.

Assume the descent condition:

```text
x R y  implies  h(y) < h(x).
```

Then every finite `R`-chain beginning at `x_0` has length at most `h(x_0)`. In particular, no infinite `R`-chain exists.

## Proof

For a chain `x_0 R x_1 R ... R x_n`, the descent condition gives

```text
h(x_0) > h(x_1) > ... > h(x_n) >= 0.
```

A strictly decreasing sequence of nonnegative integers beginning at `h(x_0)` has at most `h(x_0)` strict drops. Hence `n <= h(x_0)`. Therefore infinite descent is impossible.

## Repository interpretation

This closes the repository-scope descent-termination core:

```text
integer height + strict decrease per admissible move => termination.
```

## Non-claim boundary

This does not prove the Poincare conjecture.

This does not prove that every topological simplification move required by a full Poincare proof satisfies the descent condition.

This does not prove completeness of the proposed move system.

The remaining mathematical frontier is the admissibility theorem:

```text
every required geometric/topological reduction admits a move satisfying h(y) < h(x).
```
