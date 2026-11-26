# Counterexample to a universal extinction-time bound

Status: **Exact counterexample to a scale-independent strengthening of Perelman's theorem.** This does not contradict finite extinction for any fixed closed simply connected initial 3-manifold.

## False strengthening

The following claim is false:

> There is a single finite constant (C) such that every Ricci flow starting from every initial Riemannian metric on every closed simply connected 3-manifold becomes extinct by time (C).

## Counterexample on one fixed topology

Use the same manifold (M=S^3) for every input, with the round initial metrics
\[
g_R(0)=R^2g_{\mathrm{unit}},\qquad R>0.
\]
The exact Ricci flow is
\[
g_R(t)=(R^2-4t)g_{\mathrm{unit}},
\qquad 0\le t<R^2/4.
\]
It becomes extinct at
\[
T_R=R^2/4.
\]
Given any proposed universal bound (C<\infty), choose (R>2\sqrt C). Then
\[
T_R=R^2/4>C.
\]
Thus no such scale-independent (C) exists, even when the topology is held fixed as (S^3).

## Why this tests the actual method

Ricci flow has parabolic scaling: if (g(t)) is a solution, then
\[
\widetilde g(t)=\lambda g(t/\lambda)
\]
is also a solution, with time scaled by (\lambda>0\). Consequently the extinction time scales by the same factor. A theorem asserting finite extinction for each fixed input is compatible with arbitrarily large extinction times across rescaled initial metrics.

The explicit round solution is an exact witness to this scaling obstruction; no numerical approximation is required.

## Shadow-of-infinity limit

Taking (R_n\to\infty) and fixed basepoints gives
\[
(S^3,R_n^2g_{\mathrm{unit}},p_n)\longrightarrow
(\mathbb R^3,g_{\mathrm E},0)
\]
in pointed smooth convergence on bounded spatial and time regions. Each compact flow has finite extinction time (R_n^2/4), while the pointed limit is the stationary Euclidean flow for all (t\ge0).

## Logical boundary

Established:
- no universal extinction-time bound independent of initial scale;
- extinction times diverge in the explicit round family;
- the pointed limit is noncompact and stationary.

Not established:
- any failure of Perelman's finite-extinction theorem for an individual closed manifold;
- any failure of the surgery procedure under its actual hypotheses;
- a new Poincaré proof.

The right strengthened target is a **scale-covariant estimate**: the extinction bound should transform consistently under (g\mapsto\lambda g), rather than claim a universal absolute time.
