# Uniform-on-bounded-time proof of the round-sphere shadow limit

This note supplies the local geometric convergence estimate behind
`ROUND_S3_SHADOW_OF_INFINITY_COUNTEREXAMPLE.md`. It does not assert that
Perelman's theorem fails.

## Sequence and flow

Fix basepoints (p_n\in S^3) and let (R_n\to\infty). Put
\[
g_n(0)=R_n^2g_{\mathrm{unit}},\qquad
g_n(t)=(R_n^2-4t)g_{\mathrm{unit}}.
\]
Write (\rho_n(t)=\sqrt{R_n^2-4t}), so (g_n(t)) is the round metric
of radius (\rho_n(t)) and becomes extinct at (T_n=R_n^2/4\).

Fix any finite (A>0). For all sufficiently large (n), (R_n^2>4A),
so the flow exists throughout (0\le t\le A).

## Explicit pointed local metric

In geodesic polar coordinates centered at (p_n), the round metric of
radius (\rho_n(t)), away from the polar cut locus, is
\[
g_n(t)=dr^2+\rho_n(t)^2
\sin^2\!\left(\frac r{\rho_n(t)}\right)g_{S^2}.
\]
The polar cut locus is at distance (\pi\rho_n(t)\). Since
\(\rho_n(t)\to\infty\) uniformly for (t\in[0,A]\), every fixed
ball (B(0,L)\subset\mathbb R^3\) lies inside this polar chart for all
sufficiently large (n), uniformly over the time interval.

For fixed (L,A<\infty), the coefficient has the representation
\[
\rho_n(t)^2\sin^2\!\left(\frac r{\rho_n(t)}\right)
=r^2\left(\frac{\sin(r/\rho_n(t))}{r/\rho_n(t)}\right)^2.
\]
The function (x\mapsto(\sin x/x)^2), extended smoothly at (x=0)
with value (1), converges to (1) in every derivative on compact
sets as its argument tends to zero. Also
\[
\sup_{0\le t\le A}\frac{L}{\rho_n(t)}
\le \frac{L}{\sqrt{R_n^2-4A}}\longrightarrow0.
\]
Consequently the polar metric coefficients converge in (C^\infty) on
each fixed bounded spatial region, uniformly on every bounded time
interval, to
\[
g_\infty(t)=dr^2+r^2g_{S^2}=g_{\mathrm E}.
\]
This is pointed smooth convergence on bounded time intervals to the
stationary Euclidean Ricci flow.

## Curvature and extinction estimates

The sectional curvature of the round sphere is
\[
K_n(t)=\frac1{R_n^2-4t}.
\]
Hence for each finite (A),
\[
\sup_{0\le t\le A}|K_n(t)|
=\frac1{R_n^2-4A}\longrightarrow0.
\]
Meanwhile (T_n=R_n^2/4\to\infty). Thus no common finite upper bound
for the extinction times exists, even though every member of the
sequence is a closed simply connected 3-sphere and each individual flow
has finite extinction.

The pointed limit is complete, noncompact, flat, and stationary. It
does not become extinct.

## Logical conclusion

This disproves the following limit-commutation assertion:

> Finite-time extinction of each closed simply connected member of a
> sequence implies finite-time extinction of its pointed smooth
> noncompact limit, with a uniform extinction-time bound.

The example does **not** disprove finite extinction for any individual
closed simply connected 3-manifold. The limit leaves the compact
hypothesis. No conclusion about Perelman's original theorem is reversed.

## Proof boundary

The displayed formula and the local (C^\infty) limit establish the
counterexample analytically. This is not a formalized Ricci-flow proof in
Lean. A Lean encoding would need definitions of the round metric, Ricci
flow solution, pointed smooth convergence, and extinction; the current
repository's combinatorial triangulation development does not by itself
formalize those analytic objects.
