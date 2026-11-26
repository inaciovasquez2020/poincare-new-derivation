# Round-sphere shadow-of-infinity counterexample

Status: **Exact counterexample to a uniform-extinction / limit-commutation claim; not a counterexample to Perelman's theorem.**

## Claim being tested

The following tempting extension is false:

> If every closed simply connected 3-manifold in a sequence has a Ricci flow that becomes extinct in finite time, then a pointed smooth limit of those flows must also become extinct in finite time, with an extinction time bounded uniformly along the sequence.

The counterexample preserves the closed, simply connected topology at every finite stage. Infinity appears only in the pointed limit.

## Construction

Let (g_{\mathrm{unit}}) be the unit round metric on (S^3), and set
\[
(M_n,g_n(0),p_n)=(S^3,R_n^2g_{\mathrm{unit}},p_n),\qquad R_n\to\infty.
\]
The round Ricci flow is explicit:
\[
g_n(t)=(R_n^2-4t)g_{\mathrm{unit}},\qquad 0\le t<T_n,
\]
where
\[
T_n=R_n^2/4.
\]
Indeed, for the unit round 3-sphere, \(\operatorname{Ric}(g_{\mathrm{unit}})=2g_{\mathrm{unit}}\); constant rescaling leaves the Ricci tensor as a covariant 2-tensor unchanged, so
\[
\partial_tg_n=-4g_{\mathrm{unit}}=-2\operatorname{Ric}(g_n).
\]
Each \(M_n=S^3\) is compact and simply connected, and each round flow becomes extinct at its finite time \(T_n\). But \(T_n\to\infty\), so there is no uniform finite extinction-time bound across the sequence.

## The shadow limit

For every fixed finite time interval \([0,A]\), all sufficiently large \(n\) satisfy \(T_n>A\). The pointed metrics on that interval converge locally smoothly to
\[
(\mathbb R^3,g_{\mathrm E},0),
\]
the Euclidean metric, whose Ricci tensor is zero. The limiting Ricci flow is therefore
\[
g_\infty(t)=g_{\mathrm E}\qquad\text{for all }t\ge0.
\]
It exists for all time and never becomes extinct.

This is an explicit “shadow of infinity”: each finite-stage manifold is a closed simply connected sphere with finite extinction, while the pointed limit loses compactness and is a stationary noncompact flow.

## What this does and does not prove

**Proved by the construction:** finite extinction for each compact member does not imply a uniform extinction-time bound, and finite extinction does not pass to this pointed noncompact limit.

**Not disproved:** Perelman's finite-extinction theorem for each closed simply connected 3-manifold. Every member of the sequence obeys that theorem. The limit is not closed, so the original theorem's hypotheses fail in the limit.

**Not established:** a counterexample to any of Perelman's original claims, or a failure of the surgery construction under its stated hypotheses.

## Exact missing hypothesis for the false extension

A limit theorem would need an additional uniform estimate preventing \(T_n\to\infty\), or another hypothesis that rules out the loss of compactness. This example shows that such uniformity cannot follow from closedness and simple connectedness of each individual \(M_n\) alone.

## Reproducibility checks

1. Verify the round-flow equation by differentiating \((R_n^2-4t)g_{\mathrm{unit}}\).
2. Verify \(T_n=R_n^2/4\to\infty\).
3. Fix any \(A<\infty\); then \(T_n>A\) for all sufficiently large \(n\).
4. Take the pointed local limit on \([0,A]\); the radius tends to infinity and the curvature \(2/(R_n^2-4t)\) tends to zero.
5. Since \(\operatorname{Ric}(g_{\mathrm E})=0\), the limit is stationary and non-extinct.

This is an analytic counterexample to a specific overgeneralization, not a new proof of Poincaré and not a refutation of Perelman.
