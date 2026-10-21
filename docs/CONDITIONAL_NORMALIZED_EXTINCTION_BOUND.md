# Conditional normalized extinction bound

**Status:** conditional consequence of the published width inequality; not a new Ricci-flow theorem and not a proof of the Poincaré conjecture.

## 1. Starting estimate

In the closed orientable prime non-aspherical 3-manifold setting where the Colding–Minicozzi width estimate applies, let the nonnegative sweepout width satisfy

\[
D^+W(t)\le -4\pi+\frac{3}{4(t+C)}W(t),\qquad C>0.
\]

Here \(C\) depends on initial geometric data. This note assumes the cited width estimate and its hypotheses, including the applicable treatment of surgery, rather than reproving them.

Multiplication by \((t+C)^{-3/4}\) and integration gives

\[
\frac{W(T)}{(T+C)^{3/4}}
\le \frac{W(0)}{C^{3/4}}
-16\pi\big((T+C)^{1/4}-C^{1/4}\big).
\]

Because \(W(T)\ge0\), the right side cannot be negative while the estimate and flow remain applicable. Therefore the corresponding extinction-time upper bound is

\[
T_{\rm ext}\le
\left(C^{1/4}+\frac{W(0)}{16\pi C^{3/4}}\right)^4-C.
\]

This is an upper bound, not an equality for the actual extinction time.

## 2. A uniform bound under explicit input controls

Assume, in addition, that a family of initial data has common constants

\[
0<C_{\min}\le C\le C_{\max}<\infty,
\qquad 0\le W(0)\le W_*<\infty.
\]

Then

\[
\boxed{
T_{\rm ext}\le
\left(C_{\max}^{1/4}
+\frac{W_*}{16\pi C_{\min}^{3/4}}\right)^4-C_{\min}.
}
\]

Indeed, the positive expression inside the fourth power is bounded above by the expression using \(C_{\max}\) and \(C_{\min}\); also \(-C\le-C_{\min}\). The bound is useful only when the hypotheses genuinely provide these common constants. If the displayed right side is negative due to incompatible/overly loose assumptions, that signals that the assumed bounds and the starting estimate cannot all describe a nontrivial admissible flow.

## 3. Scaling audit

Under parabolic rescaling \(g\mapsto\lambda g\), \(\lambda>0\), lengths scale by \(\lambda^{1/2}\), sweepout width scales by \(W\mapsto\lambda W\), the time-offset parameter scales by \(C\mapsto\lambda C\), and time scales by \(T\mapsto\lambda T\). The extinction expression scales accordingly:

\[
\left((\lambda C)^{1/4}
+\frac{\lambda W(0)}{16\pi(\lambda C)^{3/4}}\right)^4-\lambda C
=\lambda\left[
\left(C^{1/4}+\frac{W(0)}{16\pi C^{3/4}}\right)^4-C
\right].
\]

Thus the estimate is scale-covariant. It is not an absolute time bound independent of the initial scale.

## 4. What this does and does not establish

- **Established conditionally:** uniform controls on both \(C\) and \(W(0)\) imply an explicit uniform extinction-time bound via the width inequality.
- **Not established:** a diameter-only bound for \(C\) or \(W(0)\), or a universal extinction-time bound for arbitrary initial metrics.
- **Not established:** a new proof of finite extinction, the Poincaré conjecture, or a Lean formalization of this calculation.
- **Relevant stress test:** round 3-spheres of radius \(R\) have extinction time \(R^2/4\); as \(R\to\infty\), the extinction times diverge while pointed bounded-region limits become stationary Euclidean flow. This rules out confusing pointwise finite extinction with a uniform bound across unnormalized scales.

## References

- Tobias H. Colding and William P. Minicozzi II, “Estimates for the extinction time for the Ricci flow on certain 3-manifolds and a question of Perelman,” *Journal of the American Mathematical Society* 18 (2005), 561–569. DOI: 10.1090/S0894-0347-05-00486-8.
- Tobias H. Colding and William P. Minicozzi II, “Width and finite extinction time of Ricci flow,” *Geometry & Topology* 12 (2008), 2537–2586.

**Verification boundary:** This document records a conditional analytic derivation. No Lean theorem or repository test is claimed by this note.
