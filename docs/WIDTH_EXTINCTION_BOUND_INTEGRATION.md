# Width inequality: integrated extinction bound and scaling audit

Status: **Derived conditional estimate from a published differential inequality.** This is not a new proof of the width inequality, nor a substitute for the hypotheses and surgery analysis in the source theorem.

## 1. Starting estimate

Colding–Minicozzi establish, for the relevant closed orientable prime non-aspherical 3-manifold setting under Ricci flow, the forward upper-derivative inequality
\[
D^+W(t)\le -4\pi+\frac{3}{4(t+C)}W(t),
\]
where \(W(t)\ge0\) is the width and \(C>0\) is determined by initial geometric data. The precise flow/surgery hypotheses must be those of the source theorem; this note does not independently extend the estimate to other classes.

Source: Colding and Minicozzi, *Estimates for the extinction time for the Ricci flow on certain 3-manifolds and a question of Perelman*, JAMS 18 (2005), DOI 10.1090/S0894-0347-05-00486-8; see also their *Width and finite extinction time of Ricci flow*, Geometry & Topology 12 (2008).

## 2. Integrating factor calculation

Formally at differentiability times (or using the source's upper-derivative integration argument), multiply by \((t+C)^{-3/4}\):
\[
\frac{d}{dt}\left[W(t)(t+C)^{-3/4}\right]
\le -4\pi(t+C)^{-3/4}.
\]
Integrating from \(0\) to \(T\) gives
\[
\frac{W(T)}{(T+C)^{3/4}}
\le \frac{W(0)}{C^{3/4}}
-16\pi\left[(T+C)^{1/4}-C^{1/4}\right].
\]
Because \(W(T)\ge0\) while the flow remains non-extinct, the right-hand side cannot be negative. Solving for its zero yields the explicit upper-bound expression
\[
\boxed{T_{\rm bound}=
\left(C^{1/4}+\frac{W(0)}{16\pi C^{3/4}}\right)^4-C.}
\]
Under the source theorem's assumptions and its treatment of extinction/surgery, this is the integrated finite-time contradiction. The expression is an upper bound, not an exact extinction time in general.

## 3. Scaling audit

Under parabolic rescaling \(g\mapsto\lambda g\), time and area scale by \(\lambda\). Thus \(W(0)\mapsto\lambda W(0)\) and \(C\mapsto\lambda C\). Each term inside the parentheses in \(T_{\rm bound}\) scales as \(\lambda^{1/4}\), and the fourth power and final \(-C\) scale as \(\lambda\). The bound is therefore scale-covariant.

This resolves the earlier apparent conflict: there is no universal absolute-time bound across arbitrary rescalings, while a geometric-data-dependent bound is compatible with finite extinction.

## 4. What remains open for the proposed normalization

A diameter-normalized uniform bound would require proving that the chosen class of initial metrics controls the combination
\[
\left(C^{1/4}+\frac{W(0)}{16\pi C^{3/4}}\right)^4-C
\]
uniformly. This note does not establish such control from diameter alone, nor does it assert that it is impossible. A valid theorem must state additional geometric hypotheses and prove the needed bound.

## 5. Relevance to the user's global-rigidity program

The transferable proof pattern is limited but concrete:

1. Identify a nonnegative quantity that remains defined while the object persists.
2. Prove a differential or discrete descent inequality with an explicit error term.
3. Integrate/sum the inequality and show indefinite persistence would force the quantity negative.
4. Verify the quantity survives every allowed transition, including surgery or its discrete analogue.

For the triangulation program, the missing step is still a proved global invariant that controls cycles and escape; the Ricci-flow width is not itself such an invariant.

## Verification boundary

- **Derived in this note:** the integrated algebraic bound from the stated width inequality and its scaling covariance.
- **Source-dependent:** the width differential inequality, the precise hypotheses, and the handling of surgery.
- **Not proved:** diameter-only control of width/initial scalar-curvature parameter; a new Poincaré proof; the missing global cyclic-rigidity theorem.
- **Formalization:** no Lean theorem or test result is claimed.
