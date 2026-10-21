# Normalization gap: scalar-curvature offset in the width estimate

**Status:** dependency audit. This is not a counterexample to a diameter-only extinction estimate.

## 1. The input used by the width argument

Colding–Minicozzi use the scalar-curvature lower bound

\[
R_{\min}(t)\ge -\frac{3}{2(t+C)}
\]

for a constant \(C>0\) determined by the initial metric. The scalar-curvature evolution equation in dimension three is

\[
\partial_t R=\Delta R+2|\operatorname{Ric}|^2
\ge \Delta R+\frac23R^2.
\]

The comparison ODE \(y'=(2/3)y^2\), initialized at a negative lower bound \(y(0)=R_{\min}(0)<0\), gives

\[
y(t)=-\frac{3}{2(t+C)},\qquad C=-\frac{3}{2R_{\min}(0)}.
\]

If the initial scalar-curvature lower bound is nonnegative, this particular negative-curvature barrier is unnecessary; the displayed formula is intended for the negative initial lower-bound case.

## 2. What diameter normalization does not establish

The formula for this barrier uses an initial scalar-curvature lower bound, not diameter. Consequently, a claim that \(\operatorname{diam}(M,g)=1\) automatically gives a common upper bound on this \(C\) would require an additional theorem relating diameter to the relevant scalar-curvature lower bound. No such theorem is supplied by the width inequality itself.

Thus the implication

\[
\operatorname{diam}(M,g)=1
\quad\Longrightarrow\quad C\le C_{\max}
\]

is **not proved here**. In particular, this note does not claim that the implication is false, nor does it construct a family disproving a diameter-only extinction-time bound.

## 3. Exact frontier for the conditional estimate

The integrated width inequality gives

\[
T_{\mathrm{ext}}\le
\left(C^{1/4}+\frac{W(0)}{16\pi C^{3/4}}\right)^4-C.
\]

To obtain a uniform estimate from this expression using the elementary bounds recorded in CONDITIONAL_NORMALIZED_EXTINCTION_BOUND.md, it suffices to establish common controls

\[
0<C_{\min}\le C\le C_{\max}<\infty,
\qquad W(0)\le W_*<\infty.
\]

The remaining geometry problem is to derive these controls from a useful, explicitly stated normalization or to replace this estimate with one whose inputs are controlled by that normalization. The scalar-curvature barrier alone does not accomplish this.

## 4. Verification boundary

- The ODE calculation above is elementary and explicit.
- The Ricci-flow scalar-curvature evolution inequality and width estimate are established inputs from the literature, not reproved by this document.
- No diameter-only counterexample is claimed.
- No Lean theorem, CI run, or new proof of finite extinction/Poincaré is claimed.

## Reference

Tobias H. Colding and William P. Minicozzi II, “Estimates for the extinction time for the Ricci flow on certain 3-manifolds and a question of Perelman,” *Journal of the American Mathematical Society* 18 (2005), 561–569, DOI 10.1090/S0894-0347-05-00486-8; see also “Width and finite extinction time of Ricci flow,” *Geometry & Topology* 12 (2008), 2537–2586.
