# Scale-covariant extinction: exact benchmark and unresolved normalized frontier

Status: **Exact model calculation + open target.** This note does not modify or challenge Perelman's finite-extinction theorem.

## 1. Exact benchmark on a fixed topology

Let \(g_{\mathrm{unit}}\) be the unit round metric on \(S^3\). Under the convention
\[
\partial_t g=-2\operatorname{Ric}(g),
\]
the round family
\[
g_R(t)=(R^2-4t)g_{\mathrm{unit}},\qquad 0\le t<T_R,
\]
has extinction time
\[
T_R=R^2/4.
\]
Its initial diameter is \(D_R=\pi R\). Therefore
\[
\boxed{T_R/D_R^2=1/(4\pi^2)},\qquad
\boxed{T_R=D_R^2/(4\pi^2)}.
\]
This is an exact equality, not a numerical fit.

## 2. Counterexample and what normalization fixes

There is no finite constant \(C\) such that every initial round metric on this same \(S^3\) becomes extinct by time \(C\): choose \(R>2\sqrt C\). This refutes only a scale-independent absolute-time bound.

Normalizing the initial diameter to one removes this particular scaling obstruction. It does **not**, by itself, prove that all normalized metrics have a uniformly bounded extinction time. That would require a separate theorem with explicit hypotheses and a proof controlling geometry beyond the round family.

Ricci-flow scaling explains the obstruction: if \(g(t)\) solves the equation, then \(\tilde g(t)=\lambda g(t/\lambda)\) also solves it, and its time interval is multiplied by \(\lambda\). Any scale-covariant time estimate must scale like a length squared.

## 3. The shadow-of-infinity test

Set \(R_n\to\infty\) and choose basepoints \(p_n\in S^3\). For bounded time intervals and bounded spatial neighborhoods, the round metrics converge in pointed smooth topology to Euclidean space. In polar coordinates on a fixed bounded region,
\[
g_n(t)=dr^2+(R_n^2-4t)\sin^2\!\left(\frac{r}{\sqrt{R_n^2-4t}}\right)g_{S^2}.
\]
Writing \(s_n(t)=\sqrt{R_n^2-4t}\), the angular coefficient is
\[
s_n(t)^2\sin^2(r/s_n(t))
=r^2\left(\frac{\sin(r/s_n(t))}{r/s_n(t)}\right)^2
\longrightarrow r^2
\]
in \(C^\infty\) on compact spatial regions, uniformly on each bounded time interval. Hence the limit is the stationary Euclidean Ricci flow. Yet each compact member becomes extinct at \(T_n=R_n^2/4\to\infty\).

The logical failure is precise: **finite extinction for every member of a sequence does not imply finite extinction of its pointed noncompact limit, and does not imply a uniform extinction-time bound.** Compactness of each input is not preserved by this limiting process.

## 4. The actual frontier for a stronger theorem

A meaningful next statement would have the form:

> For a specified class \(\mathcal C\) of closed simply connected Riemannian 3-manifolds, with a stated scale normalization and explicit geometric control, there exists a finite bound for \(T_{\mathrm{ext}}\) depending only on those normalized controls.

This is a **target, not an established theorem**. A proof must identify the exact admissible controls, show they are sufficient for the extinction argument (including surgery), and derive a bound. Diameter normalization alone is not justified here as sufficient.

## 5. Relevance to the triangulation/global-rigidity program

The analogy is methodological, not a transfer of proof: a local or finite-stage descent statement does not establish global termination if the hypotheses permit escape through unbounded scale, degeneration, or an infinite sequence of states. A valid global theorem needs a named invariant and a compactness/well-foundedness argument that rules out the relevant escape mode.

For the repository's triangulation program, this note supplies no missing cyclic-rigidity lemma and proves no Poincaré theorem. It identifies a proof obligation: state the global invariant, its domain, and the mechanism that prevents an infinite trajectory from escaping every finite controlled region.

## Verification boundary

- **Proved here:** exact round-flow formula; exact diameter-normalized equality; failure of any scale-independent absolute extinction-time bound; pointed round limit calculation.
- **Not proved here:** a universal extinction bound for all diameter-normalized metrics; a new estimate for Perelman's surgery flow; a counterexample to Perelman's theorem; the repository's missing global cyclic-rigidity theorem; a new proof of Poincaré.
- **Formalization:** no Lean theorem or test result is claimed by this document.
