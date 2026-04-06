# NOTE: Raw unconditional form Phi(T)=0 -> S3(T) is false in general; repaired form uses invariant(T)=0 to force simply_connected(T).
# Derivation Log

## Step 1 — Local move system
Let \(T\) be a finite triangulation of a closed \(3\)-manifold.
Use admissible moves
\[
(1\leftrightarrow 4),\qquad (2\leftrightarrow 3).
\]

## Step 2 — Candidate defect
\[
\Phi(T)=\sum_{v}|d(v)-6|.
\]

## Step 3 — Candidate descent under a \((3\to 2)\) move
For an edge \(e=(u,v)\) of edge-degree \(3\), with opposite vertices \(w_1,w_2,w_3\),
\[
\Delta_e
=
\sum_{x\in V(e)} \bigl(|d(x)-6|-|d'(x)-6|\bigr).
\]

The sign reduction yielded the formal criterion
\[
\Delta_e>0 \iff A+C\ge 3,
\]
with
\[
A=\#\{x\in\{u,v\}: d(x)>6\},\qquad
C=\#\{w_i: d(w_i)<6\}.
\]

## Step 4 — Missing lemma
A sufficient missing lemma is:

### Edge Imbalance Lemma
For every closed simply connected triangulated \(3\)-manifold with
\[
\Phi(T)>0,
\]
there exists an edge \(e\) of edge-degree \(3\) such that
\[
A+C\ge 3.
\]

## Step 5 — Failed route
A global max-degree control lemma was introduced and then refuted.
Hence that route is invalid.

## Step 6 — Unsupported route
A sign-mixing lemma was asserted:
\[
\exists e=(u,v)\text{ such that }(d(u)-6)(d(v)-6)<0.
\]
This was not established rigorously.

## Step 7 — Unsupported zero-defect closure
The claim
\[
\Phi(T)=0 \Rightarrow T\cong \partial\Delta^4
\]
was also not established.

## Conclusion
The derivation remains conditional and incomplete.
