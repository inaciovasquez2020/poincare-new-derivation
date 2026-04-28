# Degree-3 Exposure Lemma — Corrected Frontier Status

Status: Global formulation false.

The previous global non-increasing exposure target is false.

## Counterexample: boundary of the 600-cell

Let

\[
T=\partial C_{600}.
\]

Then

\[
T\cong S^3,
\qquad
T\text{ is closed and simply connected},
\]

\[
|V(T)|=120,
\qquad
d(v)=20\quad\forall v\in V(T),
\]

and every edge has

\[
\deg(e)=5.
\]

Hence

\[
\Phi(T)=\sum_{v\in V(T)} |d(v)-6|
      =120(20-6)
      =1680>0.
\]

No \(3\to2\) move is initially admissible, since every edge has degree \(5\).

No \(4\to1\) move is initially admissible, since every vertex has tetrahedral incidence \(20\).

For a \(1\to4\) move, one tetrahedron is replaced by four tetrahedra. The four old vertices each replace one old tetrahedral incidence by three new tetrahedral incidences, so

\[
d(v):20\mapsto22.
\]

The new vertex has

\[
d(w)=4.
\]

Therefore

\[
\Delta\Phi
=
4\bigl(|22-6|-|20-6|\bigr)+|4-6|
=
4(16-14)+2
=
10>0.
\]

For a \(2\to3\) move, the two opposite vertices change by

\[
d(v):20\mapsto22,
\]

and the three shared-face vertices remain unchanged. Hence

\[
\Delta\Phi
=
2\bigl(|22-6|-|20-6|\bigr)
=
2(16-14)
=
4>0.
\]

Thus every available first move strictly increases \(\Phi\), while the previous global exposure formulation required

\[
\Phi(T_i)\le \Phi(T)
\quad\forall i.
\]

Since \(T\) initially has no degree-\(3\) edge and no admissible first move preserves the bound \(\Phi\le1680\), the global non-increasing Degree-3 Exposure Lemma is false.

## Invalid topological patch

The correction

\[
T\text{ closed simply connected}
\wedge
T\not\cong S^3
\]

is not admissible as a non-vacuous replacement target.

By the Poincaré theorem, a closed simply connected \(3\)-manifold is homeomorphic to \(S^3\). Therefore this antecedent is empty.

It is also circular in a repository whose subject is a Poincaré-type derivation.

## Corrected bounded frontier

For a fixed certified bound \(N\), define the bounded exposure certificate:

\[
\mathrm{BDE}(N):
\]

\[
\forall T\,
\Bigl(
T\text{ closed simply connected triangulated }3\text{-manifold}
\wedge
|V(T)|\le N
\wedge
\Phi(T)>0
\Bigr)
\Rightarrow
\exists T_0,\ldots,T_m
\]

such that

\[
T_0=T,
\qquad
T_{i+1}\in\mathcal M(T_i),
\]

\[
\Phi(T_i)\le\Phi(T)
\quad(0\le i\le m),
\]

and

\[
\exists e\in T_m
\bigl(
\deg(e)=3
\wedge
A(e)+C(e)\ge3
\bigr).
\]

This bounded statement is the corrected deterministic frontier.

It is a finite certificate target, not a global theorem.

If \(N<120\), the \(600\)-cell obstruction is outside the certified domain.

If \(N\ge120\), the certificate must explicitly handle \(\partial C_{600}\) or the non-increasing condition must be replaced by a barrier-descent condition allowing temporary increase.

## Corrected global alternative

A non-vacuous global replacement must allow barriers:

\[
\forall T\,
\Bigl(
T\text{ closed simply connected triangulated }3\text{-manifold}
\wedge
\Phi(T)>0
\Bigr)
\Rightarrow
\exists T_0,\ldots,T_m
\]

such that

\[
T_0=T,
\qquad
T_{i+1}\in\mathcal M(T_i),
\]

\[
\Phi(T_m)<\Phi(T),
\]

with no requirement that

\[
\Phi(T_i)\le\Phi(T)
\quad\forall i.
\]

This barrier-descent replacement is not proved here.

## Remaining open object

The remaining non-vacuous theorem-level object is one of the following:

1. a finite executable proof of \(\mathrm{BDE}(N)\) for the certified bound \(N\), or
2. a global barrier-descent theorem.

No theorem-level Poincaré closure follows from this file.

Compatibility markers:
- The previous single-step edge imbalance formulation is false as stated.
- Replacement theorem object: Degree-3 Exposure Lemma.
- This lemma is **Open**.

Test guard markers:
- Counterexample reference: boundary of the regular \(600\)-cell.
- Replacement theorem object:
  \(T_0=T\), \(T_{i+1}\in\mathcal M(T_i)\), \(\Phi(T_i)\le \Phi(T)\), \(\deg(e)=3\), and \(A(e)+C(e)\ge 3\).
- This lemma is **Open**.
- No theorem-level Poincaré claim follows from this file.

Additional exact guard markers:
- \(\neg\exists e\;(\deg(e)=3)\).
- Status remains open without load-bearing axioms or `sorry` holes.
