# Degree-3 Exposure Lemma

**Status:** Open.  
**Role:** Replacement target for the false single-step Edge Imbalance Lemma.

---

## Failure of the single-step Edge Imbalance Lemma

The single-step statement

\[
\Phi(T)>0
\Rightarrow
\exists e\text{ of degree }3\text{ such that }A(e)+C(e)\ge 3
\]

is false as stated.

A counterexample is the boundary of the regular \(600\)-cell.

For this triangulation,

\[
T\simeq S^3,
\]

\[
|V(T)|=120,
\]

\[
d(v)=20\quad\forall v,
\]

and every edge has degree

\[
\deg(e)=5.
\]

Therefore

\[
\Phi(T)=\sum_{v\in T}|d(v)-6|
       =120|20-6|
       =1680>0,
\]

but

\[
\neg\exists e\;(\deg(e)=3).
\]

Thus the Edge Imbalance Lemma cannot be used as a one-step descent theorem.

---

## Replacement theorem object

The correct replacement target is the following exposure lemma.

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
\]

\[
T_{i+1}\in\mathcal M(T_i),
\]

\[
\Phi(T_i)\le \Phi(T)
\quad
(0\le i\le m),
\]

and

\[
\exists e\in T_m\,
\bigl(
\deg(e)=3
\wedge
A(e)+C(e)\ge 3
\bigr).
\]

Consequently, if the final exposed edge satisfies the strict descent sign condition, then

\[
\exists T'\in\mathcal M^{*}(T)
\quad
\Phi(T')<\Phi(T).
\]

---

## Current status

This lemma is **Open**.

No theorem-level Poincaré claim follows until this exposure lemma and the zero-defect characterization are formally proved without load-bearing axioms or `sorry` holes.

---

## Frontier lock

The repository may not claim that the Edge Imbalance Lemma is proved in its original single-step form.

The repository may only use the Degree-3 Exposure Lemma as an open replacement target.
