# Mathematical erratum — 2026-11-25

Base: `8842f3bf42c7ddc604a1b545d9116ef34effdc25`.

## [docs/lemmas/sign_mixing_edge_lemma.tex](../docs/lemmas/sign_mixing_edge_lemma.tex)

The averaging proof is invalid. Curvature balance does not imply either weighted degree-three incidence sum vanishes. Edges with a zero-curvature endpoint also need not lie wholly in a single sign class. Even the stated balance and existence of a degree-three edge allow all vertex degrees to equal six at the level of abstract degree data; no strict sign change then exists. This is not asserted to be a realizable triangulation. The intended manifold lemma remains unproved, and \texttt{scripts/tests/sign\_mixing\_search.py} samples unconstrained degree labels and edges rather than triangulations or curvature-balanced data. It cannot certify this lemma. See the existing unsupported-route classification in the derivation document.

## [docs/chronicles_final_wall.tex](../docs/chronicles_final_wall.tex)

The conditional qualitative implication is retained: if unbounded complexity forces unbounded witness count, and the witness count satisfies $m\le C T$ for the number $T$ of realized types, then bounded $T$ forces bounded complexity. The stated numerical bound $\operatorname{cx}_H(G)\le CC_0$ does not follow. It would require an additional quantitative comparison between complexity and witness count, for example $\operatorname{cx}_H(G)\le A m+B$, yielding $\operatorname{cx}_H(G)\le AC C_0+B$ when $T\le C_0$. The same-threshold conclusion is not justified by the displayed assumptions. No global Poincare closure is established.

Paper audit only. No Lean declarations or PDF artifacts changed. Existing local Pachner theorems are not reclassified. Code search on the default branch found the derivation's existing unsupported-route notice and the random-label search script, but did not establish a complete dependency audit.
