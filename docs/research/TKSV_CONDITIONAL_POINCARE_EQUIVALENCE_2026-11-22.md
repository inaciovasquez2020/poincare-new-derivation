# TKSV: conditional Poincaré equivalence and explicit Pachner certificates

Date: 2026-11-22
Status: **conditional framework; independent global Poincaré derivation OPEN**
Source checkpoint: `82c5513626533dd1ab925e9529264e2166bd8247`.
Scope: finite connected closed combinatorial 3-manifolds and legal 1–4, 2–3, 3–2, 4–1 Pachner moves.

## Principal correction: strict net vertex descent is equivalent to Poincaré

Let E be the class of finite connected closed simply connected combinatorial 3-manifolds. Define **G** to mean that each K in E with f0(K)>5 admits a finite legal Pachner path K -> L with f0(L)<f0(K). Temporary vertex increases are allowed.

**Proposition (paper proof, established external topology for reverse implication):**
G if and only if every K in E has realization homeomorphic to S^3.

*G -> Poincaré.* Legal Pachner moves preserve PL type, hence closedness, connectedness and simple connectivity. Every closed combinatorial 3-manifold has at least five vertices. A five-vertex connected closed combinatorial 3-manifold is the boundary of the 4-simplex. Strong induction on f0 and G give the claimed sphere recognition.

*Poincaré -> G.* Poincaré recognition identifies |K| with S^3. By Moise's theorem in dimension three, K and the boundary of the 4-simplex are PL-homeomorphic. Pachner connectivity provides a finite legal bistellar path between them. The endpoint has five vertices, fewer than K.

**Consequences.** G is a reformulation of Poincaré, not a weaker missing lemma. Deriving Poincaré from G is a valid *conditional* theorem but not an independent proof. An independent derivation must prove G without using the classical Poincaré recognition theorem, or use another noncircular global argument.

## Exact move accounting

Define g2(K) = f1(K)-4*f0(K)+10.

| Move | Delta f0 | Delta f3 | Delta g2 |
|---|---:|---:|---:|
| 1–4 | +1 | +3 | 0 |
| 2–3 | 0 | +1 | +1 |
| 3–2 | 0 | -1 | -1 |
| 4–1 | -1 | -3 | 0 |

For any legal sequence ending at the boundary of the 4-simplex, with counts N14, N23, N32, N41:
- N41-N14 = f0(K)-5.
- N32-N23 = g2(K).
- Total length N = f0(K)-5+g2(K)+2*(N14+N23).

These are exact necessary equalities, not a reachability theorem.

## General two-cycle join lower bound

Let C_m and C_n denote simple cycles, m,n>=3. Their join is a triangulated S^3, with:
- f0 = m+n.
- f1 = m+n+mn.
- g2 = (m-3)(n-3)+1.

For m,n>=4, initial edge tetrahedron degrees are n, m, or 4, and vertex tetrahedron degrees are 2n or 2m. Thus no initial 3–2 or 4–1 move exists. Every normalization path begins with a positive 1–4 or 2–3 move, and the count identity yields

**d_P(C_m*C_n, boundary Delta4) >= (m-2)(n-2)+3.**

This bound is attained for m=4 by a uniform explicit construction of length 2n-1. Attainment for all m,n>=5 is NOT ESTABLISHED.

## Exact family certificates: provenance and limitations

Mac-reported read-only finite checks in this research conversation (not rerun from this GitHub branch):

| Family / audit | Cases | Validated moves | Result |
|---|---:|---:|---|
| Suspended-cycle C_m*C_n, 4<=m<=12 and 4<=n<=20 | 153 | 3213 | COMPUTATION_PASS: target vertex removed |
| Global blocker removal on tested join examples | 45 | 747 | COMPUTATION_PASS: star preserved during preparation |
| Stacked g2=0 spheres | 640 | 20800 | COMPUTATION_PASS: complete descent |
| Positive-g2 C3*C_n and stacked C4*C4 families | 298 | 5181 | COMPUTATION_PASS: complete descent |
| Additional g2=2 Q_n construction and stackings | 148 | 3700 | COMPUTATION_PASS: complete descent |
| Optimal C4*C_n, n=4..100 | 97 | 9991 | COMPUTATION_PASS: complete optimal-length descent |

Other independently checked examples:
- Seven legal moves normalize C4*C4 to boundary Delta4, with no temporary vertices.
- Seven legal moves reduce C5*C5 from 10 to 9 vertices; this is not complete normalization.
- A six-vertex stacked-sphere counterexample proves that deletion of an arbitrary blocker edge at zero net vertex cost, preserving a protected star and *all original vertices*, is impossible.
- A separate global-edge counterexample proves that an induced suspended cycle in a vertex link does not imply the suspension edge is absent globally.
- Face-blocker clearance by direct 2–3 when the opposite edge is absent, or by 1–4 followed by 2–3 otherwise, passed adversarial finite tests.

The finite tests establish their precise instances only. They are not Lean kernel certificates and do not establish unrestricted local edge elimination, universal blocker recovery, or G. All claims of arbitrary-link ambient lifting require a separate complete legality proof.

## A conditional theorem, not a proof announcement

**Theorem (conditional):** Given G, every finite connected closed simply connected combinatorial 3-manifold is homeomorphic to S^3.

**Verification boundary:** This statement is a standard strong-induction consequence of G; G itself is equivalent to Poincaré. The provided abstract Lean `Setup` specification encodes base classification, preservation and connectivity as assumed fields; it does not construct these facts from concrete triangulations. No new Lean build or axiom audit is reported here.

## Current open frontier

1. Prove a genuinely noncircular global well-founded descent mechanism allowing auxiliary vertices, **or** find a different independent global argument.
2. Establish the precise hypotheses and full proof of arbitrary-edge blocking clearance, including global complementary-face legality.
3. Distinguish the geometric **G2** face-cycle modules from the numerical invariant **g2** used here.
4. Formalize particular load-bearing finite statements in Lean with no sorry/axiom/opaque/admit/native_decide and audit allowed axioms.
5. Do not infer unconditional Poincaré closure from successful family certificates or from invoking Poincaré for G.

GLOBAL_POINCARE := OPEN
UNIVERSAL_NET_VERTEX_DESCENT := OPEN
ABSTRACT_CONDITIONAL_EQUIVALENCE := PROVED_ON_PAPER
NEW_LEAN_BUILD := NOT_RUN
REPOSITORY_PROMOTION_TO_MAIN := NOT_PERFORMED
