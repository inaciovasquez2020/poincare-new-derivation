# Parity face chart via finite closed lifts

**Status:** paper-level assembly argument; exact Lean declarations and axiom audit NOT_RUN. Local HEAD `02637eb1…` unavailable on GitHub, and this note must not be represented as a verified implementation. `GLOBAL_POINCARE := OPEN`.

## 1. Finite closed-lift quotient principle

Let `P,Y` be topological spaces, `ι` finite, and `Aᵢ` topological spaces. Let `c:P→Y` be continuous and `jᵢ:Aᵢ→P` continuous. Assume each `c∘jᵢ:Aᵢ→Y` is a **closed map**, and every `y∈Y` has some preimage `c(jᵢ(a))=y`.

Then `c` is quotient. Surjectivity follows from coverage. To verify the topology, if `c⁻¹(B)` is closed, `(c∘jᵢ)⁻¹(B)=jᵢ⁻¹(c⁻¹(B))` is closed. The image `Bᵢ := (c∘jᵢ)''((c∘jᵢ)⁻¹(B))` is closed because `c∘jᵢ` is closed; coverage gives `B=⋃ᵢBᵢ`, a **finite** union of closed sets. The opposite implication uses continuity of `c`.

This theorem does **not** require each `jᵢ` to be injective or closed; closedness is required only of `c∘jᵢ`. The closure of the images alone is insufficient unless the maps are closed on all closed subsets of their respective domains.

## 2. Face-chart application

For a primal face `f` with precisely two distinct tetrahedron cofaces `T,U`, let `U_f` be the locus of carrier points with positive coordinates at every vertex of `f`. Consider tetrahedron-copy representatives `P` restricted to `U_f`, the restricted gluing quotient `q:P→q(P)`, and the normalized chart code `c:P→U_f×Bool`.

Candidate bit normalization: `bit(a) xor (if a.side=T then false else S(f))`. On the two tetrahedron sides, define four lifts `j_{side,k}` by inserting a carrier point in the selected side with raw bit `k xor gauge(side)`. Their chart composites are `x↦(x,k)` on `A_side=U_f∩|side|`.

For the finite closed-lift theorem, verify:
1. The two tetrahedral loci `A_T,A_U` are closed *relative to* `U_f`; each `x↦(x,k)` is a closed map into `U_f×Bool`.
2. `U_f=A_T∪A_U`, using the local star/coface property and the exact carrier construction.
3. `j_{side,k}` and `c` are continuous with the **actual restricted representative topology**; continuity of a map into `Option` or `Bool` cannot be inferred merely from it being a well-defined set function.
4. The relation defining the gluing quotient preserves the chart code. This requires checking every generating gluing, not only a selected direct face-gluing step; `Quot.lift` then handles transitive quotient equality.
5. The **reverse** fiber implication: equal chart codes imply equivalent quotient representatives, using same-side representative identification or a valid parity-face gluing across the two sides.
6. `q` is the actual quotient map after restricting the source over `U_f`. Restriction to a saturated **open** subset is quotient when `q` is quotient; confirm saturation/openness with the exact carrier projection.

Provided (1)-(6), both `q` and `c` are quotient, and have the same fibers, hence yield a homeomorphism `q(P) ≃ₜ U_f×Bool`. Its projection onto `U_f` equals the carrier projection because the equality holds on every representative and `q` is surjective.

## 3. A caution about the precise theorem

The quotient-homeomorphism assembly does not produce the parity-face chart unless **all** quotient and fiber hypotheses have been verified at their actual use sites. In particular, verifying `c` is quotient does not automatically prove the restricted `q` is quotient; and equal chart codes do not imply equivalent representatives without the geometric same-side/opposite-side gluing lemmas.

The abstract finite-closed-lifts proof is mathematical, not yet Lean-compiled. The proposed Lean names `isQuotientMap_iff_isClosed`, `isClosed_iUnion_of_finite`, and `homeomorphOfCompatibleQuotientMaps` must be checked against the pinned repository toolchain and actual declarations before relying on elaboration.

## 4. Connection to PR #199

This chart is a separate local topological construction relevant to the parity-cover viewpoint. It is **not** a substitute for the remaining G2 radial-chain/actual-carrier simplicial-homology comparison. The latter remains the minimal global no-odd-return obligation.

**Classification:** PAPER PROOF (abstract quotient lemma); CONDITIONAL (concrete face-chart application); Lean NOT_RUN; no admissible axiom audit yet; no global JIID or independent Poincaré theorem.
