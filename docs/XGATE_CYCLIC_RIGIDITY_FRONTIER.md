# Xgate cyclic-rigidity frontier

Status: **OPEN — no repository theorem closure claimed.**

Base inspected: `bc377ea27d02c5d23e70f6e07f6000eb4322c1b3`.

## Existing verified inputs

- `Poincare.exists_recurrent_highFanEdgeEndpoints` gives indices `i,j` with `i + 1 < j`, a finite bound by `Fintype.card (SupportedEdgeState K)`, return of the same *unordered central edge* (possibly with reversed endpoint order), and retained transition-step facts on the segment.
- `Poincare.EXISTS_RECURRENT_LOCAL_FAN_CONFIGURATION` is stronger than the endpoint recurrence alone: since `HighFanLocation K` is finite and consecutive locations cannot coincide, it obtains a nonconsecutive repeated **oriented** central edge together with the same retained ordered adjacent link-triangle pair.
- `Poincare.FanChordTransition.same_location_transverse_eq` proves that repeated retained local location forces the same transverse carrier.
- `Poincare.FanChordTransition.same_location_same_transverse_same_chord` proves that the same location and transverse carrier determine both chord endpoints.
- `Poincare.repeated_highFan_location_next_edgeState_eq` combines these facts: repeated retained local location forces equality of the successor edge states.
- `Poincare.FanChordTransition.same_location_different_transverse_impossible` rules out different transverse carriers at the same retained location.
- `Poincare.ClosedTriangulationCore.fanChord_twoCycle_same_transverse_impossible_noFour` excludes the specific two-step return with the same transverse carrier under the no-degree-four and connected-link hypotheses.
- `Poincare.ClosedTriangulationCore.exists_finite_recurrent_highFanEdgeCycle_of_noMove23_noDescent_noHigh` constructs a recurrent segment from the stated no-move, no-descent, and no-high-edge exclusions. Its documentation explicitly says that this does not itself assert the recurrent cycle is impossible.

## What has been derived

The changing-transverse case at an identical retained location is already excluded. In fact, a repeated `HighFanLocation` forces the transverse carriers and chord endpoints to agree, so the next central edge state repeats as well. This is the repository's existing local shortening mechanism.

That still does **not** contradict the current recurrent-cycle theorem. The exact implication proved by `repeated_highFan_location_next_edgeState_eq` is only

`states[i].location = states[j].location` and valid continuation steps imply `states[i+1].edgeState = states[j+1].edgeState`.

It does **not** prove `states[i+1] = states[j+1]`, equality of their retained `FanChordTransition`s, or equality of their next local locations. `HighFanState` stores a transition, including the ordered adjacent link triangles and tetrahedral witnesses; equality of the canonical central-edge key forgets that data. The continuation construction is existential rather than a demonstrated function of the edge state, so the same central edge can carry different retained transition data.

A proposed shortening based only on successor-edge equality is therefore invalid: the repeated edge-state indices are shifted by one but have the same separation, and no repeated full state or well-founded decrease follows. To make shortening valid, one needs either (a) a deterministic/memoryless continuation theorem that is proved compatible with the geometric construction and a cycle-minimality argument, or (b) a separate incidence/link invariant that forbids the residual cycle. Neither follows merely from finite recurrence of edge states.

## Abstract countermodel boundary

At the abstract finite-state level, a directed cycle can return to an edge key while retaining different transition/location labels at each occurrence. This shows that the endpoint bookkeeping alone cannot imply geometric rigidity. It is **not** a triangulation of a closed 3-manifold and is **not** a counterexample to the repository's full geometric hypotheses. No topology-compliant counterexample has been found or claimed.

## Weakest missing invariant

The prior proposed target—forcing a repeated location with different transverse carriers—is the wrong target because the existing lemmas prove that case impossible directly. The useful target is instead one of the following:

1. **Cycle-shortening invariant:** show that the repeated-location successor-edge equality produces a strictly shorter recurrent object in a well-founded measure that the actual construction preserves; or
2. **Geometric closure invariant:** show that any recurrent edge cycle with changing retained locations necessarily produces the already excluded same-transverse two-step configuration, or a legal Move23 / strict topology-preserving `PhiSupport` descent / prohibited high-edge obstruction.

The invariant must be derived from the retained transition geometry and the actual `ClosedTriangulationCore`, manifold, connected-link, no-degree-four, no-Move23, no-descent, and no-high-edge assumptions. It must not be introduced as an unproved axiom or assumed theorem.

## Verification boundary

- **Proved at base:** finite recurrent edge endpoint reduction; finite repeated-local-location reduction; uniqueness of transverse carrier and chord endpoints at a repeated location; equality of successor edge states; the same-transverse two-step contradiction.
- **Not proved:** a well-founded cycle-shortening invariant; cyclic rigidity for longer cycles with changing retained locations; a topology-compliant counterexample; global high-fan termination; `Poincare.JIID`; Poincare conjecture.
- **Changes in this branch:** this frontier record only; no Lean theorem is asserted by this document.


## Follow-up: the mixed-mode continuation has the same frontier

Inspection of `GlobalFanReentryModeLinkedStep.lean`,
`GlobalFanReentryModeFiniteRecurrence.lean`, and
`GlobalFanReentryModeFailClosedRecurrence.lean` confirms that the repository
already retains more lineage for the mixed fan/reentry process. Its finite-key
recurrence theorem classifies the return as either a nonconsecutive repeated
fan edge or a repeated witnessed-reentry key. The source comments explicitly
stop at recurrence and do not exclude either cycle.

This does not supply the missing cycle invariant. The finite key deliberately
forgets local link triangles and witness data; even recurrence of a full
`HighFanState` would only yield a periodic trajectory under a
nondeterministic successor relation. Periodicity is not itself contradictory:
the no-move/no-descent hypotheses produce an infinite obstruction trajectory,
and an additional geometric theorem is needed to rule out its cycle.

### Well-founded-measure audit

- `PhiSupport` is a measure on the triangulation, which remains fixed along
  this obstruction trajectory. It strictly decreases only when the separate
  descent alternative is taken; under the no-descent branch it supplies no
  decrease along successive states.
- The canonical edge key and the mixed finite key are finite recurrence keys,
  not strictly decreasing measures.
- No source-level theorem found in the inspected continuation/recurrence files
  makes the successor choice a function of the coarse key or proves a
  strictly decreasing measure on retained transitions.
- Therefore the minimal-cycle route remains conditional on a new invariant;
  it cannot be completed by applying finite pigeonhole recurrence alone.

**Updated conclusion:** the repository proves finite recurrence and local
same-location rigidity. It does not yet prove cyclic rigidity, exclude the
residual recurrent fan/reentry branches, or supply a compliant counterexample.


## Follow-up: exact retained reentry data and the residual return

The source definitions show that `WitnessedReentryState` retains a `Move32Site`,
its realization proof, and its exact-three shared-edge proof. The
`Move32SourceFaceWitnessedReentry` relation additionally retains two distinct
tetrahedra sharing the old obstruction face, complementary vertices `x,y`,
a tetrahedron containing the new edge, and the exact equalities
`s'.d = x`, `s'.e = y`. Thus this branch does retain more geometric lineage
than the finite key does.

However, `FanReentryModeState.finiteKey` reduces a reentry state to only the
canonical unordered pair `{site.d, site.e}`. Existing
`sharedSupportedEdgeState_ne_of_sourceFaceReentry` proves adjacent keys differ;
the finite recurrence theorem then gives a nonconsecutive repeated key. It does
not prove the repeated full `Move32Site`s or the complementary tetrahedral
witnesses are equal.

The potentially useful invariant is therefore not simply edge recurrence. It
must exploit how the complementary pair `(x,y)` is extracted from the old
tetrahedra and how the next site’s obstruction face is selected. A precise
candidate target is a return-rigidity theorem: for a closed witnessed-reentry
cycle, show that a repeated canonical shared edge plus the retained step
witnesses forces either (i) equality of full sites with a forbidden immediate
self-edge, (ii) a degree-four vertex, or (iii) a legal Move23 / strict
`PhiSupport` descent. The inspected definitions do not currently establish
this disjunction. This is a proof target, not a theorem or verified conjecture.

## Follow-up: high-edge branch and normalization closure audit (2026-10-23)

This audit separates the branches already handled by the code from the theorem still required for a global normalization argument. It is a documentation-only frontier update; it does not assert a new Lean theorem.

### Branch 1 — high edge conversion

The existing theorem
`ClosedTriangulationCore.exists_legal_move23_or_highFanState_of_edgeIncidence_four_le`
converts an edge with incidence at least four, under its stated core/manifold/incidence hypotheses, into either a legal Move23 site or a `HighFanState`. This is a valid branch split, not a termination result.

The source-face obstruction chain also contains
`move32_sourceFace_obstruction_false_of_noHigh`: under its connected-link and no-degree-four hypotheses, a represented source-face obstruction forces a nonself high-incidence edge. Consequently, any attempted global argument that assumes both such an obstruction and absence of all nonself high edges is vacuous under those hypotheses. It cannot discharge the genuine high-edge branch.

### Branch 2 — legal-move progress

The existing Move2332 block proves a strict `PhiSupport` decrease when its second Move32 source face is absent. When that source face is represented, the theorem retains the second source-face obstruction and the automatic reinjection theorem routes the next state to a legal Move23 option, a high-fan mode, or witnessed reentry (depending on the exact theorem's hypotheses).

This handles the local legal-move alternative only when the required incidence-four and legality premises are available. It does not prove that every legal Move23 selected by the general high-edge split admits the specific balanced Move2332 block, nor that the remaining obstruction branches terminate. Do not generalize the local block to all legal moves without proving those premises.

### Branch 3 — exact termination obligation

The missing statement is a geometric cycle-exclusion/termination theorem for the actual retained transition data. In particular, it must not merely repeat a finite-key recurrence result. It must establish, under the actual closed connected 3-manifold, closed-core, connected-link, tetrahedron-overlap, and no-degree-four assumptions, that a recurrent high-fan/witnessed-reentry cycle yields at least one of:

1. a legal move for which the applicable local progress theorem's premises are proved;
2. a strict topology-preserving `PhiSupport` descent;
3. a contradiction with an established incidence/link constraint.

The current sources do not establish this disjunction for every recurrent cycle. The abstract finite-key countermodel boundary above is only a warning about insufficient bookkeeping, not a triangulation counterexample.

### Branch 4 — normalization and JIID

Even a proved cycle-exclusion lemma would need to be connected to a well-founded normalization induction: each nonterminal case must produce a valid successor triangulation in the same admissible class and either decrease a natural-valued measure or discharge the case. Only after the induction yields the stated normalization theorem may its existing topological consequence be applied. The current frontier does not prove the required universal descent/normalization theorem, and `Poincare.JIID` remains open.

### Verification record

- **Inspected repository:** `inaciovasquez2020/poincare-new-derivation`, default branch `main`, on 2026-10-23.
- **Files checked:** `GlobalHighEdgeToFanState.lean`, `GlobalFanChordMove2332SecondStep.lean`, `GlobalFanChordMove2332AutomaticModeReinjection.lean`, `GlobalMove32SourceFaceNoHighContradiction.lean`, `GlobalFanReentryModeFiniteRecurrence.lean`, and this frontier document.
- **Code change:** none in Lean; this update records the audited proof boundary and the precise missing implication.
- **Build/CI:** not run in this session. No compile, theorem closure, normalization completion, or Poincare proof is claimed.
