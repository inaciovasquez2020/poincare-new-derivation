# Two-step return audit for mixed fan/reentry dynamics

Status: **PARTIAL REDUCTION — no two-step exclusion theorem proved.**

## Exact transition cases

The relation FanReentryModeStep has five constructors:

- fan_next: fan to fan, with the next edge equal to the current transition's
  certified successor edge;
- fan_reentry: fan to witnessed reentry, carrying the complementary-edge
  witness and exact-three successor;
- fan_reinject: fan to fan, with an explicit changed-edge condition;
- reentry_next: witnessed reentry to witnessed reentry through the actual
  Move32SourceFaceWitnessedReentry relation;
- reentry_fan: witnessed reentry to fan, with an explicit nonself condition.

For the two reentry constructors, the current and next shared edges are
nonself: in reentry_next this follows from the witnessed relation's
nonself complementary-edge clause and the successor endpoint equalities; in
reentry_fan it is an explicit field. For fan-to-fan transitions, the edge
changes by FanReentryModeStep.fan_to_fan_canonicalEdgeKey_ne.

Thus the relation excludes a one-step return to the same unordered edge in
the same fan mode, but this does **not** rule out a two-step cycle A -> B -> A.

## What the existing return lemmas give

If a witnessed reentry returns to an anchor's unordered shared edge and the
returning complementary tetrahedron is one of the anchor target tetrahedra,
GlobalMove32ReentryReturnCrossingConfiguration derives the cross-incidence
facts and identifies the return edge with the anchor edge.

GlobalMove32ReentryReturnSourceFaceOverlap then derives at least two distinct
vertices common to the anchor and return source faces.

This is a genuine geometric constraint, but it is not a contradiction:
the source-face intersection is permitted by the current theorem statement.
No existing implication from that overlap to a legal Move23, strict descent,
or forbidden degree-four/high-edge outcome has been identified.

## Exact remaining obligation for a two-step proof

For each possible pair of constructors in FanReentryModeStep, assume
q₀ → q₁ and q₁ → q₀. Then either:

1. derive a contradiction using the actual transition witnesses and the
   existing link-star and source-face separation results; or
2. construct a triangulation satisfying the full closed-manifold, link,
   degree, and no-outcome hypotheses that realizes the pair.

An abstract two-node directed graph is not a valid geometric counterexample.
Likewise, edge-key inequality alone cannot exclude a two-cycle.

## Boundary

**Not proved:** no two-step cycle of the complete mixed state exists.

**Not established:** a topology-compliant two-step counterexample exists.

The next proof attempt must split on the two transition constructors and
derive an incidence contradiction from the full witnesses, not from the
edge keys alone.
