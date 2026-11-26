# U(16) delayed-insertion certificate

Date: 2026-11-26

## Verification baseline

- Repository HEAD: 82c5513626533dd1ab925e9529264e2166bd8247
- Branch: work/first-nonzero-reentry-20261027
- Lean: 4.30.0-rc1
- Research gates: 13/13 complete
- Lean declarations audited: 62/62
- Compiler warnings: zero
- Forbidden axioms: zero

## Formal results

- Legal commutation diamonds for independent Pachner moves.
- Arbitrary-position fresh stellar insertion.
- Conditional admissible-swap path normalization.
- Preservation of applicable upper bounds during delayed swaps.
- Exact simultaneous-activation and nested-rewrite fixtures.

## Computational results

At peak defect cap 368:

| Objective | Shorter paths excluded | Minimum moves |
|---|---:|---:|
| Strict defect descent | 11 | 12 |
| Strict descent restoring vertex count to 16 | 12 | 13 |

The exhaustive bounded searches examined 16,187 and 23,235
distinct retained states, respectively.

Both searches permit consecutive insertions and do not use
unrestricted immediate-touch pruning.

Initial defect: 352.
Final witness defect: 348.

## Reproduction

From the repository root, using the pinned environment:

    lake env lean docs/certificates/u16_delayed_insertion_2026-11-26/DelayedInsertionNormalization.lean

    python3 -B docs/certificates/u16_delayed_insertion_2026-11-26/u16_final.py /tmp/u16-computation.json

## Scope limitations

The normalization theorem is conditional on admissible-swap closure.
Unrestricted immediate-touch pruning is not justified.
Higher-cap shortest-path exclusions remain open.
Universal stabilized descent remains open.
The computational search is not itself Lean-verified.
Restored vertex count means cardinality, not fixed vertex labels.

GLOBAL_POINCARE := OPEN

This directory preserves a standalone research certificate rather
than modifying the repository's principal Lean import hierarchy.
