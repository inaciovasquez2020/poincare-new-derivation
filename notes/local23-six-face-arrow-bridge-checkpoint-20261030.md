# Face-pairing local 2→3 boundary and SnapPy arrow-interface checkpoint

## Verified source-bound receipts

### Existing interior non-reuse invariant
- Source commit: `76d5b44f0bf49cdbafca65ed11e16c3455cdc68e`
- Theorem: `Poincare.standardLocal23InteriorPairings_noRepeatedFace`
- Targeted build: [run 41132100310](https://github.com/inaciovasquez2020/poincare-new-derivation/actions/runs/41132100310), 310/310 jobs, PASS.
- Targeted theorem axiom audit: [run 41132886535](https://github.com/inaciovasquez2020/poincare-new-derivation/actions/runs/41132886535), job `124328060956`, PASS.
- Reported axioms: `Classical.choice`, `Quot.sound`, `propext` (all in allowlist).
- Archived audit artifact ID `13012794737`, SHA-256 `5ac5694229a3fdd4babdfa3127e21293a5b02f20a802515a7d1f3277fcc90bbb`.

### Six exterior boundary correspondences
- Exact source commit: `023ccad50e2535b709d20ca04dad9952ffd66b4e`
- File: `lean/Poincare/FacePairingLocalMove23Boundary.lean`
- Build: [run 41133163232](https://github.com/inaciovasquez2020/poincare-new-derivation/actions/runs/41133163232), job `124328990801`, **PASS**, `311/311`.
- Theorems: `standardLocal23BoundaryFaces_card`, `standardLocal23BoundaryFaces_nodup`, and `standardLocal23BoundaryFaces_vertices_agree`.
- Boundary face mapping by occurrence/opposite vertex:
  - `(0,0) → (2,3)` BCD
  - `(0,1) → (1,3)` ACD
  - `(0,2) → (0,3)` ABD
  - `(1,0) → (2,2)` BCE
  - `(1,1) → (1,2)` ACE
  - `(1,2) → (0,2)` ABE

These theorems establish the six local outer triangles and their one-to-one incidence matches. They do **not** establish a globally legal move or any (2\to0) endpoint identification.

## SnapPy source-level constraint

The `McomplexWithExpansion._two_to_zero_base` implementation in
`src/snappy/exterior_to_link/mcomplex_with_expansion.py` first requires:
```python
assert arrow.axis().valence() == 2
assert arrow.equator().valence() == 2
a = arrow.copy()
a.opposite().next().reverse().opposite()
e = self.two_to_three(a, return_arrow=True, must_succeed=True)
```
It includes exceptional-case checks against certain self-gluings and tetrahedron coincidences before the first elementary move.

SnapPy `Arrow` is an occurrence/edge/face frame and `next()` traverses a face gluing permutation (see `src/snappy/snap/t3mlite/arrow.py`). The current Lean `FacePairingData` stores pairings but has **no edge-equivalence quotient, edge-valence function, arrow frame, or external embedding map**.

## Open bridge obligation

Construct an embedding of the *full* local pillow with surrounding gluings into an occurrence-labeled face pairing, and define/verify the transported edge quotient and arrow operations. Prove the post-transition arrow face produced by
`a.opposite().next().reverse().opposite()` matches the bipyramid `2→3` source site, with all guards satisfied.

Until this is done:

`BOUNDARY := ¬ VerifiedArrowSelectedLocal23Compatibility`

Do not attempt or assert the subsequent three `3→2` moves, a `2→0` factorization, endpoint equivalence, or global descent.
