# Face-pairing pillow: exact-source build and axiom audit receipt

Status: **targeted build PASS; targeted theorem axiom audit PASS**.

## Source identity

- Repository: `inaciovasquez2020/poincare-new-derivation`
- Exact checkout/source commit: `4707282f60e7a46b19f47c4f1aa31888f2ed1335`
- Compiled source: `lean/Poincare/FacePairingPillow.lean`
- Source Git blob SHA-1: `7e97d45f943898a7b5a5efc99bdc7f9747f9f712`
- Lean target: `Poincare.FacePairingPillow`

## Build evidence

- Initial independently targeted build: [run 41114142043](https://github.com/inaciovasquez2020/poincare-new-derivation/actions/runs/41114142043), job `124263829829`: **SUCCESS**, 123 jobs, at the exact source commit.
- Additional exact-source targeted rebuild: [run 41131364640](https://github.com/inaciovasquez2020/poincare-new-derivation/actions/runs/41131364640), job `124322838985`: **SUCCESS**, 123 jobs.

## Targeted axiom evidence

The second run performed `#print axioms` for precisely these three declarations after rebuilding their import:

| Declaration | Reported axioms | Result |
| --- | --- | --- |
| `Poincare.twoFacePillow_has_two_identifications` | `Quot.sound`, `propext` | PASS |
| `Poincare.twoFacePillow_distinct_occurrences_and_faces` | `Quot.sound`, `propext` | PASS |
| `Poincare.twoFacePillow_no_repeated_face` | `Quot.sound`, `propext` | PASS |

Permitted axiom set: `propext, Classical.choice, Quot.sound`.

### Archived CI artifact

- GitHub Actions artifact ID: `13013735968`
- Artifact name: `face-pairing-pillow-targeted-audit`
- Artifact digest reported by GitHub: `sha256:778b58c378961bd600e4ff17882a116444502d73f6617f2f273e6c06ee748a4f`
- Artifact contains the targeted build log, `#print axioms` input and output, the source-bound manifest, and SHA256SUMS. Its lifetime follows GitHub Actions artifact retention.
- This note independently preserves the essential receipt details after artifact expiration.

## Boundary

These checks certify the three narrowly stated witness facts only. They **do not** establish the `2→3, 3→2, 3→2, 3→2` legal four-move factorization of the (2\to0) pillow, endpoint equivalence, a homeomorphism or realization-preserving bridge, or universal Poincaré descent.

**Next admissible object:** a face-pairing-aware specification of the first `2→3` step with a proven boundary pairing and local legality statement, before claiming the four-step composite.
