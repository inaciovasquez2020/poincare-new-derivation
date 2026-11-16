# PR #199 Exact-HEAD Verification

HEAD: 237b7c2f8517c3199bd379523bab5a52b64555be
Toolchain: leanprover/lean4:v4.30.0-rc1
Source SHA256: f5b5f1b1cf367872c2a50012d96f68742e7f6ea6d48548eaf154a9c541a38f4c
Compilation: PASS
Axiom audit: PASS
Geometric bridge: OPEN
Universal descent: OPEN

```text
/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.o9KlprFdjH/FullAudit.lean:65:10: warning: This simp argument is unused:
  hb

Hint: Omit it from the simp argument list.
  simp [hb̵,̵ ̵h̵w]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/var/folders/g7/t7cdygm521zfn6t572ncddgw0000gn/T/tmp.o9KlprFdjH/FullAudit.lean:65:14: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [hb,̵ ̵h̵w̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'Poincare.DualPotentialCandidate.step_symmetric' depends on axioms: [propext]
'Poincare.DualPotentialCandidate.reach_symmetric' depends on axioms: [propext]
'Poincare.DualPotentialCandidate.step_shift' depends on axioms: [propext]
'Poincare.DualPotentialCandidate.reach_shift' depends on axioms: [propext]
'Poincare.DualPotentialCandidate.unique_parity_of_no_odd_return' depends on axioms: [propext]
'Poincare.DualPotentialCandidate.potential_of_no_odd_return' depends on axioms: [propext, Classical.choice]
'Poincare.DualPotentialCandidate.potential_of_unique_lifted_paths' depends on axioms: [propext, Classical.choice]
```
