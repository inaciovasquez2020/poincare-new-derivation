import Lean
import Poincare.VertexLinkLocalConnectednessCounterexample

open Lean

/-
Isolated audit against the pre-edit source commit c8971611b28b1a78d4b5d886642472fa13f5ee66.
The generated declaration type identifies the branch proposition; declaration ranges, when retained
by Lean, identify the source span. This file is audit-only and does not modify the target proof.
-/

#check Poincare.edgePinchCandidate_closedCore._native.native_decide.ax_1_426
#print Poincare.edgePinchCandidate_closedCore._native.native_decide.ax_1_426

run_cmd do
  let target : Name :=
    `Poincare.edgePinchCandidate_closedCore._native.native_decide.ax_1_426
  let env ← getEnv
  match env.find? target with
  | none =>
      logError m!"AUDIT_MISSING_DECLARATION := {target}"
  | some info =>
      logInfo m!"AUDIT_DECLARATION := {target}"
      logInfo m!"AUDIT_TYPE_EXPR := {info.type}"
      let ranges ← Lean.findDeclarationRanges? target
      logInfo m!"AUDIT_SOURCE_RANGE := {ranges}"
