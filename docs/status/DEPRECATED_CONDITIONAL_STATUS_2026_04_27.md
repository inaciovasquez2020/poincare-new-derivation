# Deprecated Conditional Status — 2026-04-27

Status: Deprecated / Conditional Sketch

This repository is not a proof of the Poincare conjecture.
It contains sorries, axioms, or admitted obligations in load-bearing definitions or lemmas.
It should be treated only as an experimental derivation sketch unless all sorries, admits, and project axioms are removed and the core topological definitions are formalized against accepted Lean topology definitions.

Axiom count: 31
Admit count: 0
Sorry count: 64

## Axiom locations

- `lean/Poincare/GreedySelectorCorrect.lean:7` — `axiom greedy_selector_correct :`
- `lean/Poincare/VertexDefectPhiPos.lean:6` — `axiom vertexDefect_pos_implies_Phi_pos :`
- `lean/Regge/ReggeComplete.lean:16` — `axiom schlafli_local :`
- `lean/Regge/ReggeComplete.lean:19` — `axiom schlafli_global :`
- `lean/Regge/ReggeComplete.lean:22` — `axiom pachner_23_invariant :`
- `lean/Regge/Core.lean:11` — `axiom TetraGeom : Type`
- `lean/Regge/Core.lean:12` — `axiom FundamentalGroup : SimplicialComplex → Type`
- `lean/Regge/ReggeFinal.lean:29` — `axiom holonomy_trivial_implies_fundamental_group_trivial`
- `lean/Regge/Holonomy.lean:21` — `axiom holonomy_injective`
- `lean/Regge/Pachner.lean:8` — `axiom fundamental_group_s3_trivial (T : SimplicialComplex) (h_S3 : IsThreeSphere T) :`
- `lean/Regge/Pachner.lean:28` — `axiom holonomy_identity_is_exp_zero : holonomy_rho T identity_element path t = exp_so3 zero_so3`
- `lean/Regge/HolonomyDerived.lean:6` — `axiom NonDegenerate : SimplicialComplex → Prop`
- `lean/Regge/HolonomyDerived.lean:8` — `axiom holonomy_injective_derived`
- `lean/Regge/ReggeMathComplete.lean:14` — `axiom schlafli_identity :`
- `lean/Regge/ReggeMathComplete.lean:18` — `axiom pachner_invariance :`
- `lean/Regge/ReggeMathComplete.lean:22` — `axiom flat_implies_trivial_holonomy :`
- `lean/Regge/ReggeMathComplete.lean:26` — `axiom trivial_holonomy_implies_simply_connected :`
- `lean/Regge/ReggeMathComplete.lean:30` — `axiom simply_connected_implies_s3 :`
- `lean/Regge/FinalClosure.lean:9` — `axiom edge_generator_linear_independence`
- `lean/Regge/HolonomyMatrixModel.lean:10` — `axiom so3Model : Type`
- `lean/Regge/HolonomyMatrixModel.lean:11` — `axiom SO3Model : Type`
- `lean/Regge/HolonomyMatrixModel.lean:13` — `axiom so3_norm : so3Model → ℝ`
- `lean/Regge/HolonomyMatrixModel.lean:15` — `axiom exp_so3_model : so3Model → SO3Model`
- `lean/Regge/HolonomyMatrixModel.lean:16` — `axiom log_SO3_principal : SO3Model → so3Model`
- `lean/Regge/HolonomyMatrixModel.lean:18` — `axiom log_exp_principal :`
- `lean/Regge/HolonomyMatrixModel.lean:24` — `axiom gramMatrix : SimplicialComplex → ℝ → ℝ`
- `lean/Regge/HolonomyMatrixModel.lean:25` — `axiom lambdaMin : ℝ → ℝ`
- `lean/Regge/HolonomyMatrixModel.lean:27` — `axiom gram_coercive :`
- `lean/Regge/HolonomyMatrixModel.lean:31` — `axiom holonomy_product :`
- `lean/Regge/HolonomyMatrixModel.lean:38` — `axiom holonomy_linearization_constructive`
- `Poincare/Foundations.lean:14` — `axiom boundary_squared_zero : Prop`

## Admit locations

- None

## Sorry locations

- `lean/Poincare/FinalConstructive.lean:12` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:18` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:23` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:29` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:35` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:40` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:48` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:53` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:60` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:66` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:72` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:77` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:86` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:94` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:103` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:109` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:117` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:125` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:132` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:141` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:150` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:160` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:169` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:178` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:188` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:202` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:212` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:223` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:234` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:244` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:259` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:272` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:288` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:304` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:315` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:326` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:337` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:348` — `by sorry`
- `lean/Poincare/FinalConstructive.lean:363` — `by sorry`
- `lean/Regge/ReggeComplete.lean:25` — `def boundary1 {C1 C0} (∂1 : C1 → C0) := by sorry`
- `lean/Regge/ReggeComplete.lean:26` — `def boundary2 {C2 C1} (∂2 : C2 → C1) := by sorry`
- `lean/Oblivion/CanonicalCodes.lean:16` — `def ExtendsGlobally (C C' : Code) : Prop := by sorry`
- `lean/Oblivion/CanonicalCodes.lean:63` — `def Realizes (C : Code) (T : Triangulation) : Prop := by sorry`
- `lean/Oblivion/CanonicalCodes.lean:65` — `def PachnerMove (T T' : Triangulation) : Prop := by sorry`
- `lean/Oblivion/CanonicalCodes.lean:185` — `def IsSphere (X : Type) : Prop := by sorry`
- `lean/Oblivion/CanonicalCodes.lean:432` — `def preserves_incidence (φ : Iso2Complex L SphereModel) : Prop := by sorry`
- `lean/Oblivion/CanonicalCodes.lean:498` — `def preserves_faces (φ : Iso2Complex L SphereModel) : Prop := by sorry`
- `lean/Oblivion/CanonicalCodes.lean:499` — `def preserves_edges (φ : Iso2Complex L SphereModel) : Prop := by sorry`
- `lean/Oblivion/CanonicalCodes.lean:500` — `def preserves_vertices (φ : Iso2Complex L SphereModel) : Prop := by sorry`
- `lean/Oblivion/CanonicalCodes.lean:569` — `sorry`
- `lean/Oblivion/CanonicalCodes.lean:610` — `sorry`
- `lean/Oblivion/CanonicalCodes.lean:624` — `sorry`
- `lean/Oblivion/CanonicalCodes.lean:634` — `sorry`
- `lean/Oblivion/CanonicalCodes.lean:636` — `-- Replace previous sorry using algebra lemma`
- `lean/Oblivion/CanonicalCodes.lean:680` — `sorry`
- `lean/Oblivion/CanonicalCodes.lean:697` — `-- Final elimination of edge_face_relation sorry using explicit counting`
- `lean/Oblivion/CanonicalCodes.lean:715` — `sorry`
- `lean/Oblivion/LASRStandalone.lean:26` — `def FOkAdmissible {α : Type u} (k R Δ B : Nat) (C : Configuration α) : Prop := by sorry`
- `lean/Cyclone/CycleBasisLift.lean:44` — `def IsTreeSubgraph (G : Graph) (S : Set G.V) : Prop := by sorry`
- `Poincare/GreedyDescent.lean:60` — `sorry`
- `Poincare/GreedyDescent.lean:68` — `sorry`
- `Poincare/GreedyDescent.lean:73` — `sorry`
- `Poincare/GreedyDescent.lean:78` — `sorry`
- `Poincare/GreedyDescent.lean:85` — `sorry`

## Boundary rule

If `axiom + admit + sorry > 0`, no Poincare-proof claim is allowed.
