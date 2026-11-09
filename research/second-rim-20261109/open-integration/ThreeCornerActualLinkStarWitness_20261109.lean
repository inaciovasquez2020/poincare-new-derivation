/-!
SOURCE-LOCAL LEAN CANDIDATE — NOT COMPILED

Place inside namespace Poincare in an isolated copy of
lean/Poincare/GlobalEdgeCyclicFanChordClassification.lean,
AFTER the existing private theorem
AmbientEdgeCyclicFan.star_length_eq_three_of_triangle and BEFORE end Poincare.

The declarations use the actual Poincare.Triangulation, Tet, LinkTriangle,
vertexLinkStarTriangles, vertexLinkStarGraph, and AmbientEdgeCyclicFan APIs.
They do not postulate second-move legality.
-/

private theorem threeCorner_extractStarTriangle
    {K : Triangulation} (v x : Nat)
    (τ : Tet) (hτ : τ ∈ K.tets)
    (hv : v ∈ τ.verts) (hxv : x ≠ v) (hx : x ∈ τ.verts) :
    ∃ σ : {ρ : LinkTriangle // ρ ∈ vertexLinkStarTriangles K v x},
      τ.linkTriangleAt? v = some σ.1 ∧
      ∀ y : Nat, y ≠ v → y ∈ τ.verts → y ∈ σ.1.verts := by
  obtain ⟨σ, hσ, hExtract⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem K v τ hτ hv
  have hxσ : x ∈ σ.verts :=
    (τ.mem_linkTriangleAt?_iff v x σ hExtract hxv).2 hx
  refine ⟨⟨σ, (mem_vertexLinkStarTriangles_iff K v x σ).2 ⟨hσ, hxσ⟩⟩,
    hExtract, ?_⟩
  intro y hyv hy
  exact (τ.mem_linkTriangleAt?_iff v y σ hExtract hyv).2 hy

private theorem threeCorner_extractedTriangles_ne
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v : Nat} {τ υ : Tet}
    (hτ : τ ∈ K.tets) (hυ : υ ∈ K.tets)
    {σ ρ : LinkTriangle}
    (hσ : σ ∈ vertexLinkTriangles K v)
    (hρ : ρ ∈ vertexLinkTriangles K v)
    (hExtractτ : τ.linkTriangleAt? v = some σ)
    (hExtractυ : υ.linkTriangleAt? v = some ρ)
    (hne : τ ≠ υ) : σ ≠ ρ := by
  intro heq
  apply hne
  calc
    τ = ambientTetOfVertexLinkTriangle K v ⟨σ, hσ⟩ :=
      (hcore.ambientTetOfVertexLinkTriangle_eq hσ hτ hExtractτ).symm
    _ = ambientTetOfVertexLinkTriangle K v ⟨ρ, hρ⟩ :=
      congrArg (ambientTetOfVertexLinkTriangle K v) (Subtype.ext heq)
    _ = υ := hcore.ambientTetOfVertexLinkTriangle_eq hρ hυ hExtractυ

/-- Three distinct actual tetrahedra sharing the edge `(v,x)` and pairwise
sharing, respectively, the off-edge vertices `b`, `c`, `z` induce a
3-clique in the *actual* represented link-star graph. -/
theorem ClosedTriangulationCore.threeCorner_linkStarTriangle
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (v x b c z : Nat)
    (hxv : x ≠ v)
    (hbv : b ≠ v) (hcv : c ≠ v) (hzv : z ≠ v)
    (hbx : b ≠ x) (hcx : c ≠ x) (hzx : z ≠ x)
    (τ0 τ1 τ2 : Tet)
    (hτ0 : τ0 ∈ K.tets) (hτ1 : τ1 ∈ K.tets) (hτ2 : τ2 ∈ K.tets)
    (hτ01 : τ0 ≠ τ1) (hτ02 : τ0 ≠ τ2) (hτ12 : τ1 ≠ τ2)
    (hv0 : v ∈ τ0.verts) (hv1 : v ∈ τ1.verts) (hv2 : v ∈ τ2.verts)
    (hx0 : x ∈ τ0.verts) (hx1 : x ∈ τ1.verts) (hx2 : x ∈ τ2.verts)
    (hb0 : b ∈ τ0.verts) (hb1 : b ∈ τ1.verts)
    (hc0 : c ∈ τ0.verts) (hc2 : c ∈ τ2.verts)
    (hz1 : z ∈ τ1.verts) (hz2 : z ∈ τ2.verts) :
    ∃ σ0 σ1 σ2 :
        {σ : LinkTriangle // σ ∈ vertexLinkStarTriangles K v x},
      (vertexLinkStarGraph K v x).Adj σ0 σ1 ∧
      (vertexLinkStarGraph K v x).Adj σ0 σ2 ∧
      (vertexLinkStarGraph K v x).Adj σ1 σ2 := by
  obtain ⟨σ0, hExtract0, hmem0⟩ :=
    threeCorner_extractStarTriangle v x τ0 hτ0 hv0 hxv hx0
  obtain ⟨σ1, hExtract1, hmem1⟩ :=
    threeCorner_extractStarTriangle v x τ1 hτ1 hv1 hxv hx1
  obtain ⟨σ2, hExtract2, hmem2⟩ :=
    threeCorner_extractStarTriangle v x τ2 hτ2 hv2 hxv hx2
  have hσ0 : σ0.1 ∈ vertexLinkTriangles K v :=
    ((mem_vertexLinkStarTriangles_iff K v x σ0.1).1 σ0.2).1
  have hσ1 : σ1.1 ∈ vertexLinkTriangles K v :=
    ((mem_vertexLinkStarTriangles_iff K v x σ1.1).1 σ1.2).1
  have hσ2 : σ2.1 ∈ vertexLinkTriangles K v :=
    ((mem_vertexLinkStarTriangles_iff K v x σ2.1).1 σ2.2).1
  have hne01 : σ0 ≠ σ1 := by
    intro heq
    exact (threeCorner_extractedTriangles_ne hcore hτ0 hτ1
      hσ0 hσ1 hExtract0 hExtract1 hτ01)
      (congrArg Subtype.val heq)
  have hne02 : σ0 ≠ σ2 := by
    intro heq
    exact (threeCorner_extractedTriangles_ne hcore hτ0 hτ2
      hσ0 hσ2 hExtract0 hExtract2 hτ02)
      (congrArg Subtype.val heq)
  have hne12 : σ1 ≠ σ2 := by
    intro heq
    exact (threeCorner_extractedTriangles_ne hcore hτ1 hτ2
      hσ1 hσ2 hExtract1 hExtract2 hτ12)
      (congrArg Subtype.val heq)
  refine ⟨σ0, σ1, σ2, ?_, ?_, ?_⟩
  · apply (vertexLinkStarGraph_adj K v x σ0 σ1).2
    exact ⟨hne01, σ0.2, σ1.2, b, hbx,
      hmem0 b hbv hb0, hmem1 b hbv hb1⟩
  · apply (vertexLinkStarGraph_adj K v x σ0 σ2).2
    exact ⟨hne02, σ0.2, σ2.2, c, hcx,
      hmem0 c hcv hc0, hmem2 c hcv hc2⟩
  · apply (vertexLinkStarGraph_adj K v x σ1 σ2).2
    exact ⟨hne12, σ1.2, σ2.2, z, hzx,
      hmem1 z hzv hz1, hmem2 z hzv hz2⟩

/-- Source-local use of the existing *private* cyclic-fan triangle lemma.
The three links above, when a cyclic fan covers the whole star, imply exact
incidence 3. Honest manifoldness is used only to supply that covering fan. -/
theorem ClosedTriangulationCore.threeCorner_edgeIncidence_eq_three
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (v x b c z : Nat)
    (hxv : x ≠ v)
    (hbv : b ≠ v) (hcv : c ≠ v) (hzv : z ≠ v)
    (hbx : b ≠ x) (hcx : c ≠ x) (hzx : z ≠ x)
    (τ0 τ1 τ2 : Tet)
    (hτ0 : τ0 ∈ K.tets) (hτ1 : τ1 ∈ K.tets) (hτ2 : τ2 ∈ K.tets)
    (hτ01 : τ0 ≠ τ1) (hτ02 : τ0 ≠ τ2) (hτ12 : τ1 ≠ τ2)
    (hv0 : v ∈ τ0.verts) (hv1 : v ∈ τ1.verts) (hv2 : v ∈ τ2.verts)
    (hx0 : x ∈ τ0.verts) (hx1 : x ∈ τ1.verts) (hx2 : x ∈ τ2.verts)
    (hb0 : b ∈ τ0.verts) (hb1 : b ∈ τ1.verts)
    (hc0 : c ∈ τ0.verts) (hc2 : c ∈ τ2.verts)
    (hz1 : z ∈ τ1.verts) (hz2 : z ∈ τ2.verts) :
    (K.tets.filter (fun τ => v ∈ τ.verts ∧ x ∈ τ.verts)).length = 3 := by
  obtain ⟨σ0, σ1, σ2, h01, h02, h12⟩ :=
    hcore.threeCorner_linkStarTriangle v x b c z hxv
      hbv hcv hzv hbx hcx hzx
      τ0 τ1 τ2 hτ0 hτ1 hτ2 hτ01 hτ02 hτ12
      hv0 hv1 hv2 hx0 hx1 hx2 hb0 hb1 hc0 hc2 hz1 hz2
  have hrep : VertexLinkVertexRepresented K v x :=
    (vertexLinkVertexRepresented_iff_star_nonempty K v x).2
      ⟨σ0.1, σ0.2⟩
  obtain ⟨F⟩ :=
    hcore.exists_ambientEdgeCyclicFan_of_topologicalThreeManifold hM hrep
  have hstar : (vertexLinkStarTriangles K v x).length = 3 :=
    F.star_length_eq_three_of_triangle hcore
      (hcore.vertexLinkStarDegreeTwo hrep) h01 h02 h12
  rw [hcore.vertexLinkStarTriangles_length_eq_edgeIncidence v x hxv.symm] at hstar
  exact hstar

/-- The high-spoke contradiction is now mere arithmetic. -/
theorem ClosedTriangulationCore.no_high_spoke_threeCorner
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (v x b c z : Nat)
    (hxv : x ≠ v)
    (hbv : b ≠ v) (hcv : c ≠ v) (hzv : z ≠ v)
    (hbx : b ≠ x) (hcx : c ≠ x) (hzx : z ≠ x)
    (τ0 τ1 τ2 : Tet)
    (hτ0 : τ0 ∈ K.tets) (hτ1 : τ1 ∈ K.tets) (hτ2 : τ2 ∈ K.tets)
    (hτ01 : τ0 ≠ τ1) (hτ02 : τ0 ≠ τ2) (hτ12 : τ1 ≠ τ2)
    (hv0 : v ∈ τ0.verts) (hv1 : v ∈ τ1.verts) (hv2 : v ∈ τ2.verts)
    (hx0 : x ∈ τ0.verts) (hx1 : x ∈ τ1.verts) (hx2 : x ∈ τ2.verts)
    (hb0 : b ∈ τ0.verts) (hb1 : b ∈ τ1.verts)
    (hc0 : c ∈ τ0.verts) (hc2 : c ∈ τ2.verts)
    (hz1 : z ∈ τ1.verts) (hz2 : z ∈ τ2.verts)
    (hhigh : 4 ≤ (K.tets.filter (fun τ =>
      v ∈ τ.verts ∧ x ∈ τ.verts)).length) : False := by
  have hthree :=
    hcore.threeCorner_edgeIncidence_eq_three hM v x b c z hxv
      hbv hcv hzv hbx hcx hzx
      τ0 τ1 τ2 hτ0 hτ1 hτ2 hτ01 hτ02 hτ12
      hv0 hv1 hv2 hx0 hx1 hx2 hb0 hb1 hc0 hc2 hz1 hz2
  omega

/-- The precise source-local separation corollary.  The second external
corner is allowed a differently named transverse vertex `y`.  Equal
transverses would produce the forbidden high-spoke 3-clique. -/
theorem ClosedTriangulationCore.threeCorner_transverses_ne_of_high_spoke
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (v x b c z y : Nat)
    (hxv : x ≠ v)
    (hbv : b ≠ v) (hcv : c ≠ v) (hzv : z ≠ v)
    (hbx : b ≠ x) (hcx : c ≠ x) (hzx : z ≠ x)
    (τ0 τ1 τ2 : Tet)
    (hτ0 : τ0 ∈ K.tets) (hτ1 : τ1 ∈ K.tets) (hτ2 : τ2 ∈ K.tets)
    (hτ01 : τ0 ≠ τ1) (hτ02 : τ0 ≠ τ2) (hτ12 : τ1 ≠ τ2)
    (hv0 : v ∈ τ0.verts) (hv1 : v ∈ τ1.verts) (hv2 : v ∈ τ2.verts)
    (hx0 : x ∈ τ0.verts) (hx1 : x ∈ τ1.verts) (hx2 : x ∈ τ2.verts)
    (hb0 : b ∈ τ0.verts) (hb1 : b ∈ τ1.verts)
    (hc0 : c ∈ τ0.verts) (hc2 : c ∈ τ2.verts)
    (hz1 : z ∈ τ1.verts) (hy2 : y ∈ τ2.verts)
    (hhigh : 4 ≤ (K.tets.filter (fun τ =>
      v ∈ τ.verts ∧ x ∈ τ.verts)).length) : z ≠ y := by
  intro heq
  subst y
  exact hcore.no_high_spoke_threeCorner hM v x b c z hxv
    hbv hcv hzv hbx hcx hzx
    τ0 τ1 τ2 hτ0 hτ1 hτ2 hτ01 hτ02 hτ12
    hv0 hv1 hv2 hx0 hx1 hx2 hb0 hb1 hc0 hc2 hz1 hy2 hhigh