import Poincare.GlobalFanReentryModeLinkedStep

namespace Poincare

/-- Exact original U(16) 104-facet input from Zenodo 21980010,
PachnerDCG-1.0.0_1.zip, certificates/unflippable-complexes/u16-plus/input.json.
This is data only, not a sphere-recognition or cycle-exclusion theorem. -/
def zenodoU16Original : Triangulation :=
  { tets :=
      [⟨1, 2, 3, 6⟩, ⟨1, 2, 3, 9⟩, ⟨1, 2, 5, 10⟩, ⟨1, 2, 5, 16⟩,
       ⟨1, 2, 6, 8⟩, ⟨1, 2, 8, 16⟩, ⟨1, 2, 9, 10⟩, ⟨1, 3, 6, 13⟩,
       ⟨1, 3, 9, 12⟩, ⟨1, 3, 12, 13⟩, ⟨1, 4, 9, 11⟩, ⟨1, 4, 9, 16⟩,
       ⟨1, 4, 11, 15⟩, ⟨1, 4, 15, 16⟩, ⟨1, 5, 7, 10⟩, ⟨1, 5, 7, 16⟩,
       ⟨1, 6, 8, 14⟩, ⟨1, 6, 13, 14⟩, ⟨1, 7, 10, 15⟩, ⟨1, 7, 15, 16⟩,
       ⟨1, 8, 9, 12⟩, ⟨1, 8, 9, 16⟩, ⟨1, 8, 12, 14⟩, ⟨1, 9, 10, 11⟩,
       ⟨1, 10, 11, 15⟩, ⟨1, 12, 13, 14⟩, ⟨2, 3, 4, 7⟩, ⟨2, 3, 4, 10⟩,
       ⟨2, 3, 6, 11⟩, ⟨2, 3, 7, 9⟩, ⟨2, 3, 10, 11⟩, ⟨2, 4, 7, 14⟩,
       ⟨2, 4, 10, 13⟩, ⟨2, 4, 13, 14⟩, ⟨2, 5, 10, 12⟩, ⟨2, 5, 12, 16⟩,
       ⟨2, 6, 8, 11⟩, ⟨2, 7, 9, 15⟩, ⟨2, 7, 14, 15⟩, ⟨2, 8, 11, 16⟩,
       ⟨2, 9, 10, 13⟩, ⟨2, 9, 13, 15⟩, ⟨2, 10, 11, 12⟩, ⟨2, 11, 12, 16⟩,
       ⟨2, 13, 14, 15⟩, ⟨3, 4, 5, 8⟩, ⟨3, 4, 5, 11⟩, ⟨3, 4, 7, 12⟩,
       ⟨3, 4, 8, 10⟩, ⟨3, 4, 11, 12⟩, ⟨3, 5, 8, 15⟩, ⟨3, 5, 11, 14⟩,
       ⟨3, 5, 14, 15⟩, ⟨3, 6, 11, 13⟩, ⟨3, 7, 9, 12⟩, ⟨3, 8, 10, 16⟩,
       ⟨3, 8, 15, 16⟩, ⟨3, 10, 11, 14⟩, ⟨3, 10, 14, 16⟩, ⟨3, 11, 12, 13⟩,
       ⟨3, 14, 15, 16⟩, ⟨4, 5, 6, 9⟩, ⟨4, 5, 6, 12⟩, ⟨4, 5, 8, 13⟩,
       ⟨4, 5, 9, 11⟩, ⟨4, 5, 12, 13⟩, ⟨4, 6, 9, 16⟩, ⟨4, 6, 12, 15⟩,
       ⟨4, 6, 15, 16⟩, ⟨4, 7, 12, 14⟩, ⟨4, 8, 10, 13⟩, ⟨4, 11, 12, 15⟩,
       ⟨4, 12, 13, 14⟩, ⟨5, 6, 7, 10⟩, ⟨5, 6, 7, 13⟩, ⟨5, 6, 9, 14⟩,
       ⟨5, 6, 10, 12⟩, ⟨5, 6, 13, 14⟩, ⟨5, 7, 13, 16⟩, ⟨5, 8, 13, 15⟩,
       ⟨5, 9, 11, 14⟩, ⟨5, 12, 13, 16⟩, ⟨5, 13, 14, 15⟩, ⟨6, 7, 8, 11⟩,
       ⟨6, 7, 8, 14⟩, ⟨6, 7, 10, 15⟩, ⟨6, 7, 11, 13⟩, ⟨6, 7, 14, 15⟩,
       ⟨6, 9, 14, 16⟩, ⟨6, 10, 12, 15⟩, ⟨6, 14, 15, 16⟩, ⟨7, 8, 9, 12⟩,
       ⟨7, 8, 9, 15⟩, ⟨7, 8, 11, 16⟩, ⟨7, 8, 12, 14⟩, ⟨7, 8, 15, 16⟩,
       ⟨7, 11, 13, 16⟩, ⟨8, 9, 10, 13⟩, ⟨8, 9, 10, 16⟩, ⟨8, 9, 13, 15⟩,
       ⟨9, 10, 11, 14⟩, ⟨9, 10, 14, 16⟩, ⟨10, 11, 12, 15⟩, ⟨11, 12, 13, 16⟩] }


/-- Concrete first high-fan state of the archived U(16) cycle:
central edge (1,5), chord (2,7), transverse vertex 10.
All geometric data come from the fixed 104-tetrahedron input, without a
manifold-recognition or no-descent assumption. -/
theorem zenodoU16_first_highFan :
    ∃ q : HighFanState zenodoU16Original,
      q.v = 1 ∧ q.x = 5 ∧
      q.transition.z0 = 2 ∧ q.transition.z1 = 7 := by
  let K : Triangulation := zenodoU16Original
  let t0 : LinkTriangle := ⟨3, 4, 7⟩
  let t1 : LinkTriangle := ⟨3, 7, 9⟩
  let t2 : LinkTriangle := ⟨7, 9, 15⟩
  let t3 : LinkTriangle := ⟨7, 14, 15⟩
  let t4 : LinkTriangle := ⟨4, 7, 14⟩
  have hstar :
      vertexLinkStarTriangles K 2 7 = [t0, t1, t4, t2, t3] := by
    decide
  have hm0 : t0 ∈ vertexLinkStarTriangles K 2 7 := by decide
  have hm1 : t1 ∈ vertexLinkStarTriangles K 2 7 := by decide
  have hm2 : t2 ∈ vertexLinkStarTriangles K 2 7 := by decide
  have hm3 : t3 ∈ vertexLinkStarTriangles K 2 7 := by decide
  have hm4 : t4 ∈ vertexLinkStarTriangles K 2 7 := by decide
  let s0 : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K 2 7} := ⟨t0, hm0⟩
  let s1 : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K 2 7} := ⟨t1, hm1⟩
  let s2 : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K 2 7} := ⟨t2, hm2⟩
  let s3 : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K 2 7} := ⟨t3, hm3⟩
  let s4 : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K 2 7} := ⟨t4, hm4⟩
  have h01 : (vertexLinkStarGraph K 2 7).Adj s0 s1 := by
    rw [vertexLinkStarGraph_adj]
    exact ⟨by simp [s0, s1, t0, t1],
      ⟨hm0, hm1, 3, by decide,
        by simp [s0, t0, LinkTriangle.verts],
        by simp [s1, t1, LinkTriangle.verts]⟩⟩
  have h12 : (vertexLinkStarGraph K 2 7).Adj s1 s2 := by
    rw [vertexLinkStarGraph_adj]
    exact ⟨by decide, ⟨hm1, hm2, 9, by decide, by decide, by decide⟩⟩
  have h23 : (vertexLinkStarGraph K 2 7).Adj s2 s3 := by
    rw [vertexLinkStarGraph_adj]
    exact ⟨by decide, ⟨hm2, hm3, 15, by decide, by decide, by decide⟩⟩
  have h34 : (vertexLinkStarGraph K 2 7).Adj s3 s4 := by
    rw [vertexLinkStarGraph_adj]
    exact ⟨by decide, ⟨hm3, hm4, 14, by decide, by decide, by decide⟩⟩
  have h40 : (vertexLinkStarGraph K 2 7).Adj s4 s0 := by
    rw [vertexLinkStarGraph_adj]
    exact ⟨by decide, ⟨hm4, hm0, 4, by decide, by decide, by decide⟩⟩
  let W : (vertexLinkStarGraph K 2 7).Walk s0 s0 :=
    .cons h01 (.cons h12 (.cons h23 (.cons h34 (.cons h40 .nil))))
  have hcycle : W.IsCycle := by
    refine ⟨⟨⟨by decide⟩, ?_⟩, ?_⟩
    · intro h
      cases h
    · decide
  have hcover : ∀ s : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K 2 7},
      s ∈ W.support := by
    intro s
    have hs : s.1 ∈ [t0, t1, t4, t2, t3] := by
      simpa only [hstar] using s.2
    simp only [List.mem_cons, List.mem_singleton] at hs
    rcases hs with h | h | h | h | h
    · have heq : s = s0 := Subtype.ext h
      subst s
      simp [W]
    · have heq : s = s1 := Subtype.ext h
      subst s
      simp [W]
    · have heq : s = s4 := Subtype.ext h
      subst s
      simp [W]
    · have heq : s = s2 := Subtype.ext h
      subst s
      simp [W]
    · have heq : s = s3 := Subtype.ext h
      subst s
      simp [W]
  let tetAt (s : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K 2 7}) : Tet :=
    ⟨2, s.1.v0, s.1.v1, s.1.v2⟩
  have htetmem : ∀ s, tetAt s ∈ K.tets := by
    intro s
    have hs : s.1 ∈ [t0, t1, t4, t2, t3] := by
      simpa only [hstar] using s.2
    simp only [List.mem_cons, List.mem_singleton] at hs
    rcases hs with h | h | h | h | h
    · have heq : s = s0 := Subtype.ext h
      subst s
      decide
    · have heq : s = s1 := Subtype.ext h
      subst s
      decide
    · have heq : s = s4 := Subtype.ext h
      subst s
      decide
    · have heq : s = s2 := Subtype.ext h
      subst s
      decide
    · have heq : s = s3 := Subtype.ext h
      subst s
      decide
  have htetlink : ∀ s, (tetAt s).linkTriangleAt? 2 = some s.1 := by
    intro s
    rfl
  have htetinj : Function.Injective tetAt := by
    intro s t h
    apply Subtype.ext
    have hs := congrArg (fun tau : Tet => tau.linkTriangleAt? 2) h
    simpa only [htetlink] using Option.some.inj hs
  have hfilter :
      (K.tets.filter (fun tau => 2 ∈ tau.verts ∧ 7 ∈ tau.verts)) =
        [⟨2, 3, 4, 7⟩, ⟨2, 3, 7, 9⟩, ⟨2, 4, 7, 14⟩,
         ⟨2, 7, 9, 15⟩, ⟨2, 7, 14, 15⟩] := by
    decide
  have hambient : ∀ tau ∈ K.tets,
      2 ∈ tau.verts → 7 ∈ tau.verts →
        ∃ s, tetAt s = tau := by
    intro tau htau hv hx
    have ht : tau ∈
        (K.tets.filter (fun t => 2 ∈ t.verts ∧ 7 ∈ t.verts)) :=
      List.mem_filter.mpr ⟨htau, ⟨hv, hx⟩⟩
    rw [hfilter] at ht
    simp only [List.mem_cons, List.mem_singleton] at ht
    rcases ht with h | h | h | h | h
    · refine ⟨s0, ?_⟩
      subst tau
      rfl
    · refine ⟨s1, ?_⟩
      subst tau
      rfl
    · refine ⟨s4, ?_⟩
      subst tau
      rfl
    · refine ⟨s2, ?_⟩
      subst tau
      rfl
    · refine ⟨s3, ?_⟩
      subst tau
      rfl
  let F : AmbientEdgeCyclicFan K 2 7 := {
    start := s0
    walk := W
    isCycle := hcycle
    length_ge_three := by decide
    covers := hcover
    tetAt := tetAt
    tetAt_mem := htetmem
    tetAt_link := htetlink
    tetAt_injective := htetinj
    covers_ambient := hambient
  }
  have h2 : 2 ∈ vertexSupport K := by decide
  have h7 : 7 ∈ vertexSupport K := by decide
  have hne : 2 ≠ 7 := by decide
  let sig : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K 1 5} :=
    ⟨⟨2, 5, 10⟩, by decide⟩
  let rho : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K 1 5} :=
    ⟨⟨5, 7, 10⟩, by decide⟩
  have hadj : (vertexLinkStarGraph K 1 5).Adj sig rho := by
    rw [vertexLinkStarGraph_adj]
    exact ⟨by decide,
      ⟨sig.2, rho.2, 10, by decide, by decide, by decide⟩⟩
  have hleft : SameTetVertices (⟨1, 2, 5, 10⟩ : Tet)
      ⟨1, 5, 10, 2⟩ := by
    intro v
    simp [Tet.verts]
    tauto
  have hright : SameTetVertices (⟨1, 5, 7, 10⟩ : Tet)
      ⟨1, 5, 10, 7⟩ := by
    intro v
    simp [Tet.verts]
    tauto
  refine ⟨{
    v := 1
    x := 5
    v_supported := by decide
    x_supported := by decide
    endpoints_ne := by decide
    transition := {
      z0 := 2
      z1 := 7
      endpoints_ne := hne
      z0_supported := h2
      z1_supported := h7
      edgeState := supportedEdgeStateOfDistinct K 2 7 h2 h7 hne
      edgeState_eq := rfl
      sigma := sig
      rho := rho
      adjacent := hadj
      witness := ⟨2, 3, 4, 7⟩
      witness_mem := by decide
      z0_mem := by decide
      z1_mem := by decide
      escapes_old_edge := Or.inl (by decide)
      incidence := Or.inr ⟨by decide, ⟨F⟩⟩
      transverse := 10
      leftTet := ⟨1, 2, 5, 10⟩
      rightTet := ⟨1, 5, 7, 10⟩
      leftTet_mem := by decide
      rightTet_mem := by decide
      leftTet_link := by decide
      rightTet_link := by decide
      leftTet_match := hleft
      rightTet_match := hright
      distinct := by decide
    }
  }, rfl, rfl, rfl, rfl⟩

end Poincare
