import Poincare.AscentBarrierInvariant

namespace Poincare

/-- The literal forward 1→4 replacement of any specified tetrahedron.
This is a combinatorial candidate, not a certified legal step: preservation
of the closed core and an inverse legal 4→1 certificate are still required. -/
def tetrahedronOneFourReplacement
    (K : Triangulation) (source : Tet) (e : Nat) : Triangulation :=
  { tets :=
      [⟨source.v0, source.v1, source.v2, e⟩,
       ⟨source.v0, source.v1, source.v3, e⟩,
       ⟨source.v0, source.v2, source.v3, e⟩,
       ⟨source.v1, source.v2, source.v3, e⟩] ++
      eraseFirstSameTet source K.tets }

/-- Equality orientation for the four outer vertices of a tetrahedron:
freshness in the source vertex list gives inequalities with the new vertex
on the right.  This does not establish closed-core preservation. -/
theorem tetrahedronOneFour_source_ne_fresh
    (source : Tet) (e : Nat)
    (hfresh : e ∉ source.verts) :
    source.v0 ≠ e ∧ source.v1 ≠ e ∧
    source.v2 ≠ e ∧ source.v3 ≠ e := by
  have h : e ≠ source.v0 ∧ e ≠ source.v1 ∧
      e ≠ source.v2 ∧ e ≠ source.v3 := by
    simpa [Tet.verts] using hfresh
  exact ⟨Ne.symm h.1, Ne.symm h.2.1,
    Ne.symm h.2.2.1, Ne.symm h.2.2.2⟩

/-- A fresh vertex inserted into a nondegenerate represented tetrahedron
produces only nondegenerate tetrahedra.  Full closed-core preservation still
requires distinct tetrahedron vertex sets and exact face-incidence counts. -/
theorem tetrahedronOneFourReplacement_nodup
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (source : Tet) (hsource : source ∈ K.tets)
    (e : Nat) (hfresh : e ∉ vertexSupport K) :
    ∀ τ ∈ (tetrahedronOneFourReplacement K source e).tets,
      τ.verts.Nodup := by
  have hs : source.verts.Nodup := hcore.1 source hsource
  have heSrc : e ∉ source.verts := by
    intro h
    apply hfresh
    apply (mem_vertexSupport_iff K e).2
    exact List.mem_flatMap.mpr ⟨source, hsource, h⟩
  have hne := tetrahedronOneFour_source_ne_fresh source e heSrc
  intro τ hτ
  simp only [tetrahedronOneFourReplacement, List.mem_append] at hτ
  rcases hτ with hnew | hold
  · simp only [List.mem_cons] at hnew
    rcases hnew with rfl | rfl | rfl | rfl | hnil <;>
      simp_all [Tet.verts, List.nodup_cons]
  · exact hcore.1 τ (mem_of_mem_eraseFirstSameTet hold)

/-- Fresh 1→4 insertion preserves uniqueness of represented tetrahedron
vertex sets.  This is the second closed-core component; triangular-face
incidence is a separate obligation. -/
theorem tetrahedronOneFourReplacement_pairwise
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (source : Tet) (hsource : source ∈ K.tets)
    (e : Nat) (hfresh : e ∉ vertexSupport K) :
    (tetrahedronOneFourReplacement K source e).tets.Pairwise
      (fun τ σ => ¬ SameTetVertices τ σ) := by
  let t0 : Tet := ⟨source.v0, source.v1, source.v2, e⟩
  let t1 : Tet := ⟨source.v0, source.v1, source.v3, e⟩
  let t2 : Tet := ⟨source.v0, source.v2, source.v3, e⟩
  let t3 : Tet := ⟨source.v1, source.v2, source.v3, e⟩
  let rest := eraseFirstSameTet source K.tets
  have hrest : rest.Pairwise (fun τ σ => ¬ SameTetVertices τ σ) := by
    exact hcore.2.1.sublist (eraseFirstSameTet_sublist source K.tets)
  have heSrc : e ∉ source.verts := by
    intro he
    exact hfresh ((mem_vertexSupport_iff K e).2
      (List.mem_flatMap.mpr ⟨source, hsource, he⟩))
  have hne := tetrahedronOneFour_source_ne_fresh source e heSrc
  have hd := hcore.1 source hsource
  simp [Tet.verts] at hd
  have hlocal : [t0, t1, t2, t3].Pairwise
      (fun τ σ => ¬ SameTetVertices τ σ) := by
    simp only [List.pairwise_cons, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · intro τ hτ
      rcases hτ with rfl | rfl | rfl
      · intro h
        have hx := (h source.v2).1 (by simp [t0, Tet.verts])
        simp [t1, Tet.verts] at hx
        aesop
      · intro h
        have hx := (h source.v1).1 (by simp [t0, Tet.verts])
        simp [t2, Tet.verts] at hx
        aesop
      · intro h
        have hx := (h source.v0).1 (by simp [t0, Tet.verts])
        simp [t3, Tet.verts] at hx
        aesop
    constructor
    · intro τ hτ
      rcases hτ with rfl | rfl
      · intro h
        have hx := (h source.v1).1 (by simp [t1, Tet.verts])
        simp [t2, Tet.verts] at hx
        aesop
      · intro h
        have hx := (h source.v0).1 (by simp [t1, Tet.verts])
        simp [t3, Tet.verts] at hx
        aesop
    constructor
    · intro τ hτ
      rcases hτ with rfl
      intro h
      have hx := (h source.v0).1 (by simp [t2, Tet.verts])
      simp [t3, Tet.verts] at hx
      aesop
    · simp
  have hcross (n : Tet) (hn : n ∈ [t0, t1, t2, t3])
      (τ : Tet) (hτ : τ ∈ rest) : ¬ SameTetVertices n τ := by
    intro hsame
    have heNew : e ∈ n.verts := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;>
        simp [t0, t1, t2, t3, Tet.verts]
    have heOld : e ∈ τ.verts := (hsame e).1 heNew
    apply hfresh
    apply (mem_vertexSupport_iff K e).2
    exact List.mem_flatMap.mpr
      ⟨τ, mem_of_mem_eraseFirstSameTet hτ, heOld⟩
  simp only [List.pairwise_cons] at hlocal
  change (t0 :: t1 :: t2 :: t3 :: rest).Pairwise
    (fun τ σ => ¬ SameTetVertices τ σ)
  simp only [List.pairwise_cons]
  refine ⟨?_, ?_, ?_, ?_, hrest⟩
  · intro τ hτ
    simp only [List.mem_cons] at hτ
    rcases hτ with rfl | rfl | rfl | hτ
    · exact hlocal.1 t1 (by simp)
    · exact hlocal.1 t2 (by simp)
    · exact hlocal.1 t3 (by simp)
    · exact hcross t0 (by simp) τ hτ
  · intro τ hτ
    simp only [List.mem_cons] at hτ
    rcases hτ with rfl | rfl | hτ
    · exact hlocal.2.1 t2 (by simp)
    · exact hlocal.2.1 t3 (by simp)
    · exact hcross t1 (by simp) τ hτ
  · intro τ hτ
    simp only [List.mem_cons] at hτ
    rcases hτ with rfl | hτ
    · exact hlocal.2.2.1 t3 (by simp)
    · exact hcross t2 (by simp) τ hτ
  · intro τ hτ
    exact hcross t3 (by simp) τ hτ

/-- Replacing any represented tetrahedron by its four fresh-center
subtetrahedra preserves exact two-fold incidence of every represented
nondegenerate triangular face. -/
theorem tetrahedronOneFourReplacement_face_incidence
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (source : Tet) (hsource : source ∈ K.tets)
    (e : Nat) (hfresh : e ∉ vertexSupport K) :
    ∀ x y z : Nat,
      [x, y, z].Nodup →
      (∃ τ ∈ (tetrahedronOneFourReplacement K source e).tets,
        x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts) →
      ((tetrahedronOneFourReplacement K source e).tets.filter
        (fun τ => x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts)).length = 2 := by
  classical
  let N : List Tet :=
    [⟨source.v0, source.v1, source.v2, e⟩,
     ⟨source.v0, source.v1, source.v3, e⟩,
     ⟨source.v0, source.v2, source.v3, e⟩,
     ⟨source.v1, source.v2, source.v3, e⟩]
  let U : List Tet := eraseFirstSameTet source K.tets
  have hs : source.verts.Nodup := hcore.1 source hsource
  have heSrc : e ∉ source.verts := by
    intro he
    exact hfresh ((mem_vertexSupport_iff K e).2
      (List.mem_flatMap.mpr ⟨source, hsource, he⟩))
  have hne := tetrahedronOneFour_source_ne_fresh source e heSrc
  have hd := hs
  simp [Tet.verts] at hd
  have hnotOld : ∀ τ ∈ K.tets, e ∉ τ.verts := by
    intro τ hτ he
    exact hfresh ((mem_vertexSupport_iff K e).2
      (List.mem_flatMap.mpr ⟨τ, hτ, he⟩))
  intro x y z hxyz hrepresented
  let p : Tet → Prop := fun τ =>
    x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts
  have hinvariant : ∀ τ σ, SameTetVertices τ σ → (p τ ↔ p σ) := by
    intro τ σ hsame
    simp only [p]
    constructor <;> intro h
    · exact ⟨(hsame x).1 h.1, (hsame y).1 h.2.1, (hsame z).1 h.2.2⟩
    · exact ⟨(hsame x).2 h.1, (hsame y).2 h.2.1, (hsame z).2 h.2.2⟩
  have hfilter (L : List Tet) :
      (L.filter p).length =
        (L.filter fun τ => τ.ContainsTriple x y z).length := by
    congr 2
    funext τ
    simp [p, Tet.ContainsTriple]
  have hsplit :
      (U.filter p).length + (if p source then 1 else 0) =
        (K.tets.filter p).length := by
    by_cases hp : p source
    · simpa [U, hp] using
        (eraseFirstSameTet_filter_length_add_one_eq p source K.tets
          hinvariant ⟨source, hsource, sameTetVertices_refl source⟩ hp)
    · simpa [U, hp] using
        (eraseFirstSameTet_filter_length_eq_of_not
          p source K.tets hinvariant hp)
  have hnewCount {n : Tet} (hn : n ∈ N) (hp : p n) :
      (N.filter p).length =
        (if e ∈ [x, y, z] then 2 else 1) := by
    have hx := hp.1
    have hy := hp.2.1
    have hz := hp.2.2
    simp only [N, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    all_goals
      rcases Tet.distinct_triple_face_cases _ x y z hxyz hx hy hz with
        hface | hface | hface | hface
      all_goals
        rw [hfilter N,
          filter_containsTriple_length_eq_of_sameTripleVertices N hface]
        have heFace := hface e
        simp only [List.mem_cons, List.not_mem_nil, or_false] at heFace
        simp_all [N, Tet.ContainsTriple, Tet.verts, eq_comm]
  have hnewImpliesSource
      (hneFace : e ∉ [x, y, z])
      {n : Tet} (hn : n ∈ N) (hp : p n) : p source := by
    have hsubset {v : Nat} (hv : v ∈ n.verts) :
        v ∈ source.verts ∨ v = e := by
      simp only [N, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;>
        simp only [Tet.verts, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢ <;> aesop
    have hnot : x ≠ e ∧ y ≠ e ∧ z ≠ e := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hneFace
      exact ⟨fun h => hneFace (Or.inl h.symm),
        fun h => hneFace (Or.inr (Or.inl h.symm)),
        fun h => hneFace (Or.inr (Or.inr h.symm))⟩
    refine ⟨?_, ?_, ?_⟩
    · rcases hsubset hp.1 with hx | hx
      · exact hx
      · exact (hnot.1 hx).elim
    · rcases hsubset hp.2.1 with hy | hy
      · exact hy
      · exact (hnot.2.1 hy).elim
    · rcases hsubset hp.2.2 with hz | hz
      · exact hz
      · exact (hnot.2.2 hz).elim
  have hnewIfSource (hp : p source) :
      (N.filter p).length = 1 := by
    rcases Tet.distinct_triple_face_cases source x y z hxyz
      hp.1 hp.2.1 hp.2.2 with hface | hface | hface | hface
    all_goals
      rw [hfilter N,
        filter_containsTriple_length_eq_of_sameTripleVertices N hface]
      simp_all [N, Tet.ContainsTriple, Tet.verts, eq_comm]
  change ((N ++ U).filter p).length = 2
  rw [List.filter_append, List.length_append]
  by_cases he : e ∈ [x, y, z]
  · have hUnot : ∀ τ ∈ U, ¬ p τ := by
      intro τ hτ hp
      have hnot := hnotOld τ (mem_of_mem_eraseFirstSameTet hτ)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hnot hp.1
      · exact hnot hp.2.1
      · exact hnot hp.2.2
    have hUzero : (U.filter p).length = 0 := by
      have hempty : U.filter p = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro τ hτ
        rcases List.mem_filter.mp hτ with ⟨hmem, hp⟩
        exact hUnot τ hmem (of_decide_eq_true hp)
      simp [hempty]
    rcases hrepresented with ⟨τ, hτ, hp⟩
    change τ ∈ N ++ U at hτ
    rcases List.mem_append.mp hτ with hn | hu
    · have hcount := hnewCount hn hp
      simp [he, hUzero] at hcount ⊢
      exact hcount
    · exact (hUnot τ hu hp).elim
  · by_cases hpSource : p source
    · have hKcount : (K.tets.filter p).length = 2 :=
        hcore.2.2 x y z hxyz ⟨source, hsource, hpSource⟩
      have hNcount := hnewIfSource hpSource
      omega
    · have hNzero : (N.filter p).length = 0 := by
        have hempty : N.filter p = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro n hn
          rcases List.mem_filter.mp hn with ⟨hmem, hp⟩
          exact hpSource (hnewImpliesSource he hmem (of_decide_eq_true hp))
        simp [hempty]
      rcases hrepresented with ⟨τ, hτ, hp⟩
      change τ ∈ N ++ U at hτ
      rcases List.mem_append.mp hτ with hn | hu
      · exact (hpSource (hnewImpliesSource he hn hp)).elim
      · have hKcount : (K.tets.filter p).length = 2 :=
          hcore.2.2 x y z hxyz
            ⟨τ, mem_of_mem_eraseFirstSameTet hu, hp⟩
        omega

/-- An actual legal bistellar step between closed triangulation cores.
The 1→4 case is the inverse of a certified legal 4→1 replacement,
not the placeholder global `applyMoveImpl`. -/
inductive CertifiedPachnerStep : Triangulation → Triangulation → Prop where
  | move23 {K : Triangulation}
      (hcore : ClosedTriangulationCore K)
      (s : Move23Site) (hlegal : s.LegalIn K) :
      CertifiedPachnerStep K (s.replace K)
  | move32 {K : Triangulation}
      (hcore : ClosedTriangulationCore K)
      (s : Move32Site) (hlegal : s.LegalIn K) :
      CertifiedPachnerStep K (s.replace K)
  | move41 {K : Triangulation}
      (hcore : ClosedTriangulationCore K)
      (s : Move41Site) (hlegal : s.LegalIn K) :
      CertifiedPachnerStep K (s.replace K)
  | move14 {K : Triangulation}
      (hcore : ClosedTriangulationCore K)
      (s : Move41Site) (hlegal : s.LegalIn K) :
      CertifiedPachnerStep (s.replace K) K

theorem CertifiedPachnerStep.homeomorphic
    {K L : Triangulation} (h : CertifiedPachnerStep K L) :
    Nonempty
      (triangulationTopologicalGeometricCarrier K ≃ₜ
        triangulationTopologicalGeometricCarrier L) := by
  cases h with
  | move23 hcore s hlegal =>
      exact ⟨hcore.move23GeometricCarrierHomeomorph s hlegal⟩
  | move32 hcore s hlegal =>
      exact ⟨hcore.move32GeometricCarrierHomeomorph s hlegal⟩
  | move41 hcore s hlegal =>
      exact ⟨hcore.move41GeometricCarrierHomeomorph s hlegal⟩
  | move14 hcore s hlegal =>
      exact ⟨(hcore.move41GeometricCarrierHomeomorph s hlegal).symm⟩

/-- Arbitrary finite legal Pachner histories, including vertex insertion
and any temporary increase in the nonnegative supported defect. -/
inductive CertifiedPachnerPath : Triangulation → Triangulation → Prop where
  | refl (K : Triangulation) : CertifiedPachnerPath K K
  | snoc {K L M : Triangulation}
      (hpath : CertifiedPachnerPath K L)
      (hstep : CertifiedPachnerStep L M) :
      CertifiedPachnerPath K M

/-- Concatenate two finite certified Pachner paths without changing their
endpoints or assuming monotonicity of the intermediate defect. -/
theorem CertifiedPachnerPath.trans
    {K L M : Triangulation}
    (hKL : CertifiedPachnerPath K L)
    (hLM : CertifiedPachnerPath L M) :
    CertifiedPachnerPath K M := by
  induction hLM with
  | refl => exact hKL
  | snoc _ hstep ih =>
      exact CertifiedPachnerPath.snoc ih hstep

theorem CertifiedPachnerPath.homeomorphic
    {K L : Triangulation} (h : CertifiedPachnerPath K L) :
    Nonempty
      (triangulationTopologicalGeometricCarrier K ≃ₜ
        triangulationTopologicalGeometricCarrier L) := by
  induction h with
  | refl =>
      exact ⟨Homeomorph.refl _⟩
  | snoc hpath hstep ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨f⟩ := hstep.homeomorphic
      exact ⟨e.trans f⟩

/-- Proposed universal endpoint descent, allowing arbitrary finite
nonmonotone sequences and certified inverse-4→1 (1→4) stabilizations.
This is an open proposition, NOT an established theorem or axiom. -/
def SimplyConnectedStabilizedPathDescent : Prop :=
  ∀ K : Triangulation,
    ClosedTriangulationCore K →
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K →
    TriangulationRealizationSimplyConnected K →
    0 < PhiSupport K →
    ∃ L : Triangulation,
      ClosedTriangulationCore L ∧
      CertifiedPachnerPath K L ∧
      PhiSupport L < PhiSupport K

/-- A finite certified path with smaller endpoint has the already required
topology-preserving descent property; no unproved global hypothesis is
introduced in this theorem. -/
theorem stabilizedPathDescent_implies_globalDescent
    (hcoverage : SimplyConnectedStabilizedPathDescent) :
    SimplyConnectedGlobalPhiSupportDescent := by
  intro K hcore hM hSC hpos
  obtain ⟨L, hcoreL, hpath, hlt⟩ :=
    hcoverage K hcore hM hSC hpos
  exact ⟨L, hcoreL, hlt, hpath.homeomorphic⟩

/-- Already certified three-move escape instantiates the longer-path
relation, demonstrating that endpoint descent need not be one-step descent. -/
theorem crossPolytopeBoundary4_stabilized_path_escape :
    CertifiedPachnerPath crossPolytopeBoundary4 crossPolytopeEscapeFinal := by
  apply CertifiedPachnerPath.snoc
  · apply CertifiedPachnerPath.snoc
    · apply CertifiedPachnerPath.snoc
      · exact CertifiedPachnerPath.refl crossPolytopeBoundary4
      · exact CertifiedPachnerStep.move23
          crossPolytopeBoundary4_closedCore
          crossPolytopeEscapeMove23 crossPolytopeEscapeMove23_legal
    · exact CertifiedPachnerStep.move32
        crossPolytopeEscapeAfter23_closedCore
        crossPolytopeEscapeMove32₁ crossPolytopeEscapeMove32₁_legal
  · exact CertifiedPachnerStep.move32
      crossPolytopeEscapeAfter32One_closedCore
      crossPolytopeEscapeMove32₂ crossPolytopeEscapeMove32₂_legal

theorem crossPolytopeBoundary4_stabilized_path_strict_descent :
    ∃ L : Triangulation,
      CertifiedPachnerPath crossPolytopeBoundary4 L ∧
      PhiSupport L < PhiSupport crossPolytopeBoundary4 := by
  exact ⟨crossPolytopeEscapeFinal,
    crossPolytopeBoundary4_stabilized_path_escape,
    by rw [crossPolytopeEscapeFinal_PhiSupport,
      crossPolytopeEscapeInitial_PhiSupport]; omega⟩

end Poincare
