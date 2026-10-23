import Poincare.GlobalMove32WitnessedSourceFaceReentry
import Mathlib.Tactic

namespace Poincare

/-- A vertex code whose value belongs to the finite support of K. -/
abbrev FiniteMove32Vertex (K : Triangulation) :=
  ↥((vertexSupport K).toFinset)

/-- A site code with all five coordinates in the represented vertex support. -/
structure Move32SiteCode (K : Triangulation) where
  a : FiniteMove32Vertex K
  b : FiniteMove32Vertex K
  c : FiniteMove32Vertex K
  d : FiniteMove32Vertex K
  e : FiniteMove32Vertex K
  deriving Fintype

/-- Decode finite coordinates into the existing site definition. -/
def Move32SiteCode.decode {K : Triangulation} (q : Move32SiteCode K) : Move32Site :=
  ⟨q.a.1, q.b.1, q.c.1, q.d.1, q.e.1⟩

/-- A vertex occurring in a tetrahedron of K belongs to the finite support. -/
theorem mem_vertexSupport_of_mem_tet
    {K : Triangulation} {t : Tet} (ht : t ∈ K.tets)
    {v : Nat} (hv : v ∈ t.verts) : v ∈ vertexSupport K := by
  rw [mem_vertexSupport_iff]
  simp only [allVerts, List.mem_flatMap]
  exact ⟨t, ht, hv⟩

/-- Each coordinate of a realized site occurs in the finite vertex support. -/
theorem realized_a_mem_vertexSupport
    {K : Triangulation} {s : Move32Site} (hs : s.RealizedIn K) :
    s.a ∈ vertexSupport K := by
  rcases hs with ⟨⟨t, ht, h⟩, _, _⟩
  exact mem_vertexSupport_of_mem_tet ht ((h s.a).2 (by simp [Move32Site.targetTet₀, Tet.verts]))

theorem realized_b_mem_vertexSupport
    {K : Triangulation} {s : Move32Site} (hs : s.RealizedIn K) :
    s.b ∈ vertexSupport K := by
  rcases hs with ⟨⟨t, ht, h⟩, _, _⟩
  exact mem_vertexSupport_of_mem_tet ht ((h s.b).2 (by simp [Move32Site.targetTet₀, Tet.verts]))

theorem realized_c_mem_vertexSupport
    {K : Triangulation} {s : Move32Site} (hs : s.RealizedIn K) :
    s.c ∈ vertexSupport K := by
  rcases hs with ⟨_, ⟨t, ht, h⟩, _⟩
  exact mem_vertexSupport_of_mem_tet ht ((h s.c).2 (by simp [Move32Site.targetTet₁, Tet.verts]))

theorem realized_d_mem_vertexSupport
    {K : Triangulation} {s : Move32Site} (hs : s.RealizedIn K) :
    s.d ∈ vertexSupport K := by
  rcases hs with ⟨⟨t, ht, h⟩, _, _⟩
  exact mem_vertexSupport_of_mem_tet ht ((h s.d).2 (by simp [Move32Site.targetTet₀, Tet.verts]))

theorem realized_e_mem_vertexSupport
    {K : Triangulation} {s : Move32Site} (hs : s.RealizedIn K) :
    s.e ∈ vertexSupport K := by
  rcases hs with ⟨⟨t, ht, h⟩, _, _⟩
  exact mem_vertexSupport_of_mem_tet ht ((h s.e).2 (by simp [Move32Site.targetTet₀, Tet.verts]))

/-- The finite coordinate code associated to a realized site. -/
noncomputable def Move32SiteCode.ofRealized
    {K : Triangulation} (s : Move32Site) (hs : s.RealizedIn K) :
    Move32SiteCode K :=
  ⟨⟨s.a, by simpa using realized_a_mem_vertexSupport hs⟩,
    ⟨s.b, by simpa using realized_b_mem_vertexSupport hs⟩,
    ⟨s.c, by simpa using realized_c_mem_vertexSupport hs⟩,
    ⟨s.d, by simpa using realized_d_mem_vertexSupport hs⟩,
    ⟨s.e, by simpa using realized_e_mem_vertexSupport hs⟩⟩

@[simp] theorem Move32SiteCode.decode_ofRealized
    {K : Triangulation} (s : Move32Site) (hs : s.RealizedIn K) :
    (Move32SiteCode.ofRealized s hs).decode = s := by
  cases s <;> simp [Move32SiteCode.ofRealized, Move32SiteCode.decode]
/-- Finite codes restricted to sites explicitly realized in K. -/
def FiniteRealizedMove32Site (K : Triangulation) :=
  {q : Move32SiteCode K // q.decode.RealizedIn K}

noncomputable instance finiteRealizedMove32SiteFintype (K : Triangulation) :
    Fintype (FiniteRealizedMove32Site K) := by
  classical
  unfold FiniteRealizedMove32Site
  infer_instance


/-- A list member has a finite position whose lookup is that exact member. -/
theorem exists_fin_get_eq_of_mem {α : Type} (l : List α) {a : α}
    (ha : a ∈ l) : ∃ i : Fin l.length, l.get i = a := by
  induction l with
  | nil =>
      simp at ha
  | cons b bs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with hba | hbs
      · subst a
        exact ⟨⟨0, by simp⟩, rfl⟩
      · obtain ⟨i, hi⟩ := ih hbs
        refine ⟨⟨i.val + 1, by simp⟩, ?_⟩
        simpa using hi

/-- Tetrahedron witnesses are represented by finite list positions, not by
an unrestricted subtype of the ambient tetrahedron type. -/
abbrev FiniteMove32TetIndex (K : Triangulation) := Fin K.tets.length

def FiniteMove32TetIndex.decode {K : Triangulation} (i : FiniteMove32TetIndex K) : Tet :=
  K.tets.get i

/-- Encode an existing tetrahedron membership witness as a finite index. -/
noncomputable def FiniteMove32TetIndex.ofMem
    {K : Triangulation} (t : Tet) (ht : t ∈ K.tets) :
    FiniteMove32TetIndex K :=
  Classical.choose (exists_fin_get_eq_of_mem K.tets ht)

/-- Decoding the encoded membership witness returns the original tetrahedron,
not merely a tetrahedron with equivalent vertices. -/
theorem FiniteMove32TetIndex.decode_ofMem
    {K : Triangulation} (t : Tet) (ht : t ∈ K.tets) :
    (FiniteMove32TetIndex.ofMem t ht).decode = t :=
  Classical.choose_spec (exists_fin_get_eq_of_mem K.tets ht)

/-- The full incidence predicate for a fixed explicit witness tuple. -/
def ExplicitMove32WitnessValid
    (K : Triangulation) (s s' : Move32Site)
    (tau rho sigma : FiniteMove32TetIndex K)
    (x y : FiniteMove32Vertex K) : Prop :=
  let t := tau.decode
  let r := rho.decode
  let g := sigma.decode
  t ∈ K.tets ∧
  r ∈ K.tets ∧
  ¬ SameTetVertices t r ∧
  s.a ∈ t.verts ∧ s.b ∈ t.verts ∧ s.c ∈ t.verts ∧
  s.a ∈ r.verts ∧ s.b ∈ r.verts ∧ s.c ∈ r.verts ∧
  x.1 ∈ t.verts ∧ x.1 ∉ [s.a, s.b, s.c] ∧
  y.1 ∈ r.verts ∧ y.1 ∉ [s.a, s.b, s.c] ∧
  x.1 ≠ y.1 ∧
  g ∈ K.tets ∧ x.1 ∈ g.verts ∧ y.1 ∈ g.verts ∧
  ¬ ((x.1 = s.d ∧ y.1 = s.e) ∨ (x.1 = s.e ∧ y.1 = s.d)) ∧
  s'.d = x.1 ∧ s'.e = y.1 ∧
  s'.RealizedIn K ∧ s'.SharedEdgeExactlyThree K ∧
  (∃ gamma ∈ K.tets, s'.a ∈ gamma.verts ∧ s'.b ∈ gamma.verts ∧ s'.c ∈ gamma.verts)

/-- Finite tuple of all state and witness data, before its incidence proof. -/
structure Move32WitnessData (K : Triangulation) where
  source : FiniteRealizedMove32Site K
  target : FiniteRealizedMove32Site K
  tau : FiniteMove32TetIndex K
  rho : FiniteMove32TetIndex K
  x : FiniteMove32Vertex K
  y : FiniteMove32Vertex K
  sigma : FiniteMove32TetIndex K

noncomputable instance move32WitnessDataFintype (K : Triangulation) :
    Fintype (Move32WitnessData K) := by
  classical
  letI := finiteRealizedMove32SiteFintype K
  exact Fintype.ofInjective
    (fun d : Move32WitnessData K =>
      (d.source, d.target, d.tau, d.rho, d.x, d.y, d.sigma))
    (by
      intro a b h
      cases a
      cases b
      simp_all)

/-- Finite state carrying both realized sites and every geometric witness. -/
def Move32WitnessState (K : Triangulation) :=
  {d : Move32WitnessData K //
    ExplicitMove32WitnessValid K d.source.val.decode d.target.val.decode
      d.tau d.rho d.sigma d.x d.y}

noncomputable instance move32WitnessStateFintype (K : Triangulation) :
    Fintype (Move32WitnessState K) := by
  classical
  unfold Move32WitnessState
  infer_instance

/-- The existing relation with explicit source realization. -/
def RealizedSourceWitnessedReentry
    (K : Triangulation) (s s' : Move32Site) : Prop :=
  s.RealizedIn K ∧ Move32SourceFaceWitnessedReentry K s s'

theorem realizedSourceWitnessedReentry_implies_reentry
    {K : Triangulation} {s s' : Move32Site}
    (h : RealizedSourceWitnessedReentry K s s') :
    Move32SourceFaceReentry K s s' :=
  Move32SourceFaceWitnessedReentry.toSourceFaceReentry h.2

/-- Any explicit witness state forgets to the repository's existential relation. -/
theorem Move32WitnessState.toWitnessedReentry
    {K : Triangulation} (q : Move32WitnessState K) :
    Move32SourceFaceWitnessedReentry K
      q.val.source.val.decode q.val.target.val.decode := by
  rcases q with ⟨data, h⟩
  dsimp [ExplicitMove32WitnessValid] at h
  exact ⟨data.tau.decode, data.rho.decode, data.x.1, data.y.1,
    data.sigma.decode, h⟩


/-- Reverse encoding: every original witnessed reentry with a realized source
produces a finite state. The construction below chooses its finite indices from
the original membership proofs and proves each index decodes to that exact
tetrahedron before establishing the complete incidence predicate. -/
theorem Move32WitnessState.ofWitnessedReentry
    {K : Triangulation} {s s' : Move32Site}
    (h : RealizedSourceWitnessedReentry K s s') :
    ∃ q : Move32WitnessState K, ∃ tau rho x y sigma,
      q.val.source.val.decode = s ∧ q.val.target.val.decode = s' ∧
      q.val.tau.decode = tau ∧ q.val.rho.decode = rho ∧
      q.val.x.1 = x ∧ q.val.y.1 = y ∧ q.val.sigma.decode = sigma := by
  classical
  rcases h with ⟨hs, hw⟩
  rcases hw with ⟨tau, rho, x, y, sigma, htau, hrho, hne, haT, hbT, hcT,
    haR, hbR, hcR, hxT, hxABC, hyR, hyABC, hxy, hsigma, hxG, hyG,
    hnonself, hsd, hse, hreal, hthree, hobstruction⟩
  let source : FiniteRealizedMove32Site K :=
    ⟨Move32SiteCode.ofRealized s hs, by
      rw [Move32SiteCode.decode_ofRealized]
      exact hs⟩
  let target : FiniteRealizedMove32Site K :=
    ⟨Move32SiteCode.ofRealized s' hreal, by
      rw [Move32SiteCode.decode_ofRealized]
      exact hreal⟩
  let ti := FiniteMove32TetIndex.ofMem tau htau
  let ri := FiniteMove32TetIndex.ofMem rho hrho
  let gi := FiniteMove32TetIndex.ofMem sigma hsigma
  let xv : FiniteMove32Vertex K :=
    ⟨x, by simpa using mem_vertexSupport_of_mem_tet htau hxT⟩
  let yv : FiniteMove32Vertex K :=
    ⟨y, by simpa using mem_vertexSupport_of_mem_tet hrho hyR⟩
  let data : Move32WitnessData K := ⟨source, target, ti, ri, xv, yv, gi⟩
  have valid : ExplicitMove32WitnessValid K source.val.decode target.val.decode ti ri gi xv yv := by
    dsimp [ExplicitMove32WitnessValid, ti, ri, gi, xv, yv, source, target]
    simp only [FiniteMove32TetIndex.decode_ofMem, Move32SiteCode.decode_ofRealized]
    exact ⟨htau, hrho, hne, haT, hbT, hcT, haR, hbR, hcR, hxT, hxABC,
      hyR, hyABC, hxy, hsigma, hxG, hyG, hnonself, hsd, hse, hreal,
      hthree, hobstruction⟩
  let q : Move32WitnessState K := ⟨data, valid⟩
  refine ⟨q, tau, rho, x, y, sigma, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [q, data, source, Move32SiteCode.decode_ofRealized]
  · simp [q, data, target, Move32SiteCode.decode_ofRealized]
  · simp [q, data, ti, FiniteMove32TetIndex.decode_ofMem]
  · simp [q, data, ri, FiniteMove32TetIndex.decode_ofMem]
  · simp [q, data, xv]
  · simp [q, data, yv]
  · simp [q, data, gi, FiniteMove32TetIndex.decode_ofMem]


/-- Exact finite-state characterization of the realized-source relation:
there is a valid finite witness state decoding to the given sites exactly
when the original witnessed reentry relation holds. -/
theorem witnessedReentry_iff_exists_finite_state
    {K : Triangulation} {s s' : Move32Site} :
    RealizedSourceWitnessedReentry K s s' ↔
      ∃ q : Move32WitnessState K,
        q.val.source.val.decode = s ∧ q.val.target.val.decode = s' := by
  constructor
  · intro h
    obtain ⟨q, tau, rho, x, y, sigma, hs, ht, hτ, hρ, hx, hy, hσ⟩ :=
      Move32WitnessState.ofWitnessedReentry h
    exact ⟨q, hs, ht⟩
  · rintro ⟨q, hs, ht⟩
    have hsource := q.val.source.property
    have hw := Move32WitnessState.toWitnessedReentry q
    exact ⟨by simpa [hs] using hsource, by simpa [hs, ht] using hw⟩


/-- The finite transition relation is the projection of valid finite witness
states onto their realized source and target site codes. -/
def FiniteMove32Transition (K : Triangulation)
    (source target : FiniteRealizedMove32Site K) : Prop :=
  ∃ w : Move32WitnessState K,
    w.val.source.val.decode = source.val.decode ∧
    w.val.target.val.decode = target.val.decode

/-- The projected finite transition relation is exact: it neither loses nor
adds witnessed transitions between represented sites. -/
theorem finiteMove32Transition_iff_witnessedReentry
    {K : Triangulation} (source target : FiniteRealizedMove32Site K) :
    FiniteMove32Transition K source target ↔
      Move32SourceFaceWitnessedReentry K source.val.decode target.val.decode := by
  constructor
  · rintro ⟨w, hs, ht⟩
    have hw := Move32WitnessState.toWitnessedReentry w
    simpa [hs, ht] using hw
  · intro h
    have hrealized : RealizedSourceWitnessedReentry K
        source.val.decode target.val.decode :=
      ⟨source.property, h⟩
    obtain ⟨w, _, _, _, _, _, hs, ht, _, _, _, _, _⟩ :=
      Move32WitnessState.ofWitnessedReentry hrealized
    exact ⟨w, hs, ht⟩



/-- A witnessed transition cannot be a self-loop: the non-self complementary
edge condition excludes the source's own ordered or reversed endpoint pair.
This is only irreflexivity; it does not rule out cycles of length at least two. -/
theorem finiteMove32Transition_irrefl
    {K : Triangulation} (s : FiniteRealizedMove32Site K) :
    ¬ FiniteMove32Transition K s s := by
  rintro ⟨w, hs, ht⟩
  have hw := Move32WitnessState.toWitnessedReentry w
  rcases hw with ⟨tau, rho, x, y, sigma, htau, hrho, hne,
    haT, hbT, hcT, haR, hbR, hcR, hxT, hxABC, hyR, hyABC,
    hxy, hsigma, hxG, hyG, hnonself, hsd, hse, hreal, hthree, hobstruction⟩
  have hsd' : w.val.source.val.decode.d = x := by
    simpa [hs, ht] using hsd
  have hse' : w.val.source.val.decode.e = y := by
    simpa [hs, ht] using hse
  exact hnonself (Or.inl ⟨hsd'.symm, hse'.symm⟩)

end Poincare
