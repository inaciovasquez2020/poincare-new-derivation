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
produces a finite state retaining the exact tetrahedra and vertices from its
existential witness tuple. -/
noncomputable theorem Move32WitnessState.ofWitnessedReentry
    {K : Triangulation} {s s' : Move32Site}
    (h : RealizedSourceWitnessedReentry K s s') :
    ∃ q : Move32WitnessState K,
      q.val.source.val.decode = s ∧
      q.val.target.val.decode = s' ∧
      q.val.tau.decode = Classical.choose (by
        rcases h.2 with ⟨tau, rho, x, y, sigma, htau, hrho, hne, haT, hbT, hcT,
          haR, hbR, hcR, hxT, hxABC, hyR, hyABC, hxy, hsigma, hxG, hyG,
          hnonself, hsd, hse, hreal, hthree, hobstruction⟩
        exact ⟨tau, rho, x, y, sigma, htau, hrho, hne, haT, hbT, hcT,
          haR, hbR, hcR, hxT, hxABC, hyR, hyABC, hxy, hsigma, hxG, hyG,
          hnonself, hsd, hse, hreal, hthree, hobstruction⟩) := by
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
    ⟨x, by
      apply Finset.mem_toFinset.mpr
      exact mem_vertexSupport_of_mem_tet htau hxT⟩
  let yv : FiniteMove32Vertex K :=
    ⟨y, by
      apply Finset.mem_toFinset.mpr
      exact mem_vertexSupport_of_mem_tet hrho hyR⟩
  let data : Move32WitnessData K := ⟨source, target, ti, ri, xv, yv, gi⟩
  have valid : ExplicitMove32WitnessValid K source.val.decode target.val.decode ti ri gi xv yv := by
    dsimp [ExplicitMove32WitnessValid, ti, ri, gi, xv, yv, source, target]
    simp only [FiniteMove32TetIndex.decode_ofMem, Move32SiteCode.decode_ofRealized]
    exact ⟨htau, hrho, hne, haT, hbT, hcT, haR, hbR, hcR, hxT, hxABC,
      hyR, hyABC, hxy, hsigma, hxG, hyG, hnonself, hsd, hse, hreal,
      hthree, hobstruction⟩
  let q : Move32WitnessState K := ⟨data, valid⟩
  refine ⟨q, ?_, ?_, ?_⟩
  · simp [q, data, source, Move32SiteCode.decode_ofRealized]
  · simp [q, data, target, Move32SiteCode.decode_ofRealized]
  · simp [q, data, ti, FiniteMove32TetIndex.decode_ofMem]


end Poincare
