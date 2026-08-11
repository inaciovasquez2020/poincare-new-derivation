import Poincare.Move2332LocalEscapeCriterion
import Poincare.Move23ClosedCorePreservation
import Poincare.Move32ClosedCorePreservation

namespace Poincare

set_option maxHeartbeats 800000

def move2332FirstMove32 (m : Move23Site) (x : Nat) : Move32Site where
  a := x
  b := m.d
  c := m.e
  d := m.b
  e := m.c

def move2332SecondMove32 (m : Move23Site) (y : Nat) : Move32Site where
  a := y
  b := m.d
  c := m.e
  d := m.a
  e := m.c

def move2332FirstResidual (K : Triangulation) (m : Move23Site) (x : Nat) : List Tet :=
  eraseFirstSameTet (move2332FirstMove32 m x).targetTet₁
    (eraseFirstSameTet (move2332FirstMove32 m x).targetTet₀ (m.unchangedTets K))

def degreeDefectValue (n : Nat) : Nat :=
  Int.natAbs ((n : Int) - (targetDegree : Int))

structure Move2332InitialEscapeSeed (K : Triangulation) (m : Move23Site) where
  x : Nat
  y : Nat
  distinct : [m.a, m.b, m.c, m.d, m.e, x, y].Nodup
  realized : m.RealizedIn K
  sharedFace : m.SharedFaceExactlyTwo K
  newEdgeAbsent : m.NewEdgeAbsent K
  firstTarget₀ : ∃ tau ∈ m.unchangedTets K,
    SameTetVertices tau (move2332FirstMove32 m x).targetTet₀
  firstTarget₁ : ∃ tau ∈ m.unchangedTets K,
    SameTetVertices tau (move2332FirstMove32 m x).targetTet₁
  firstSharedEdge : ((m.unchangedTets K).filter (fun tau =>
    m.b ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 2
  firstSourceFaceAbsent : ∀ tau ∈ m.unchangedTets K,
    ¬ (x ∈ tau.verts ∧ m.d ∈ tau.verts ∧ m.e ∈ tau.verts)
  secondTarget₀ : ∃ tau ∈ move2332FirstResidual K m x,
    SameTetVertices tau (move2332SecondMove32 m y).targetTet₀
  secondTarget₁ : ∃ tau ∈ move2332FirstResidual K m x,
    SameTetVertices tau (move2332SecondMove32 m y).targetTet₁
  secondSharedEdge : ((move2332FirstResidual K m x).filter (fun tau =>
    m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 2
  secondSourceFaceAbsent : ∀ tau ∈ move2332FirstResidual K m x,
    ¬ (y ∈ tau.verts ∧ m.d ∈ tau.verts ∧ m.e ∈ tau.verts)
  degreeBudget : degreeDefectValue (vertexDegree K m.d + 2) +
        degreeDefectValue (vertexDegree K m.e + 2) +
        degreeDefectValue (vertexDegree K m.b - 2) +
        degreeDefectValue (vertexDegree K m.c - 2) +
        degreeDefectValue (vertexDegree K m.a - 2) +
        degreeDefectValue (vertexDegree K m.c - 4) <
      degreeDefectValue (vertexDegree K m.d) +
        degreeDefectValue (vertexDegree K m.e) +
        degreeDefectValue (vertexDegree K m.b) +
        degreeDefectValue (vertexDegree K m.c) +
        degreeDefectValue (vertexDegree K m.a) +
        degreeDefectValue (vertexDegree K m.c - 2)

private theorem move2332FirstMove32_unchangedTets
    (K : Triangulation) (m : Move23Site) (x y : Nat)
    (hdistinct : [m.a, m.b, m.c, m.d, m.e, x, y].Nodup) :
    (move2332FirstMove32 m x).unchangedTets (m.replace K) =
      m.newTet₀ :: m.newTet₁ :: move2332FirstResidual K m x := by
  let s := move2332FirstMove32 m x
  have h00 : sameTetVerticesBool m.newTet₀ s.targetTet₀ = false := by
    simp [sameTetVerticesBool, s, move2332FirstMove32, Move32Site.targetTet₀,
      Move23Site.newTet₀, Tet.verts] at hdistinct ⊢ <;> aesop
  have h01 : sameTetVerticesBool m.newTet₁ s.targetTet₀ = false := by
    simp [sameTetVerticesBool, s, move2332FirstMove32, Move32Site.targetTet₀,
      Move23Site.newTet₁, Tet.verts] at hdistinct ⊢ <;> aesop
  have h02 : sameTetVerticesBool m.newTet₂ s.targetTet₀ = false := by
    simp [sameTetVerticesBool, s, move2332FirstMove32, Move32Site.targetTet₀,
      Move23Site.newTet₂, Tet.verts] at hdistinct ⊢ <;> aesop
  have h10 : sameTetVerticesBool m.newTet₀ s.targetTet₁ = false := by
    simp [sameTetVerticesBool, s, move2332FirstMove32, Move32Site.targetTet₁,
      Move23Site.newTet₀, Tet.verts] at hdistinct ⊢ <;> aesop
  have h11 : sameTetVerticesBool m.newTet₁ s.targetTet₁ = false := by
    simp [sameTetVerticesBool, s, move2332FirstMove32, Move32Site.targetTet₁,
      Move23Site.newTet₁, Tet.verts] at hdistinct ⊢ <;> aesop
  have h12 : sameTetVerticesBool m.newTet₂ s.targetTet₁ = false := by
    simp [sameTetVerticesBool, s, move2332FirstMove32, Move32Site.targetTet₁,
      Move23Site.newTet₂, Tet.verts] at hdistinct ⊢ <;> aesop
  have h20 : sameTetVerticesBool m.newTet₀ s.targetTet₂ = false := by
    simp [sameTetVerticesBool, s, move2332FirstMove32, Move32Site.targetTet₂,
      Move23Site.newTet₀, Tet.verts] at hdistinct ⊢ <;> aesop
  have h21 : sameTetVerticesBool m.newTet₁ s.targetTet₂ = false := by
    simp [sameTetVerticesBool, s, move2332FirstMove32, Move32Site.targetTet₂,
      Move23Site.newTet₁, Tet.verts] at hdistinct ⊢ <;> aesop
  have h22 : sameTetVerticesBool m.newTet₂ s.targetTet₂ = true := by
    simp [sameTetVerticesBool, s, move2332FirstMove32, Move32Site.targetTet₂,
      Move23Site.newTet₂, Tet.verts]
  change s.unchangedTets (m.replace K) = _
  simp [Move32Site.unchangedTets, Move23Site.replace, Move23Site.unchangedTets,
    move2332FirstResidual, eraseFirstSameTet, h00, h01, h02, h10, h11, h12,
    h20, h21, h22, s]

theorem Move2332InitialEscapeSeed.move23_legal
    {K : Triangulation} {m : Move23Site}
    (hseed : Move2332InitialEscapeSeed K m) : m.LegalIn K := by
  rcases hseed with ⟨x, y, hdistinct, hrealized, hshared, habsent, hrest⟩
  exact ⟨hrealized, hshared, habsent⟩

private theorem move2332FirstMove32_legal_of_initial_data
    {K : Triangulation} (m : Move23Site) (x y : Nat)
    (hdistinct : [m.a, m.b, m.c, m.d, m.e, x, y].Nodup)
    (ht0 : ∃ tau ∈ m.unchangedTets K,
      SameTetVertices tau (move2332FirstMove32 m x).targetTet₀)
    (ht1 : ∃ tau ∈ m.unchangedTets K,
      SameTetVertices tau (move2332FirstMove32 m x).targetTet₁)
    (hedge : ((m.unchangedTets K).filter (fun tau =>
      m.b ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 2)
    (hface : ∀ tau ∈ m.unchangedTets K,
      ¬ (x ∈ tau.verts ∧ m.d ∈ tau.verts ∧ m.e ∈ tau.verts)) :
    (move2332FirstMove32 m x).LegalIn (m.replace K) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases ht0 with ⟨tau0, htau0, hsame0⟩
    rcases ht1 with ⟨tau1, htau1, hsame1⟩
    refine ⟨⟨tau0, by rw [m.replace_tets_eq K]; simp [htau0], hsame0⟩,
      ⟨tau1, by rw [m.replace_tets_eq K]; simp [htau1], hsame1⟩,
      ⟨m.newTet₂, (m.newTets_mem_replace K).2.2, ?_⟩⟩
    intro v
    simp [move2332FirstMove32, Move32Site.targetTet₂,
      Move23Site.newTet₂, Tet.verts]
    aesop
  · change (((m.replace K).tets.filter (fun tau =>
        m.b ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 3)
    rw [m.replace_tets_eq K]
    have hd := hdistinct
    simp at hd
    simpa [List.filter_cons, Move23Site.newTet₀, Move23Site.newTet₁,
      Move23Site.newTet₂, Tet.verts, hd, Ne.symm] using congrArg Nat.succ hedge
  · intro tau htau
    rw [m.replace_tets_eq K] at htau
    simp only [List.mem_cons] at htau
    rcases htau with rfl | rfl | rfl | htau
    · simp [move2332FirstMove32, Move23Site.newTet₀, Tet.verts]
        at hdistinct ⊢
      aesop
    · simp [move2332FirstMove32, Move23Site.newTet₁, Tet.verts]
        at hdistinct ⊢
      aesop
    · simp [move2332FirstMove32, Move23Site.newTet₂, Tet.verts]
        at hdistinct ⊢
      aesop
    · simpa [move2332FirstMove32] using hface tau htau

theorem Move2332InitialEscapeSeed.firstMove32_legal
    {K : Triangulation} {m : Move23Site}
    (hseed : Move2332InitialEscapeSeed K m) :
    (move2332FirstMove32 m hseed.x).LegalIn (m.replace K) := by
  rcases hseed with
    ⟨x, y, hdistinct, hrealized, hshared, habsent,
      ht0, ht1, hedge, hface, hrest⟩
  exact move2332FirstMove32_legal_of_initial_data m x y hdistinct
    ht0 ht1 hedge hface

theorem Move2332InitialEscapeSeed.move32s_legal
    {K : Triangulation} {m : Move23Site}
    (hseed : Move2332InitialEscapeSeed K m) :
    (move2332FirstMove32 m hseed.x).LegalIn (m.replace K) ∧
    move2332FirstMove32 m hseed.x ≠ Move32Site.ofMove23Site m ∧
    (move2332SecondMove32 m hseed.y).LegalIn
      ((move2332FirstMove32 m hseed.x).replace (m.replace K)) := by
  rcases hseed with
    ⟨x, y, hdistinct, hrealized, hshared, habsent,
      ht0, ht1, hedge, hface, ht20, ht21, hedge2, hface2, hdegree⟩
  have hlegal1 := move2332FirstMove32_legal_of_initial_data m x y hdistinct
    ht0 ht1 hedge hface
  refine ⟨hlegal1, ?_, ?_⟩
  · intro heq
    have ha := congrArg Move32Site.a heq
    simp [move2332FirstMove32, Move32Site.ofMove23Site] at ha
    simp at hdistinct
    omega
  · let s1 := move2332FirstMove32 m x
    let s2 := move2332SecondMove32 m y
    have hunchanged := move2332FirstMove32_unchangedTets K m x y hdistinct
    rcases ht20 with ⟨tau20, htau20, hsame20⟩
    rcases ht21 with ⟨tau21, htau21, hsame21⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨⟨tau20, ?_, hsame20⟩, ⟨tau21, ?_, hsame21⟩,
        ⟨m.newTet₁, ?_, ?_⟩⟩
      · rw [s1.replace_tets_eq (m.replace K), hunchanged]
        simp [htau20]
      · rw [s1.replace_tets_eq (m.replace K), hunchanged]
        simp [htau21]
      · rw [s1.replace_tets_eq (m.replace K), hunchanged]
        simp
      · intro v
        simp [s2, move2332SecondMove32, Move32Site.targetTet₂,
          Move23Site.newTet₁, Tet.verts]
        aesop
    · change ((((s1.replace (m.replace K)).tets.filter (fun tau =>
          m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 3))
      rw [s1.replace_tets_eq (m.replace K), hunchanged]
      have hd := hdistinct
      simp at hd
      simpa [s1, move2332FirstMove32, Move32Site.sourceTet₀,
        Move32Site.sourceTet₁, Move23Site.newTet₀, Move23Site.newTet₁,
        Tet.verts, hd, Ne.symm] using congrArg Nat.succ hedge2
    · intro tau htau
      rw [s1.replace_tets_eq (m.replace K), hunchanged] at htau
      simp only [List.mem_cons] at htau
      rcases htau with rfl | rfl | rfl | rfl | htau
      · simp [s1, s2, move2332FirstMove32, move2332SecondMove32,
          Move32Site.sourceTet₀, Tet.verts] at hdistinct ⊢
        aesop
      · simp [s1, s2, move2332FirstMove32, move2332SecondMove32,
          Move32Site.sourceTet₁, Tet.verts] at hdistinct ⊢
        aesop
      · simp [s2, move2332SecondMove32, Move23Site.newTet₀,
          Tet.verts] at hdistinct ⊢
        aesop
      · simp [s2, move2332SecondMove32, Move23Site.newTet₁,
          Tet.verts] at hdistinct ⊢
        aesop
      · simpa [s2, move2332SecondMove32] using hface2 tau htau

theorem exists_move2332Block_PhiSupport_lt_of_initial_escape_seed
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (m : Move23Site) (hseed : Move2332InitialEscapeSeed K m)
    (hcore1 : ClosedTriangulationCore (m.replace K))
    (hcore2 : ClosedTriangulationCore
      ((move2332FirstMove32 m hseed.x).replace (m.replace K))) :
    ∃ m32₁ m32₂ : Move32Site,
      m32₁ = move2332FirstMove32 m hseed.x ∧
      m32₂ = move2332SecondMove32 m hseed.y ∧
      m.LegalIn K ∧
      m32₁.LegalIn (m.replace K) ∧
      m32₁ ≠ Move32Site.ofMove23Site m ∧
      m32₂.LegalIn (m32₁.replace (m.replace K)) ∧
      PhiSupport (m32₂.replace (m32₁.replace (m.replace K))) <
        PhiSupport K := by
  have h23 := hseed.move23_legal
  obtain ⟨hlegal1, hnoninverse, hlegal2⟩ := hseed.move32s_legal
  have hdegree := hseed.degreeBudget
  rcases m.replace_vertexDegree_site K h23 with ⟨ha, hb, hc, hd, he⟩
  rcases hcore1.move32Site_replace_vertexDegree_site
      (move2332FirstMove32 m hseed.x) hlegal1 with
    ⟨hs1a, hs1b, hs1c, hs1d, hs1e⟩
  rcases hcore2.move32Site_replace_vertexDegree_site
      (move2332SecondMove32 m hseed.y) hlegal2 with
    ⟨hs2a, hs2b, hs2c, hs2d, hs2e⟩
  have hKa : vertexDegree
      ((move2332FirstMove32 m hseed.x).replace (m.replace K)) m.a =
      vertexDegree K m.a := by
    have hdist := hseed.distinct
    have hoff := hcore1.move32Site_replace_vertexDegree_offSite
      (move2332FirstMove32 m hseed.x) hlegal1 (v := m.a)
      (by simp [move2332FirstMove32] at hdist ⊢; aesop)
      (by simp [move2332FirstMove32] at hdist ⊢; aesop)
      (by simp [move2332FirstMove32] at hdist ⊢; aesop)
      (by simp [move2332FirstMove32] at hdist ⊢; aesop)
      (by simp [move2332FirstMove32] at hdist ⊢; aesop)
    exact hoff.trans ha
  have hd1 : vertexDegree (m.replace K) m.d = vertexDegree K m.d + 2 := hd
  have he1 : vertexDegree (m.replace K) m.e = vertexDegree K m.e + 2 := he
  have hb2 : vertexDegree
      ((move2332FirstMove32 m hseed.x).replace (m.replace K)) m.b =
      vertexDegree K m.b - 2 := by
    have hs1d' : vertexDegree (m.replace K) m.b =
        vertexDegree ((move2332FirstMove32 m hseed.x).replace
          (m.replace K)) m.b + 2 := by
      simpa [move2332FirstMove32] using hs1d
    omega
  have hc2deg : vertexDegree
      ((move2332FirstMove32 m hseed.x).replace (m.replace K)) m.c =
      vertexDegree K m.c - 2 := by
    have hs1e' : vertexDegree (m.replace K) m.c =
        vertexDegree ((move2332FirstMove32 m hseed.x).replace
          (m.replace K)) m.c + 2 := by
      simpa [move2332FirstMove32] using hs1e
    omega
  have ha3 : vertexDegree
      ((move2332SecondMove32 m hseed.y).replace
        ((move2332FirstMove32 m hseed.x).replace (m.replace K))) m.a =
      vertexDegree K m.a - 2 := by
    have hs2d' : vertexDegree
        ((move2332FirstMove32 m hseed.x).replace (m.replace K)) m.a =
        vertexDegree ((move2332SecondMove32 m hseed.y).replace
          ((move2332FirstMove32 m hseed.x).replace (m.replace K))) m.a + 2 := by
      simpa [move2332SecondMove32] using hs2d
    omega
  have hc3 : vertexDegree
      ((move2332SecondMove32 m hseed.y).replace
        ((move2332FirstMove32 m hseed.x).replace (m.replace K))) m.c =
      vertexDegree K m.c - 4 := by
    have hs2e' : vertexDegree
        ((move2332FirstMove32 m hseed.x).replace (m.replace K)) m.c =
        vertexDegree ((move2332SecondMove32 m hseed.y).replace
          ((move2332FirstMove32 m hseed.x).replace (m.replace K))) m.c + 2 := by
      simpa [move2332SecondMove32] using hs2e
    omega
  refine ⟨move2332FirstMove32 m hseed.x, move2332SecondMove32 m hseed.y,
    rfl, rfl, h23, hlegal1, hnoninverse, hlegal2, ?_⟩
  apply move2332Block_PhiSupport_lt_of_local_degree_conditions
    m h23 (move2332FirstMove32 m hseed.x) hlegal1 hcore1
      (move2332SecondMove32 m hseed.y) hlegal2 hcore2
  simp only [vertexDefect]
  simp only [move2332FirstMove32, move2332SecondMove32] at hb2 hc2deg hKa ha3 hc3
  simp only [move2332FirstMove32, move2332SecondMove32]
  rw [hd1, he1, hb2, hc2deg, hKa, ha3, hc3, hb, hc]
  simpa [degreeDefectValue, targetDegree, add_assoc] using hdegree

/-- An initial `2-3-3-2-3-2` escape seed determines a genuine closed-core,
strictly descending, topology-preserving block without requiring callers to
supply closed-core proofs for either intermediate triangulation. -/
theorem exists_closedCore_homeomorphic_PhiSupport_lt_of_initial_escape_seed
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (m : Move23Site) (hseed : Move2332InitialEscapeSeed K m) :
    ∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K') := by
  let m32₁ := move2332FirstMove32 m hseed.x
  let m32₂ := move2332SecondMove32 m hseed.y
  have h23 : m.LegalIn K := hseed.move23_legal
  have hlegal1 : m32₁.LegalIn (m.replace K) := by
    simpa [m32₁] using hseed.firstMove32_legal
  have hlegal2 : m32₂.LegalIn (m32₁.replace (m.replace K)) := by
    simpa [m32₁, m32₂] using hseed.move32s_legal.2.2
  have hcore1 : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m h23
  have hcore2 : ClosedTriangulationCore (m32₁.replace (m.replace K)) :=
    hcore1.move32Site_replace_closedCore m32₁ hlegal1
  have hcore3 : ClosedTriangulationCore
      (m32₂.replace (m32₁.replace (m.replace K))) :=
    hcore2.move32Site_replace_closedCore m32₂ hlegal2
  have hdescent : PhiSupport (m32₂.replace (m32₁.replace (m.replace K))) <
      PhiSupport K := by
    obtain ⟨s1, s2, hs1, hs2, _, _, _, _, hlt⟩ :=
      exists_move2332Block_PhiSupport_lt_of_initial_escape_seed
        hcore m hseed hcore1 hcore2
    subst s1
    subst s2
    simpa [m32₁, m32₂] using hlt
  refine ⟨m32₂.replace (m32₁.replace (m.replace K)), hcore3, hdescent, ?_⟩
  exact ⟨(hcore.move23GeometricCarrierHomeomorph m h23).trans
    ((hcore1.move32GeometricCarrierHomeomorph m32₁ hlegal1).trans
      (hcore2.move32GeometricCarrierHomeomorph m32₂ hlegal2))⟩

def crossPolytopeBoundary4_move2332InitialEscapeSeed :
    Move2332InitialEscapeSeed crossPolytopeBoundary4
      crossPolytopeEscapeMove23 where
  x := 1
  y := 3
  distinct := by decide
  realized := crossPolytopeEscapeMove23_legal.1
  sharedFace := crossPolytopeEscapeMove23_legal.2.1
  newEdgeAbsent := crossPolytopeEscapeMove23_legal.2.2
  firstTarget₀ := by
    refine ⟨⟨1, 2, 4, 6⟩, ?_, ?_⟩
    · norm_num [move2332FirstMove32, Move32Site.targetTet₀,
      Move23Site.unchangedTets, crossPolytopeEscapeMove23,
      Move23Site.leftTet, Move23Site.rightTet, crossPolytopeBoundary4,
      eraseFirstSameTet, sameTetVerticesBool, Tet.verts]
    · norm_num [SameTetVertices, move2332FirstMove32,
        Move32Site.targetTet₀, crossPolytopeEscapeMove23, Tet.verts]
      aesop
  firstTarget₁ := by
    refine ⟨⟨1, 2, 4, 7⟩, ?_, ?_⟩
    · norm_num [move2332FirstMove32, Move32Site.targetTet₁,
      Move23Site.unchangedTets, crossPolytopeEscapeMove23,
      Move23Site.leftTet, Move23Site.rightTet, crossPolytopeBoundary4,
      eraseFirstSameTet, sameTetVerticesBool, Tet.verts]
    · norm_num [SameTetVertices, move2332FirstMove32,
        Move32Site.targetTet₁, crossPolytopeEscapeMove23, Tet.verts]
      aesop
  firstSharedEdge := by decide
  firstSourceFaceAbsent := by decide
  secondTarget₀ := by
    refine ⟨⟨0, 3, 4, 6⟩, ?_, ?_⟩
    · norm_num [move2332FirstResidual, move2332FirstMove32,
      move2332SecondMove32, Move32Site.targetTet₀, Move32Site.targetTet₁,
      Move23Site.unchangedTets, crossPolytopeEscapeMove23,
      Move23Site.leftTet, Move23Site.rightTet, crossPolytopeBoundary4,
      eraseFirstSameTet, sameTetVerticesBool, Tet.verts]
    · norm_num [SameTetVertices, move2332SecondMove32,
        Move32Site.targetTet₀, crossPolytopeEscapeMove23, Tet.verts]
      aesop
  secondTarget₁ := by
    refine ⟨⟨0, 3, 4, 7⟩, ?_, ?_⟩
    · norm_num [move2332FirstResidual, move2332FirstMove32,
      move2332SecondMove32, Move32Site.targetTet₀, Move32Site.targetTet₁,
      Move23Site.unchangedTets, crossPolytopeEscapeMove23,
      Move23Site.leftTet, Move23Site.rightTet, crossPolytopeBoundary4,
      eraseFirstSameTet, sameTetVerticesBool, Tet.verts]
    · norm_num [SameTetVertices, move2332SecondMove32,
        Move32Site.targetTet₁, crossPolytopeEscapeMove23, Tet.verts]
      aesop
  secondSharedEdge := by decide
  secondSourceFaceAbsent := by decide
  degreeBudget := by decide

theorem crossPolytopeBoundary4_exists_move2332Block_PhiSupport_lt_of_initial_escape_seed :
    ∃ m32₁ m32₂ : Move32Site,
      crossPolytopeEscapeMove23.LegalIn crossPolytopeBoundary4 ∧
      m32₁.LegalIn crossPolytopeEscapeAfter23 ∧
      m32₁ ≠ Move32Site.ofMove23Site crossPolytopeEscapeMove23 ∧
      m32₂.LegalIn (m32₁.replace crossPolytopeEscapeAfter23) ∧
      PhiSupport (m32₂.replace (m32₁.replace crossPolytopeEscapeAfter23)) <
        PhiSupport crossPolytopeBoundary4 := by
  obtain ⟨m32₁, m32₂, _, _, hrest⟩ :=
    exists_move2332Block_PhiSupport_lt_of_initial_escape_seed
    crossPolytopeBoundary4_closedCore crossPolytopeEscapeMove23
    crossPolytopeBoundary4_move2332InitialEscapeSeed
    crossPolytopeEscapeAfter23_closedCore
    (by simpa [crossPolytopeBoundary4_move2332InitialEscapeSeed,
      move2332FirstMove32, crossPolytopeEscapeAfter32₁] using
        crossPolytopeEscapeAfter32One_closedCore)
  exact ⟨m32₁, m32₂, hrest⟩

end Poincare
