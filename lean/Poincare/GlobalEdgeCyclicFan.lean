import Poincare.TriangulationTopologicalManifoldVertexLinkStarConnectedness
import Poincare.GlobalEdgeIncidenceThreeStarAdjacency
import Poincare.Move32CombinatorialFoundation
import Poincare.Move23SimpleBistellarData
import Poincare.ComplementVertex

namespace Poincare

/-- The ambient tetrahedron represented by a triangle in a vertex link.  The
choice is unique in a closed triangulation (see
`ambientTetOfVertexLinkTriangle_eq`). -/
noncomputable def ambientTetOfVertexLinkTriangle
    (K : Triangulation) (v : Nat)
    (sigma : {rho : LinkTriangle // rho ∈ vertexLinkTriangles K v}) : Tet :=
  Classical.choose
    ((mem_vertexLinkTriangles_iff K v sigma.1).1 sigma.2)

theorem ambientTetOfVertexLinkTriangle_mem
    (K : Triangulation) (v : Nat)
    (sigma : {rho : LinkTriangle // rho ∈ vertexLinkTriangles K v}) :
    ambientTetOfVertexLinkTriangle K v sigma ∈ K.tets :=
  (Classical.choose_spec
    ((mem_vertexLinkTriangles_iff K v sigma.1).1 sigma.2)).1

theorem ambientTetOfVertexLinkTriangle_linkTriangleAt
    (K : Triangulation) (v : Nat)
    (sigma : {rho : LinkTriangle // rho ∈ vertexLinkTriangles K v}) :
    (ambientTetOfVertexLinkTriangle K v sigma).linkTriangleAt? v = some sigma.1 :=
  (Classical.choose_spec
    ((mem_vertexLinkTriangles_iff K v sigma.1).1 sigma.2)).2

theorem ClosedTriangulationCore.ambientTetOfVertexLinkTriangle_eq
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v : Nat} {sigma : LinkTriangle}
    (hsigma : sigma ∈ vertexLinkTriangles K v)
    {tau : Tet} (htau : tau ∈ K.tets)
    (hlink : tau.linkTriangleAt? v = some sigma) :
    ambientTetOfVertexLinkTriangle K v ⟨sigma, hsigma⟩ = tau := by
  apply hcore.eq_of_mem_of_sameTetVertices
  · exact ambientTetOfVertexLinkTriangle_mem K v ⟨sigma, hsigma⟩
  · exact htau
  · intro y
    by_cases hyv : y = v
    · subst y
      constructor <;> intro _
      · exact (tau.linkTriangleAt?_isSome_iff v).1 (by simp [hlink])
      · exact
          (Tet.linkTriangleAt?_isSome_iff
            (ambientTetOfVertexLinkTriangle K v ⟨sigma, hsigma⟩) v).1
            (by simp [ambientTetOfVertexLinkTriangle_linkTriangleAt])
    · rw [
        ← Tet.mem_linkTriangleAt?_iff
          (ambientTetOfVertexLinkTriangle K v ⟨sigma, hsigma⟩) v y sigma
            (ambientTetOfVertexLinkTriangle_linkTriangleAt K v ⟨sigma, hsigma⟩) hyv,
        ← tau.mem_linkTriangleAt?_iff v y sigma hlink hyv]

/-- A cyclic edge fan with its link triangles transported to actual ambient
tetrahedra.  Keeping the graph walk in the certificate records both ordinary
successor adjacency and the final/initial closing adjacency without a second
cyclic indexing convention. -/
structure AmbientEdgeCyclicFan (K : Triangulation) (v x : Nat) where
  start : {sigma : LinkTriangle // sigma ∈ vertexLinkStarTriangles K v x}
  walk : (vertexLinkStarGraph K v x).Walk start start
  isCycle : walk.IsCycle
  length_ge_three : 3 ≤ walk.length
  covers : ∀ sigma : {rho : LinkTriangle // rho ∈ vertexLinkStarTriangles K v x},
    sigma ∈ walk.support
  tetAt : {sigma : LinkTriangle // sigma ∈ vertexLinkStarTriangles K v x} → Tet
  tetAt_mem : ∀ sigma, tetAt sigma ∈ K.tets
  tetAt_link : ∀ sigma, (tetAt sigma).linkTriangleAt? v = some sigma.1
  tetAt_injective : Function.Injective tetAt
  covers_ambient : ∀ tau ∈ K.tets,
    v ∈ tau.verts → x ∈ tau.verts → ∃ sigma, tetAt sigma = tau

/-- Every ambient cyclic fan contains an adjacent pair of star triangles. -/
theorem AmbientEdgeCyclicFan.exists_adjacent
    {K : Triangulation} {v x : Nat} (F : AmbientEdgeCyclicFan K v x) :
    ∃ sigma rho, (vertexLinkStarGraph K v x).Adj sigma rho := by
  have hlength := F.length_ge_three
  cases hwalk : F.walk with
  | nil => simp [hwalk] at hlength
  | cons hadj tail => exact ⟨_, _, hadj⟩

theorem AmbientEdgeCyclicFan.tetAt_contains_center
    {K : Triangulation} {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    (sigma) : v ∈ (F.tetAt sigma).verts := by
  rw [← (F.tetAt sigma).linkTriangleAt?_isSome_iff v, F.tetAt_link]
  rfl

theorem AmbientEdgeCyclicFan.tetAt_contains_edgeVertex
    {K : Triangulation} {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    (sigma) : x ∈ (F.tetAt sigma).verts := by
  have hx : x ∈ sigma.1.verts :=
    ((mem_vertexLinkStarTriangles_iff K v x sigma.1).1 sigma.2).2
  exact (F.tetAt sigma).linkTriangleAt?_verts_subset v sigma.1 (F.tetAt_link sigma) x hx

/-- Graph adjacency in an ambient fan supplies the exact third vertex of a
represented face containing the central edge. -/
theorem AmbientEdgeCyclicFan.adjacent_tets_share_face
    {K : Triangulation} {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    {sigma rho} (hadj : (vertexLinkStarGraph K v x).Adj sigma rho) :
    ∃ y, y ≠ x ∧
      v ∈ (F.tetAt sigma).verts ∧ x ∈ (F.tetAt sigma).verts ∧
      y ∈ (F.tetAt sigma).verts ∧
      v ∈ (F.tetAt rho).verts ∧ x ∈ (F.tetAt rho).verts ∧
      y ∈ (F.tetAt rho).verts := by
  obtain ⟨_, hstar⟩ := (vertexLinkStarGraph_adj K v x sigma rho).1 hadj
  obtain ⟨_, _, y, hyx, hys, hyr⟩ := hstar
  refine ⟨y, hyx, F.tetAt_contains_center sigma,
    F.tetAt_contains_edgeVertex sigma, ?_, F.tetAt_contains_center rho,
    F.tetAt_contains_edgeVertex rho, ?_⟩
  · exact (F.tetAt sigma).linkTriangleAt?_verts_subset v sigma.1 (F.tetAt_link sigma) y hys
  · exact (F.tetAt rho).linkTriangleAt?_verts_subset v rho.1 (F.tetAt_link rho) y hyr

/-- Successive vertices of the link cycle represent genuinely distinct
ambient tetrahedra. -/
theorem AmbientEdgeCyclicFan.adjacent_tets_ne
    {K : Triangulation} {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    {sigma rho} (hadj : (vertexLinkStarGraph K v x).Adj sigma rho) :
    F.tetAt sigma ≠ F.tetAt rho := by
  intro heq
  have hsr : sigma = rho := F.tetAt_injective heq
  exact hadj.ne hsr

/-- Graph adjacency gives an actual nondegenerate ambient face containing the
central edge.  The `Nodup` certificate is the form consumed by tetrahedron
face classification and bistellar-move legality arguments. -/
theorem ClosedTriangulationCore.ambientEdgeCyclicFan_adjacent_tets_share_face
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    {sigma rho} (hadj : (vertexLinkStarGraph K v x).Adj sigma rho) :
    exists y, [v, x, y].Nodup /\
      v ∈ (F.tetAt sigma).verts /\ x ∈ (F.tetAt sigma).verts /\
      y ∈ (F.tetAt sigma).verts /\
      v ∈ (F.tetAt rho).verts /\ x ∈ (F.tetAt rho).verts /\
      y ∈ (F.tetAt rho).verts := by
  obtain ⟨_, hstar⟩ := (vertexLinkStarGraph_adj K v x sigma rho).1 hadj
  obtain ⟨_, _, y, hyx, hysLink, hyrLink⟩ := hstar
  have hvs := F.tetAt_contains_center sigma
  have hxs := F.tetAt_contains_edgeVertex sigma
  have hys := (F.tetAt sigma).linkTriangleAt?_verts_subset v sigma.1
    (F.tetAt_link sigma) y hysLink
  have hvr := F.tetAt_contains_center rho
  have hxr := F.tetAt_contains_edgeVertex rho
  have hyr := (F.tetAt rho).linkTriangleAt?_verts_subset v rho.1
    (F.tetAt_link rho) y hyrLink
  have hnodup := hcore.1 (F.tetAt sigma) (F.tetAt_mem sigma)
  have hvx : v ≠ x := by
    intro hvx
    subst x
    exact (F.tetAt sigma).linkTriangleAt?_vertex_not_mem v sigma.1 hnodup
      (F.tetAt_link sigma)
      (((mem_vertexLinkStarTriangles_iff K v v sigma.1).1 sigma.2).2)
  have hyv : y ≠ v := by
    intro hyv
    subst y
    exact (F.tetAt sigma).linkTriangleAt?_vertex_not_mem v sigma.1 hnodup
      (F.tetAt_link sigma) hysLink
  refine ⟨y, ?_, hvs, hxs, hys, hvr, hxr, hyr⟩
  simp [List.nodup_cons, hvx, hyv.symm, hyx.symm]

/-- Adjacent tetrahedra in an ambient edge fan determine the honest local
`2-3` candidate.  Either its prospective new edge is already represented, or
the candidate is legal. -/
theorem ClosedTriangulationCore.ambientEdgeCyclicFan_adjacent_exists_legalMove23_or_representedChord
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    {sigma rho} (hadj : (vertexLinkStarGraph K v x).Adj sigma rho) :
    ∃ y z0 z1, ∃ m : Move23Site,
      m.a = v ∧ m.b = x ∧ m.c = y ∧ m.d = z0 ∧ m.e = z1 ∧
      SameTetVertices (F.tetAt sigma) m.leftTet ∧
      SameTetVertices (F.tetAt rho) m.rightTet ∧
      (m.LegalIn K ∨
        ∃ tau ∈ K.tets, z0 ∈ tau.verts ∧ z1 ∈ tau.verts) := by
  classical
  obtain ⟨y, habc, hv0, hx0, hy0, hv1, hx1, hy1⟩ :=
    hcore.ambientEdgeCyclicFan_adjacent_tets_share_face F hadj
  have hn0 := hcore.1 (F.tetAt sigma) (F.tetAt_mem sigma)
  have hn1 := hcore.1 (F.tetAt rho) (F.tetAt_mem rho)
  have hnotSame : ¬ SameTetVertices (F.tetAt sigma) (F.tetAt rho) := by
    intro hs
    exact F.adjacent_tets_ne hadj
      (hcore.eq_of_mem_of_sameTetVertices
        (F.tetAt_mem sigma) (F.tetAt_mem rho) hs)
  obtain ⟨z0, z1, hz00, hz0out, hz11, hz1out, hz01, hcover0, hcover1⟩ :=
    Tet.exists_distinct_complement_vertices
      (F.tetAt sigma) (F.tetAt rho) hn0 hn1 habc
      hv0 hx0 hy0 hv1 hx1 hy1 hnotSame
  have hsame0 : SameTetVertices (F.tetAt sigma) (⟨v, x, y, z0⟩ : Tet) := by
    intro w
    constructor
    · intro hw
      rcases hcover0 w hw with rfl | rfl | rfl | rfl <;> simp [Tet.verts]
    · intro hw
      simp [Tet.verts] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hv0
      · exact hx0
      · exact hy0
      · exact hz00
  have hsame1 : SameTetVertices (F.tetAt rho) (⟨v, x, y, z1⟩ : Tet) := by
    intro w
    constructor
    · intro hw
      rcases hcover1 w hw with rfl | rfl | rfl | rfl <;> simp [Tet.verts]
    · intro hw
      simp [Tet.verts] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hv1
      · exact hx1
      · exact hy1
      · exact hz11
  have hfive : [v, x, y, z0, z1].Nodup := by
    have hnleft := Tet.verts_nodup_of_sameTetVertices hn0 hsame0
    have hnright := Tet.verts_nodup_of_sameTetVertices hn1 hsame1
    simp [Tet.verts] at hnleft hnright ⊢
    aesop
  let m : Move23Site :=
    { a := v, b := x, c := y, d := z0, e := z1, distinct := hfive }
  refine ⟨y, z0, z1, m, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [m, Move23Site.leftTet] using hsame0
  · simpa [m, Move23Site.rightTet] using hsame1
  · by_cases hedge : ∃ tau ∈ K.tets, z0 ∈ tau.verts ∧ z1 ∈ tau.verts
    · exact Or.inr hedge
    · left
      have hrealized : m.RealizedIn K := by
        exact ⟨⟨F.tetAt sigma, F.tetAt_mem sigma, by
          simpa [m, Move23Site.leftTet] using hsame0⟩,
          ⟨F.tetAt rho, F.tetAt_mem rho, by
            simpa [m, Move23Site.rightTet] using hsame1⟩⟩
      have hshared : m.SharedFaceExactlyTwo K := by
        have hlength := hcore.2.2 v x y habc
          ⟨F.tetAt sigma, F.tetAt_mem sigma, hv0, hx0, hy0⟩
        simpa [m, Move23Site.SharedFaceExactlyTwo] using hlength
      have habsent : m.NewEdgeAbsent K := by
        intro tau htau hboth
        exact hedge ⟨tau, htau, by simpa [m] using hboth⟩
      exact ⟨hrealized, hshared, habsent⟩

/-- The five-label form of the adjacent-fan tetrahedron geometry.  This
exposes the complement vertices and their nondegeneracy directly, while
retaining the fully checked `Move23Site.LegalIn`/represented-chord split. -/
theorem ClosedTriangulationCore.ambientEdgeCyclicFan_adjacent_fiveLabelGeometry
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    {sigma rho} (hadj : (vertexLinkStarGraph K v x).Adj sigma rho) :
    ∃ y z0 z1, [v, x, y, z0].Nodup ∧ [v, x, y, z1].Nodup ∧ z0 ≠ z1 ∧
      SameTetVertices (F.tetAt sigma) (⟨v, x, y, z0⟩ : Tet) ∧
      SameTetVertices (F.tetAt rho) (⟨v, x, y, z1⟩ : Tet) ∧
      (∃ m : Move23Site,
        m.a = v ∧ m.b = x ∧ m.c = y ∧ m.d = z0 ∧ m.e = z1 ∧
        (m.LegalIn K ∨
          ∃ tau ∈ K.tets, z0 ∈ tau.verts ∧ z1 ∈ tau.verts)) := by
  obtain ⟨y, z0, z1, m, ha, hb, hc, hd, he, hleft, hright, hstatus⟩ :=
    hcore.ambientEdgeCyclicFan_adjacent_exists_legalMove23_or_representedChord F hadj
  have hfive : [v, x, y, z0, z1].Nodup := by
    simpa [ha, hb, hc, hd, he] using m.distinct
  refine ⟨y, z0, z1, ?_, ?_, ?_, ?_, ?_, m, ha, hb, hc, hd, he, hstatus⟩
  · exact hfive.sublist (by simp)
  · exact hfive.sublist (by simp)
  · simp [List.nodup_cons] at hfive
    aesop
  · simpa [ha, hb, hc, hd, Move23Site.leftTet] using hleft
  · simpa [ha, hb, hc, he, Move23Site.rightTet] using hright

/-- A represented edge in an honest closed triangulated three-manifold has a
single finite cyclic fan whose subgraph contains every represented link
triangle in the edge star. -/
theorem ClosedTriangulationCore.exists_vertexLinkStar_exact_coveringCycle_of_topologicalThreeManifold
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x) :
    ∃
      (sigma :
        {tau : LinkTriangle //
          tau ∈ vertexLinkStarTriangles K v x}),
      ∃
        (p : (vertexLinkStarGraph K v x).Walk sigma sigma),
        p.IsCycle ∧
        p.toSubgraph.verts =
          (Set.univ :
            Set
              {tau : LinkTriangle //
                tau ∈ vertexLinkStarTriangles K v x}) := by
  exact
    exists_vertexLinkStar_coveringCycle
      K v x hrep
      (vertexLinkStarConnected_of_topologicalThreeManifold
        K hcore hM hrep)
      (hcore.vertexLinkStarDegreeTwo hrep)

/-- A represented edge in an honest closed triangulated three-manifold has a
single finite cyclic fan.  The vertices of the walk are precisely all link
triangles containing the transverse vertex, hence precisely the represented
tetrahedra around the edge after applying `linkTriangleAt?`. -/
theorem ClosedTriangulationCore.exists_vertexLinkStar_coveringCycle_of_topologicalThreeManifold
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x) :
    ∃
      (sigma :
        {tau : LinkTriangle //
          tau ∈ vertexLinkStarTriangles K v x}),
      ∃
        (p : (vertexLinkStarGraph K v x).Walk sigma sigma),
        p.IsCycle ∧
        3 ≤ p.length ∧
        ∀ tau :
            {rho : LinkTriangle //
              rho ∈ vertexLinkStarTriangles K v x},
          tau ∈ p.support := by
  obtain ⟨sigma, p, hpcycle, hpcover⟩ :=
    hcore.exists_vertexLinkStar_exact_coveringCycle_of_topologicalThreeManifold
      hM hrep
  refine ⟨sigma, p, hpcycle, hpcycle.three_le_length, ?_⟩
  intro tau
  rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
  rw [hpcover]
  exact Set.mem_univ tau

/-- The exact link-star cycle transported, without loss or duplication, to
the ambient represented tetrahedra containing the edge. -/
theorem ClosedTriangulationCore.exists_ambientEdgeCyclicFan_of_topologicalThreeManifold
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    Nonempty (AmbientEdgeCyclicFan K v x) := by
  classical
  obtain ⟨sigma0, p, hpcycle, hpcover⟩ :=
    hcore.exists_vertexLinkStar_exact_coveringCycle_of_topologicalThreeManifold hM hrep
  let tetAt :
      {sigma : LinkTriangle // sigma ∈ vertexLinkStarTriangles K v x} → Tet :=
    fun sigma => ambientTetOfVertexLinkTriangle K v
      ⟨sigma.1, (mem_vertexLinkStarTriangles_iff K v x sigma.1).1 sigma.2 |>.1⟩
  have hxv : x ≠ v := by
    obtain ⟨sigma, hsigma, hxsigma⟩ := hrep
    obtain ⟨tau, htau, hlink⟩ := (mem_vertexLinkTriangles_iff K v sigma).1 hsigma
    exact fun hxv =>
      tau.linkTriangleAt?_vertex_not_mem v sigma (hcore.1 tau htau) hlink
        (hxv ▸ hxsigma)
  refine ⟨{
    start := sigma0
    walk := p
    isCycle := hpcycle
    length_ge_three := hpcycle.three_le_length
    covers := ?_
    tetAt := tetAt
    tetAt_mem := ?_
    tetAt_link := ?_
    tetAt_injective := ?_
    covers_ambient := ?_ }⟩
  · intro sigma
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hpcover]
    exact Set.mem_univ sigma
  · intro sigma
    exact ambientTetOfVertexLinkTriangle_mem K v _
  · intro sigma
    exact ambientTetOfVertexLinkTriangle_linkTriangleAt K v _
  · intro sigma rho heq
    apply Subtype.ext
    have hfun := congrArg (fun tau : Tet => tau.linkTriangleAt? v) heq
    exact Option.some.inj (by simpa [tetAt,
      ambientTetOfVertexLinkTriangle_linkTriangleAt] using hfun)
  · intro tau htau hv hx
    obtain ⟨sigma, hsigma, hlink⟩ :=
      exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem K v tau htau hv
    have hxsigma : x ∈ sigma.verts :=
      (tau.mem_linkTriangleAt?_iff v x sigma hlink hxv).2 hx
    have hsstar : sigma ∈ vertexLinkStarTriangles K v x :=
      (mem_vertexLinkStarTriangles_iff K v x sigma).2 ⟨hsigma, hxsigma⟩
    refine ⟨⟨sigma, hsstar⟩, ?_⟩
    exact hcore.ambientTetOfVertexLinkTriangle_eq hsigma htau hlink

/-- The shared edge of every realized incidence-three `Move32Site` is carried
by the exact three-triangle cyclic fan supplied by the honest manifold
structure.  This is the compiler-visible bridge from the Move32 recurrence
objects to the cyclic edge-fan API. -/
theorem ClosedTriangulationCore.exists_move32Site_sharedEdge_exact_coveringCycle_of_topologicalThreeManifold
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hthree : s.SharedEdgeExactlyThree K) :
    (vertexLinkStarTriangles K s.d s.e).length = 3 ∧
      ∃
        (sigma :
          {tau : LinkTriangle //
            tau ∈ vertexLinkStarTriangles K s.d s.e}),
        ∃
          (p : (vertexLinkStarGraph K s.d s.e).Walk sigma sigma),
          p.IsCycle ∧
          p.toSubgraph.verts =
            (Set.univ :
              Set
                {tau : LinkTriangle //
                  tau ∈ vertexLinkStarTriangles K s.d s.e}) := by
  have hdistinct := hcore.move32Site_distinct s hrealized
  have hde : s.d ≠ s.e := by
    simp [List.nodup_cons] at hdistinct
    aesop
  have hrep : VertexLinkVertexRepresented K s.d s.e :=
    (hcore.vertexLinkVertexRepresented_and_star_length_three_of_edgeIncidence_three
      s.d s.e hde hthree).1
  exact
    ⟨(hcore.vertexLinkVertexRepresented_and_star_length_three_of_edgeIncidence_three
        s.d s.e hde hthree).2,
      hcore.exists_vertexLinkStar_exact_coveringCycle_of_topologicalThreeManifold
        hM hrep⟩

/-- Exact ambient fan-and-chord geometry attached to an incidence-three
shared edge. -/
structure Move32Site.AmbientFanChordCertificate
    (K : Triangulation) (s : Move32Site) where
  fan : AmbientEdgeCyclicFan K s.d s.e
  sigma : {t : LinkTriangle //
    t ∈ vertexLinkStarTriangles K s.d s.e}
  rho : {t : LinkTriangle //
    t ∈ vertexLinkStarTriangles K s.d s.e}
  adjacent : (vertexLinkStarGraph K s.d s.e).Adj sigma rho
  y : Nat
  z0 : Nat
  z1 : Nat
  move23 : Move23Site
  move23_a : move23.a = s.d
  move23_b : move23.b = s.e
  move23_c : move23.c = y
  move23_d : move23.d = z0
  move23_e : move23.e = z1
  left_ambient : SameTetVertices (fan.tetAt sigma) move23.leftTet
  right_ambient : SameTetVertices (fan.tetAt rho) move23.rightTet
  chord_status : move23.LegalIn K ∨
    ∃ tau ∈ K.tets, z0 ∈ tau.verts ∧ z1 ∈ tau.verts

theorem ClosedTriangulationCore.exists_ambientFanChordCertificate_of_move32Site
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (s : Move32Site) (hrealized : s.RealizedIn K)
    (hthree : s.SharedEdgeExactlyThree K) :
    Nonempty (s.AmbientFanChordCertificate K) := by
  classical
  have hdistinct := hcore.move32Site_distinct s hrealized
  have hde : s.d ≠ s.e := by
    simp [List.nodup_cons] at hdistinct
    aesop
  have hrep : VertexLinkVertexRepresented K s.d s.e :=
    (hcore.vertexLinkVertexRepresented_and_star_length_three_of_edgeIncidence_three
      s.d s.e hde hthree).1
  obtain ⟨F⟩ :=
    hcore.exists_ambientEdgeCyclicFan_of_topologicalThreeManifold hM hrep
  obtain ⟨sigma0, sigma1, sigma2, h01, h02, h12,
      hadj01, hadj02, hadj12⟩ :=
    hcore.exists_three_pairwiseAdjacent_vertexLinkStarTriangles_of_edgeIncidence_three
      s.d s.e hde hthree
  let sigma : {t : LinkTriangle //
      t ∈ vertexLinkStarTriangles K s.d s.e} := ⟨sigma0, hadj01.1⟩
  let rho : {t : LinkTriangle //
      t ∈ vertexLinkStarTriangles K s.d s.e} := ⟨sigma1, hadj01.2.1⟩
  have hsigmarho : sigma ≠ rho := by
    intro h
    exact h01 (congrArg Subtype.val h)
  have hadj : (vertexLinkStarGraph K s.d s.e).Adj sigma rho :=
    (vertexLinkStarGraph_adj K s.d s.e sigma rho).2 ⟨hsigmarho, hadj01⟩
  obtain ⟨y, z0, z1, m, ha, hb, hc, hd, he,
      hleft, hright, hstatus⟩ :=
    hcore.ambientEdgeCyclicFan_adjacent_exists_legalMove23_or_representedChord
      F hadj
  exact ⟨{
    fan := F, sigma := sigma, rho := rho, adjacent := hadj,
    y := y, z0 := z0, z1 := z1, move23 := m,
    move23_a := ha, move23_b := hb, move23_c := hc,
    move23_d := hd, move23_e := he,
    left_ambient := hleft, right_ambient := hright,
    chord_status := hstatus }⟩

end Poincare
