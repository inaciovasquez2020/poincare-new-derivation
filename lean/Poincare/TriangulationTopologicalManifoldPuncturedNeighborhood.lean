import Poincare.TriangulationTopologicalVertexStarRadialAccess
import Poincare.TriangulationTopologicalHonestManifold
import Poincare.SpherePolygonalApproximation
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

open Set Filter Metric
open scoped Manifold

namespace Poincare

/-- A punctured open ball in the three-dimensional Euclidean model is simply connected. -/
theorem threeManifoldModel_isSimplyConnected_ball_diff_singleton
    (y : ThreeManifoldModel) {ε : ℝ} (hε : 0 < ε) :
    IsSimplyConnected (Metric.ball y ε \ {y}) := by
  let e : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    OpenPartialHomeomorph.univBall y ε
  have hsource : ({0}ᶜ : Set ThreeManifoldModel) ⊆ e.source := by
    simp [e]
  have himage : e '' ({0}ᶜ : Set ThreeManifoldModel) = Metric.ball y ε \ {y} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwsource : w ∈ e.source := hsource hw
      have hew : e w ∈ Metric.ball y ε := by
        rw [← OpenPartialHomeomorph.univBall_target y hε]
        exact e.map_source hwsource
      refine ⟨hew, ?_⟩
      simp only [mem_singleton_iff]
      intro heq
      have : w = 0 := by
        apply e.injOn hwsource (by simp [e])
        simpa [e] using heq
      exact hw this
    · rintro ⟨hzball, hzne⟩
      have hztarget : z ∈ e.target := by
        simpa [e, OpenPartialHomeomorph.univBall_target y hε] using hzball
      refine ⟨e.symm z, ?_, e.right_inv hztarget⟩
      simp only [mem_compl_iff, mem_singleton_iff]
      intro heq
      have : z = y := by
        rw [← e.right_inv hztarget, heq]
        simp [e]
      exact hzne this
  let h := e.homeomorphOfImageSubsetSource hsource himage
  haveI : SimplyConnectedSpace ({0}ᶜ : Set ThreeManifoldModel) :=
    euclideanSpace3_punctured_isSimplyConnected
  exact h.symm.toHomotopyEquiv.simplyConnectedSpace

/-- A punctured open ball in the three-dimensional Euclidean model is path-connected. -/
theorem threeManifoldModel_isPathConnected_ball_diff_singleton
    (y : ThreeManifoldModel) {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (Metric.ball y ε \ {y}) := by
  let e : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    OpenPartialHomeomorph.univBall y ε
  have hrank : 1 < Module.rank ℝ ThreeManifoldModel := by
    rw [← Module.finrank_eq_rank]
    norm_num [ThreeManifoldModel]
  have hpath : IsPathConnected ({0}ᶜ : Set ThreeManifoldModel) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  rw [← show e '' ({0}ᶜ : Set ThreeManifoldModel) = Metric.ball y ε \ {y} by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwsource : w ∈ e.source := by simp [e]
      have hew : e w ∈ Metric.ball y ε := by
        rw [← OpenPartialHomeomorph.univBall_target y hε]
        exact e.map_source hwsource
      refine ⟨hew, ?_⟩
      simp only [mem_singleton_iff]
      intro heq
      have : w = 0 := by
        apply e.injOn hwsource (by simp [e])
        simpa [e] using heq
      exact hw this
    · rintro ⟨hzball, hzne⟩
      have hztarget : z ∈ e.target := by
        simpa [e, OpenPartialHomeomorph.univBall_target y hε] using hzball
      refine ⟨e.symm z, ?_, e.right_inv hztarget⟩
      simp only [mem_compl_iff, mem_singleton_iff]
      intro heq
      have : z = y := by
        rw [← e.right_inv hztarget, heq]
        simp [e]
      exact hzne this]
  exact hpath.image' (e.continuousOn.mono (by simp [e]))

/-- Around every point of an honest topological three-manifold carrier there
is an arbitrarily small open neighborhood whose puncture is simply connected.
The neighborhood is the inverse image of a Euclidean chart ball. -/
theorem triangulationTopological_exists_open_punctured_simplyConnected_neighborhood_sub
    (K : Triangulation)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (x : triangulationTopologicalGeometricCarrier K)
    {N : Set (triangulationTopologicalGeometricCarrier K)}
    (hN : N ∈ nhds x) :
    ∃ U : Set (triangulationTopologicalGeometricCarrier K),
      IsOpen U ∧ x ∈ U ∧ U ⊆ N ∧ IsSimplyConnected (U \ {x}) := by
  rcases hM with ⟨hT2, hcharted, hmanifold, _hcompact, _hconnected⟩
  letI := hT2
  letI := hcharted
  letI := hmanifold
  let e : OpenPartialHomeomorph
      (triangulationTopologicalGeometricCarrier K) ThreeManifoldModel :=
    chartAt ThreeManifoldModel x
  have hxsource : x ∈ e.source := by
    simp [e]
  have himageN : e '' (e.source ∩ N) ∈ nhds (e x) :=
    e.image_mem_nhds hxsource (inter_mem (e.open_source.mem_nhds hxsource) hN)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himageN
  let U : Set (triangulationTopologicalGeometricCarrier K) :=
    e.symm '' Metric.ball (e x) ε
  have hballtarget : Metric.ball (e x) ε ⊆ e.target := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hball hz
    exact e.map_source hp.1
  have hUopen : IsOpen U :=
    e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballtarget
  have hxU : x ∈ U := by
    exact ⟨e x, Metric.mem_ball_self hε, e.left_inv hxsource⟩
  have hUsub : U ⊆ N := by
    rintro p ⟨z, hzball, rfl⟩
    obtain ⟨q, hq, hqeq⟩ := hball hzball
    have hqeq' : q = e.symm z := by
      rw [← hqeq]
      exact (e.left_inv hq.1).symm
    simpa [hqeq'] using hq.2
  have himage : e.symm '' (Metric.ball (e x) ε \ {e x}) = U \ {x} := by
    ext p
    constructor
    · rintro ⟨z, ⟨hzball, hzne⟩, rfl⟩
      have hztarget : z ∈ e.target := hballtarget hzball
      refine ⟨⟨z, hzball, rfl⟩, ?_⟩
      simp only [mem_singleton_iff]
      intro heq
      have : z = e x := by
        rw [← e.right_inv hztarget, heq]
      exact hzne this
    · rintro ⟨⟨z, hzball, rfl⟩, hpne⟩
      refine ⟨z, ⟨hzball, ?_⟩, rfl⟩
      simp only [mem_singleton_iff]
      intro hzeq
      apply hpne
      simpa [hzeq] using e.left_inv hxsource
  let h := e.symm.homeomorphOfImageSubsetSource
    (fun z hz ↦ hballtarget hz.1) himage
  haveI : SimplyConnectedSpace ↑(Metric.ball (e x) ε \ {e x}) :=
    threeManifoldModel_isSimplyConnected_ball_diff_singleton (e x) hε
  exact ⟨U, hUopen, hxU, hUsub, h.symm.toHomotopyEquiv.simplyConnectedSpace⟩

/-- Around every point of an honest topological three-manifold carrier there
is an arbitrarily small open neighborhood whose puncture is connected.  The
neighborhood is chosen as the inverse image of a Euclidean chart ball, so this
form is suitable for later carrier-local and radial-star arguments. -/
theorem triangulationTopological_exists_open_punctured_connected_neighborhood_sub
    (K : Triangulation)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (x : triangulationTopologicalGeometricCarrier K)
    {N : Set (triangulationTopologicalGeometricCarrier K)}
    (hN : N ∈ nhds x) :
    ∃ U : Set (triangulationTopologicalGeometricCarrier K),
      IsOpen U ∧ x ∈ U ∧ U ⊆ N ∧ IsConnected (U \ {x}) := by
  rcases hM with ⟨hT2, hcharted, hmanifold, _hcompact, _hconnected⟩
  letI := hT2
  letI := hcharted
  letI := hmanifold
  let e : OpenPartialHomeomorph
      (triangulationTopologicalGeometricCarrier K) ThreeManifoldModel :=
    chartAt ThreeManifoldModel x
  have hxsource : x ∈ e.source := by
    simp [e]
  have himage : e '' (e.source ∩ N) ∈ nhds (e x) :=
    e.image_mem_nhds hxsource (inter_mem (e.open_source.mem_nhds hxsource) hN)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himage
  let U : Set (triangulationTopologicalGeometricCarrier K) :=
    e.symm '' Metric.ball (e x) ε
  have hballtarget : Metric.ball (e x) ε ⊆ e.target := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hball hz
    exact e.map_source hp.1
  have hUopen : IsOpen U :=
    e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballtarget
  have hxU : x ∈ U := by
    exact ⟨e x, Metric.mem_ball_self hε, e.left_inv hxsource⟩
  have hUsub : U ⊆ N := by
    rintro p ⟨z, hzball, rfl⟩
    obtain ⟨q, hq, hqeq⟩ := hball hzball
    have hqeq' : q = e.symm z := by
      rw [← hqeq]
      exact (e.left_inv hq.1).symm
    simpa [hqeq'] using hq.2
  have hpuncturedPath : IsPathConnected (U \ {x}) := by
    have hmodel := threeManifoldModel_isPathConnected_ball_diff_singleton (e x) hε
    rw [← show e.symm '' (Metric.ball (e x) ε \ {e x}) = U \ {x} by
      ext p
      constructor
      · rintro ⟨z, ⟨hzball, hzne⟩, rfl⟩
        have hztarget : z ∈ e.target := hballtarget hzball
        refine ⟨⟨z, hzball, rfl⟩, ?_⟩
        simp only [mem_singleton_iff]
        intro heq
        have : z = e x := by
          rw [← e.right_inv hztarget, heq]
        exact hzne this
      · rintro ⟨⟨z, hzball, rfl⟩, hpne⟩
        refine ⟨z, ⟨hzball, ?_⟩, rfl⟩
        simp only [mem_singleton_iff]
        intro hzeq
        apply hpne
        simpa [hzeq] using e.left_inv hxsource]
    exact hmodel.image' ((e.continuousOn_symm).mono
      (fun z hz ↦ hballtarget hz.1))
  exact ⟨U, hUopen, hxU, hUsub, hpuncturedPath.isConnected⟩

/-- Every represented vertex in an honest topological three-manifold has an open
carrier neighborhood, contained in its represented star, whose puncture is connected. -/
theorem triangulationTopological_exists_open_punctured_connected_neighborhood
    (K : Triangulation)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v : Nat} (hv : v ∈ vertexSupport K) :
    ∃ U : Set (triangulationTopologicalGeometricCarrier K),
      IsOpen U ∧
      triangulationTopologicalCarrierVertex K v hv ∈ U ∧
      (∀ p ∈ U, p.1 ∈ triangulationTopologicalVertexStar K v) ∧
      IsConnected (U \ {triangulationTopologicalCarrierVertex K v hv}) := by
  let x := triangulationTopologicalCarrierVertex K v hv
  let N := triangulationTopologicalTruncatedVertexStarNeighborhood K v
  have hNnhds : N ∈ nhds x := by
    simpa [N, x] using
      triangulationTopologicalTruncatedVertexStarNeighborhood_mem_nhds K hv
  obtain ⟨U, hUopen, hxU, hUN, hUconnected⟩ :=
    triangulationTopological_exists_open_punctured_connected_neighborhood_sub
      K hM x hNnhds
  refine ⟨U, hUopen, by simpa [x] using hxU, ?_, by simpa [x] using hUconnected⟩
  intro p hp
  apply triangulationTopologicalTruncatedVertexStarNeighborhood_subset_vertexStar K v
  exact hUN hp

end Poincare
