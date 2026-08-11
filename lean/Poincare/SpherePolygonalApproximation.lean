import Poincare.SphereNormalizedChord
import Poincare.SphereFiniteEscape
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.Path
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Product

namespace Poincare

open scoped unitInterval

/-- A uniformly short sphere subpath is homotopic, relative to its endpoints, to the
normalized chord joining those endpoints.  The deliberately separated bounds are
the form produced by uniform subdivision and by the normalized-chord estimate. -/
theorem Path.subpath_homotopic_normalizedChord_of_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) (a b : unitInterval)
    (hab : dist (p a : E) (p b : E) < (1 : ℝ) / 4)
    (hsub : ∀ s : unitInterval,
      dist ((p.subpath a b) s : E) (p a : E) < (1 : ℝ) / 2) :
    Path.Homotopic (p.subpath a b)
      (normalizedChord (p a : E) (p b : E)
        (by simp)
        (by simp)
        (by linarith)) := by
  let hu : ‖(p a : E)‖ = 1 := by
    simp
  let hv : ‖(p b : E)‖ = 1 := by
    simp
  let huv : dist (p a : E) (p b : E) < 2 := by linarith
  apply normalizedStraight_pathHomotopic
  intro s
  calc
    dist ((p.subpath a b) s : E)
        ((normalizedChord (p a : E) (p b : E) hu hv huv) s : E) ≤
        dist ((p.subpath a b) s : E) (p a : E) +
          dist (p a : E)
            ((normalizedChord (p a : E) (p b : E) hu hv huv) s : E) :=
      dist_triangle _ _ _
    _ < 2 := by
      rw [dist_comm (p a : E)]
      have hchord := dist_normalizedChord_source_le_two_mul hu hv huv s
      have hs := hsub s
      linarith

/-- A path admits a positive uniform subdivision count on whose parameter scale its
image has diameter less than `1 / 4`. -/
theorem Path.exists_subdivision_dist_lt_quarter
    {X : Type*} [PseudoMetricSpace X] {x y : X} (p : Path x y) :
    ∃ n : ℕ, 0 < n ∧ ∀ s t : unitInterval,
      dist (s : ℝ) (t : ℝ) ≤ 1 / (n : ℝ) → dist (p s) (p t) < (1 : ℝ) / 4 := by
  obtain ⟨δ, hδ, hp⟩ := Metric.uniformContinuous_iff.mp p.uniformContinuous
    ((1 : ℝ) / 4) (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m + 1, Nat.succ_pos m, fun s t hst ↦ hp ?_⟩
  exact lt_of_le_of_lt hst (by simpa using hm)

/-- A path has a finite sequence of equally spaced sampled vertices whose consecutive
vertices are less than `1 / 4` apart. -/
theorem Path.exists_sampled_vertices_dist_lt_quarter
    {X : Type*} [PseudoMetricSpace X] {x y : X} (p : Path x y) :
    ∃ n : ℕ, 0 < n ∧ ∃ v : Fin (n + 1) → unitInterval,
      v 0 = 0 ∧ v (Fin.last n) = 1 ∧
        ∀ i : Fin n, dist (p (v i.castSucc)) (p (v i.succ)) < (1 : ℝ) / 4 := by
  obtain ⟨n, hn, hp⟩ := Path.exists_subdivision_dist_lt_quarter p
  let v : Fin (n + 1) → unitInterval := fun i ↦
    ⟨(i : ℝ) / n, by
      constructor
      · positivity
      · rw [div_le_one (by exact_mod_cast hn)]
        have hi : (i : ℕ) ≤ n := by omega
        exact_mod_cast hi⟩
  refine ⟨n, hn, v, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp [v]
  · apply Subtype.ext
    simp [v, hn.ne']
  · intro i
    apply hp
    rw [Real.dist_eq]
    simp only [v]
    rw [show ((i.succ : Fin (n + 1)) : ℝ) = (i : ℝ) + 1 by norm_num,
      add_div, one_div]
    simp

/-- A sphere-valued path has uniformly short sampled edges whose normalized chord
stays within `1 / 2` of the source vertex.  This is the quantitative local input for
homotoping each sampled subpath to its polygonal replacement. -/
theorem Path.exists_sampled_sphere_vertices_normalizedChord_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) :
    ∃ n : ℕ, 0 < n ∧ ∃ v : Fin (n + 1) → unitInterval,
      v 0 = 0 ∧ v (Fin.last n) = 1 ∧
        ∀ i : Fin n,
          dist (p (v i.castSucc) : E) (p (v i.succ) : E) < (1 : ℝ) / 4 ∧
          ∃ huv : dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2,
            ∀ s : unitInterval,
              dist
                  ((normalizedChord
                    (p (v i.castSucc) : E) (p (v i.succ) : E)
                    (by simp)
                    (by simp)
                    huv) s : E)
                  (p (v i.castSucc) : E) < (1 : ℝ) / 2 := by
  obtain ⟨n, hn, v, hv0, hv1, hv⟩ := Path.exists_sampled_vertices_dist_lt_quarter p
  have hedge (i : Fin n) :
      dist (p (v i.castSucc) : E) (p (v i.succ) : E) < (1 : ℝ) / 4 := by
    simpa [Subtype.dist_eq] using hv i
  refine ⟨n, hn, v, hv0, hv1, fun i ↦ ⟨hedge i, ?_⟩⟩
  have hu : ‖(p (v i.castSucc) : E)‖ = 1 := by
    simp
  have hw : ‖(p (v i.succ) : E)‖ = 1 := by
    simp
  have huv : dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2 := by
    linarith [hedge i]
  refine ⟨huv, fun s ↦ ?_⟩
  exact lt_of_le_of_lt
    (dist_normalizedChord_source_le_two_mul hu hw huv s) (by linarith [hedge i])

/-- A sphere-valued path admits an equally spaced finite subdivision on which every
subpath is homotopic, relative to its endpoints, to the normalized chord between
its sampled endpoints. -/
theorem Path.exists_sampled_subpath_homotopic_normalizedChord
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) :
    ∃ n : ℕ, 0 < n ∧ ∃ v : Fin (n + 1) → unitInterval,
      v 0 = 0 ∧ v (Fin.last n) = 1 ∧
        ∀ i : Fin n,
          ∃ huv : dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2,
            Path.Homotopic (p.subpath (v i.castSucc) (v i.succ))
              (normalizedChord (p (v i.castSucc) : E) (p (v i.succ) : E)
                (by simp)
                (by simp) huv) := by
  obtain ⟨n, hn, hp⟩ := Path.exists_subdivision_dist_lt_quarter p
  let v : Fin (n + 1) → unitInterval := fun i ↦
    ⟨(i : ℝ) / n, by
      constructor
      · positivity
      · rw [div_le_one (by exact_mod_cast hn)]
        have hi : (i : ℕ) ≤ n := by omega
        exact_mod_cast hi⟩
  have hvstep (i : Fin n) :
      dist (v i.castSucc : ℝ) (v i.succ : ℝ) = 1 / (n : ℝ) := by
    rw [Real.dist_eq]
    simp only [v]
    rw [show ((i.succ : Fin (n + 1)) : ℝ) = (i : ℝ) + 1 by norm_num,
      add_div, one_div]
    simp
  refine ⟨n, hn, v, ?_, ?_, fun i ↦ ?_⟩
  · apply Subtype.ext
    simp [v]
  · apply Subtype.ext
    simp [v, hn.ne']
  · have hedge : dist (p (v i.castSucc) : E) (p (v i.succ) : E) < (1 : ℝ) / 4 := by
      exact hp _ _ (le_of_eq (hvstep i))
    have huv : dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2 := by
      linarith
    refine ⟨huv, Path.subpath_homotopic_normalizedChord_of_close p _ _ hedge ?_⟩
    intro s
    have hparam :
        dist (Set.Icc.convexCombo (v i.castSucc) (v i.succ) s : ℝ)
          (v i.castSucc : ℝ) ≤ 1 / (n : ℝ) := by
      rw [Real.dist_eq]
      change |((1 - (s : ℝ)) * (v i.castSucc : ℝ) +
        (s : ℝ) * (v i.succ : ℝ)) - (v i.castSucc : ℝ)| ≤ _
      rw [show (1 - (s : ℝ)) * (v i.castSucc : ℝ) +
          (s : ℝ) * (v i.succ : ℝ) - (v i.castSucc : ℝ) =
          (s : ℝ) * ((v i.succ : ℝ) - (v i.castSucc : ℝ)) by ring,
        abs_mul, abs_of_nonneg s.property.1]
      have hs : (s : ℝ) ≤ 1 := s.property.2
      rw [← Real.dist_eq, dist_comm, hvstep i]
      exact mul_le_of_le_one_left (by positivity) hs
    have hclose := hp (Set.Icc.convexCombo (v i.castSucc) (v i.succ) s)
      (v i.castSucc) hparam
    have hclose' :
        dist ((p.subpath (v i.castSucc) (v i.succ)) s : E)
          (p (v i.castSucc) : E) < (1 : ℝ) / 4 := by
      simpa [Path.subpath, Subtype.dist_eq] using hclose
    linarith

/-- The polygonal path obtained by concatenating the normalized chords between
consecutive sampled vertices of a sphere-valued path. -/
noncomputable def normalizedChordChain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) {n : ℕ}
    (v : Fin (n + 1) → unitInterval)
    (huv : ∀ i : Fin n,
      dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2) :
    Path (p (v 0)) (p (v (Fin.last n))) :=
  Path.concat (p ∘ v) fun i ↦
    normalizedChord (p (v i.castSucc) : E) (p (v i.succ) : E)
      (by simp)
      (by simp) (huv i)

@[simp] theorem normalizedChordChain_start
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) {n : ℕ}
    (v : Fin (n + 1) → unitInterval)
    (huv : ∀ i : Fin n,
      dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2) :
    normalizedChordChain p v huv 0 = p (v 0) :=
  (normalizedChordChain p v huv).source

@[simp] theorem normalizedChordChain_end
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) {n : ℕ}
    (v : Fin (n + 1) → unitInterval)
    (huv : ∀ i : Fin n,
      dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2) :
    normalizedChordChain p v huv 1 = p (v (Fin.last n)) :=
  (normalizedChordChain p v huv).target

/-- Replacing every sampled subpath by its normalized chord replaces their
finite concatenation by a path-homotopic polygonal chain. -/
theorem normalizedChordChain_homotopic_sampledPath
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) {n : ℕ}
    (v : Fin (n + 1) → unitInterval)
    (huv : ∀ i : Fin n,
      dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2)
    (hedge : ∀ i : Fin n,
      Path.Homotopic (p.subpath (v i.castSucc) (v i.succ))
        (normalizedChord (p (v i.castSucc) : E) (p (v i.succ) : E)
          (by simp)
          (by simp) (huv i))) :
    Path.Homotopic (p.subpath (v 0) (v (Fin.last n)))
      (normalizedChordChain p v huv) := by
  exact (Path.Homotopic.concat_subpath p v).symm.trans
    (Path.Homotopic.concat_hcomp (p ∘ v)
      (fun i ↦ p.subpath (v i.castSucc) (v i.succ))
      (fun i ↦ normalizedChord (p (v i.castSucc) : E) (p (v i.succ) : E)
        (by simp)
        (by simp) (huv i)) hedge)

/-- Every sphere-valued path is homotopic relative to its endpoints to a finite
polygon whose edges are normalized chords between explicitly sampled vertices. -/
theorem Path.exists_normalizedChordPolygon_homotopic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) :
    ∃ n : ℕ, 0 < n ∧ ∃ v : Fin (n + 1) → unitInterval,
      v 0 = 0 ∧ v (Fin.last n) = 1 ∧
      ∃ huv : ∀ i : Fin n,
        dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2,
      ∃ h0 : x = p (v 0), ∃ h1 : y = p (v (Fin.last n)),
      ∃ q : Path x y,
        q = (normalizedChordChain p v huv).cast h0 h1 ∧
        Path.Homotopic p q := by
  obtain ⟨n, hn, v, hv0, hv1, hedge⟩ :=
    Path.exists_sampled_subpath_homotopic_normalizedChord p
  choose huv hhom using hedge
  have h0 : x = p (v 0) := by simp [hv0]
  have h1 : y = p (v (Fin.last n)) := by simp [hv1]
  refine ⟨n, hn, v, hv0, hv1, huv, h0, h1,
    (normalizedChordChain p v huv).cast h0 h1, rfl, ?_⟩
  have hchain := normalizedChordChain_homotopic_sampledPath p v huv hhom
  have hcast := hchain.pathCast h0 h1
  have heq : (p.subpath (v 0) (v (Fin.last n))).cast h0 h1 = p := by
    ext t
    simp [Path.subpath, hv0, hv1]
  rw [heq] at hcast
  exact hcast

private theorem Path.concat_mem_of_edges
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (z : Fin (n + 1) → X)
    (F : (i : Fin n) → Path (z i.castSucc) (z i.succ))
    (S : Fin n → Set X) (hn : 0 < n)
    (hF : ∀ i t, F i t ∈ S i) :
    ∀ t, ∃ i, Path.concat z F t ∈ S i := by
  induction n with
  | zero => omega
  | succ n ih =>
      intro t
      rw [Path.concat_succ]
      let G := (Path.concat (z ∘ Fin.castSucc) (fun k ↦ F k.castSucc)).trans
        (F (Fin.last n))
      change ∃ i, G t ∈ S i
      have htmem :
          G t ∈
            Set.range (Path.concat (z ∘ Fin.castSucc) (fun k ↦ F k.castSucc)) ∪
              Set.range (F (Fin.last n)) := by
        have htG : G t ∈ Set.range G := Set.mem_range_self t
        have hGrange : Set.range G =
            Set.range (Path.concat (z ∘ Fin.castSucc) (fun k ↦ F k.castSucc)) ∪
              Set.range (F (Fin.last n)) := by
          exact Path.trans_range _ _
        rwa [hGrange] at htG
      rcases htmem with ⟨s, hs⟩ | ⟨s, hs⟩
      · cases n with
        | zero =>
            refine ⟨Fin.last 0, ?_⟩
            have heq : G t = F (Fin.last 0) 0 := by
              calc
                G t = Path.concat (z ∘ Fin.castSucc) (fun k ↦ F k.castSucc) s := hs.symm
                _ = z 0 := by
                  rw [Path.concat_zero]
                  rfl
                _ = F (Fin.last 0) 0 := (F (Fin.last 0)).source.symm
            rw [heq]
            exact hF (Fin.last 0) 0
        | succ n =>
            obtain ⟨i, hi⟩ := ih (z ∘ Fin.castSucc)
              (fun k ↦ F k.castSucc) (fun k ↦ S k.castSucc) (by omega)
              (fun i t ↦ hF i.castSucc t) s
            exact ⟨i.castSucc, hs ▸ hi⟩
      · exact ⟨Fin.last n, hs ▸ hF (Fin.last n) s⟩

/-- Every point of a normalized-chord polygon lies in the span of the two sampled
vertices of one of its consecutive edges. -/
theorem normalizedChordPolygon_mem_pairSpan
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) {n : ℕ} (hn : 0 < n)
    (v : Fin (n + 1) → unitInterval)
    (huv : ∀ i : Fin n,
      dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2)
    (t : unitInterval) :
    ∃ i : Fin n, ((normalizedChordChain p v huv t :
        Metric.sphere (0 : E) 1) : E) ∈
      Submodule.span ℝ ({(p (v i.castSucc) : E), (p (v i.succ) : E)} : Set E) := by
  refine Path.concat_mem_of_edges (p ∘ v)
    (fun i ↦ normalizedChord (p (v i.castSucc) : E) (p (v i.succ) : E)
      (by simp)
      (by simp) (huv i))
    (fun i ↦ {z : Metric.sphere (0 : E) 1 |
      (z : E) ∈ Submodule.span ℝ
        ({(p (v i.castSucc) : E), (p (v i.succ) : E)} : Set E)}) hn ?_ t
  intro i s
  change ‖(1 - (s : ℝ)) • (p (v i.castSucc) : E) +
      (s : ℝ) • (p (v i.succ) : E)‖⁻¹ •
        ((1 - (s : ℝ)) • (p (v i.castSucc) : E) +
          (s : ℝ) • (p (v i.succ) : E)) ∈
      Submodule.span ℝ
        ({(p (v i.castSucc) : E), (p (v i.succ) : E)} : Set E)
  apply Submodule.smul_mem
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- A normalized-chord polygon in the unit two-sphere avoids the antipode of
some unit vector.  The avoiding vector is chosen outside all of the finitely
many planes spanned by consecutive sampled vertices. -/
theorem exists_sphere_point_not_mem_normalizedChordPolygon
    {x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} (p : Path x y)
    {n : ℕ} (hn : 0 < n) (v : Fin (n + 1) → unitInterval)
    (huv : ∀ i : Fin n,
      dist (p (v i.castSucc) : EuclideanSpace ℝ (Fin 3))
        (p (v i.succ) : EuclideanSpace ℝ (Fin 3)) < 2) :
    ∃ a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ t : unitInterval, normalizedChordChain p v huv t ≠
        (⟨-(a : EuclideanSpace ℝ (Fin 3)), by
          simp⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  obtain ⟨a, ha, havoid⟩ := exists_unit_not_mem_finset_pairSpans Finset.univ
    (fun i : Fin n ↦ (p (v i.castSucc) : EuclideanSpace ℝ (Fin 3)))
    (fun i : Fin n ↦ (p (v i.succ) : EuclideanSpace ℝ (Fin 3)))
  let a' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ⟨a, by simpa [Metric.mem_sphere] using ha⟩
  refine ⟨a', fun t heq ↦ ?_⟩
  obtain ⟨i, hi⟩ := normalizedChordPolygon_mem_pairSpan p hn v huv t
  have hneg : -a ∈ Submodule.span ℝ
      ({(p (v i.castSucc) : EuclideanSpace ℝ (Fin 3)),
        (p (v i.succ) : EuclideanSpace ℝ (Fin 3))} :
        Set (EuclideanSpace ℝ (Fin 3))) := by
    have heq' : ((normalizedChordChain p v huv t :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) = -a := by
      simpa [a'] using congrArg
        (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
          (z : EuclideanSpace ℝ (Fin 3))) heq
    rw [heq'] at hi
    exact hi
  have ha_mem := (Submodule.span ℝ
    ({(p (v i.castSucc) : EuclideanSpace ℝ (Fin 3)),
      (p (v i.succ) : EuclideanSpace ℝ (Fin 3))} :
      Set (EuclideanSpace ℝ (Fin 3)))).neg_mem hneg
  exact havoid i (Finset.mem_univ i) (by simpa using ha_mem)

/-- Removing one point from a unit sphere in a real inner product space leaves a
contractible space.  Stereographic projection identifies the complement of the
point with the full orthogonal-complement vector space. -/
theorem unitSphere_punctured_contractible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : Metric.sphere (0 : E) 1) :
    ContractibleSpace {z : Metric.sphere (0 : E) 1 // z ≠ a} := by
  let ha : ‖(a : E)‖ = 1 := by
    simp
  haveI : ContractibleSpace (stereographic ha).target := by
    rw [stereographic_target]
    exact convex_univ.contractibleSpace Set.univ_nonempty
  haveI : ContractibleSpace (stereographic ha).source :=
    (stereographic ha).toHomeomorphSourceTarget.contractibleSpace
  simpa [stereographic_source] using
    (inferInstance : ContractibleSpace (stereographic ha).source)

/-- A loop on a unit sphere that avoids one point is null-homotopic relative to
its basepoint.  The loop lifts to the punctured sphere, which is contractible,
and its path homotopy maps back along the subtype inclusion. -/
theorem Path.homotopic_refl_of_avoids_unitSphere_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : Metric.sphere (0 : E) 1} (q : Path x x)
    (a : Metric.sphere (0 : E) 1) (havoid : ∀ t, q t ≠ a) :
    Path.Homotopic q (Path.refl x) := by
  let X := {z : Metric.sphere (0 : E) 1 // z ≠ a}
  let x' : X := ⟨x, by simpa using havoid 0⟩
  let q' : Path x' x' :=
    { toFun := fun t ↦ ⟨q t, havoid t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  let inclusion : C(X, Metric.sphere (0 : E) 1) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  letI : ContractibleSpace X := unitSphere_punctured_contractible a
  have hq' : Path.Homotopic q' (Path.refl x') :=
    SimplyConnectedSpace.paths_homotopic q' (Path.refl x')
  simpa [q', x', inclusion] using hq'.map inclusion

/-- Every loop on the unit two-sphere is null-homotopic relative to its
basepoint.  Replace the loop by a finite normalized-chord polygon, choose a
sphere point missed by that polygon, and contract inside its complement. -/
theorem unitSphere3_loop_nullhomotopic
    {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (p : Path x x) :
    p.Homotopic (Path.refl x) := by
  obtain ⟨n, hn, v, hv0, hv1, huv, h0, h1, q, hq, hpq⟩ :=
    Path.exists_normalizedChordPolygon_homotopic p
  obtain ⟨a, ha⟩ :=
    exists_sphere_point_not_mem_normalizedChordPolygon p hn v huv
  let b : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ⟨-(a : EuclideanSpace ℝ (Fin 3)), by
      simp⟩
  have hqavoid : ∀ t, q t ≠ b := by
    intro t
    rw [hq]
    simp [b, ha]
  exact hpq.trans
    (Path.homotopic_refl_of_avoids_unitSphere_point q b hqavoid)

/-- The unit two-sphere in Euclidean three-space is simply connected. -/
theorem unitSphere3_simplyConnected :
    SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank']
    norm_num
  haveI : PathConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere hrank 0 zero_le_one)
  rw [simply_connected_iff_loops_nullhomotopic]
  exact ⟨inferInstance, fun _ p ↦ unitSphere3_loop_nullhomotopic p⟩

private theorem simplyConnectedSpace_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] :
    SimplyConnectedSpace (X × Y) := by
  rw [simply_connected_iff_unique_homotopic]
  refine ⟨inferInstance, ?_⟩
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  let q₀ := Path.Homotopic.prod
    (⟦PathConnectedSpace.somePath a₁ b₁⟧ : Path.Homotopic.Quotient a₁ b₁)
    (⟦PathConnectedSpace.somePath a₂ b₂⟧ : Path.Homotopic.Quotient a₂ b₂)
  refine ⟨⟨⟨q₀⟩, fun q ↦ ?_⟩⟩
  rw [← Path.Homotopic.prod_projLeft_projRight q]
  change Path.Homotopic.prod _ _ = q₀
  congr <;> apply Subsingleton.elim

/-- Euclidean three-space with the origin removed is simply connected.  Polar
coordinates identify it with the simply connected unit two-sphere times the
contractible positive radial interval. -/
theorem euclideanSpace3_punctured_isSimplyConnected :
    IsSimplyConnected
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) := by
  letI : SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    unitSphere3_simplyConnected
  letI : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi 0).contractibleSpace ⟨1, by simp⟩
  letI : SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Ioi (0 : ℝ)) :=
    simplyConnectedSpace_prod
  exact (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))).toHomotopyEquiv
    |>.simplyConnectedSpace

end Poincare
