import Poincare.FourSimplexBoundaryCombinatorialCertificate
import Poincare.FourSimplexSphere
import Poincare.TriangulationTopologicalGeometricCompactness

open Set

namespace Poincare

/-- The five certified vertices, in the order used by the standard four-simplex. -/
def fourSimplexBoundaryLabel (a b c d e : Nat) : Fin 5 → Nat :=
  [a, b, c, d, e].get

@[simp] theorem fourSimplexBoundaryLabel_zero (a b c d e : Nat) :
    fourSimplexBoundaryLabel a b c d e 0 = a := rfl
@[simp] theorem fourSimplexBoundaryLabel_one (a b c d e : Nat) :
    fourSimplexBoundaryLabel a b c d e 1 = b := rfl
@[simp] theorem fourSimplexBoundaryLabel_two (a b c d e : Nat) :
    fourSimplexBoundaryLabel a b c d e 2 = c := rfl
@[simp] theorem fourSimplexBoundaryLabel_three (a b c d e : Nat) :
    fourSimplexBoundaryLabel a b c d e 3 = d := rfl
@[simp] theorem fourSimplexBoundaryLabel_four (a b c d e : Nat) :
    fourSimplexBoundaryLabel a b c d e 4 = e := rfl

theorem fourSimplexBoundaryLabel_injective {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) :
    Function.Injective (fourSimplexBoundaryLabel a b c d e) :=
  h.injective_get

/-- Finite-coordinate linear realization change from the Pi-space to the
standard affine four-simplex ambient space. -/
noncomputable def fourSimplexBoundaryPiLinearMap (a b c d e : Nat) :
    (Nat → ℝ) →ₗ[ℝ] FourSimplexAmbient where
  toFun p := ∑ i : Fin 5,
    p (fourSimplexBoundaryLabel a b c d e i) • fourSimplexAffineBasis i
  map_add' p q := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r p := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum]

@[simp] theorem fourSimplexBoundaryPiLinearMap_basisVertex
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) (i : Fin 5) :
    fourSimplexBoundaryPiLinearMap a b c d e
        (triangulationTopologicalGeometricVertex
          (fourSimplexBoundaryLabel a b c d e i)) =
      fourSimplexAffineBasis i := by
  classical
  unfold fourSimplexBoundaryPiLinearMap
  change (∑ j : Fin 5,
      triangulationTopologicalGeometricVertex
          (fourSimplexBoundaryLabel a b c d e i)
          (fourSimplexBoundaryLabel a b c d e j) •
        fourSimplexAffineBasis j) = _
  rw [Fintype.sum_eq_single i]
  · simp [triangulationTopologicalGeometricVertex]
  · intro j hji
    have hlabel : fourSimplexBoundaryLabel a b c d e j ≠
        fourSimplexBoundaryLabel a b c d e i := by
      exact fun heq => hji ((fourSimplexBoundaryLabel_injective h) heq)
    simp [triangulationTopologicalGeometricVertex, hlabel]

theorem fourSimplexBoundaryPiLinearMap_image_convexHull
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) (S : Set (Fin 5)) :
    fourSimplexBoundaryPiLinearMap a b c d e ''
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (fourSimplexBoundaryLabel a b c d e '' S)) =
      convexHull ℝ (fourSimplexAffineBasis '' S) := by
  classical
  rw [LinearMap.image_convexHull]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, rfl⟩
    exact ⟨i, hi, (fourSimplexBoundaryPiLinearMap_basisVertex h i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨triangulationTopologicalGeometricVertex
      (fourSimplexBoundaryLabel a b c d e i), ?_, ?_⟩
    · exact ⟨fourSimplexBoundaryLabel a b c d e i, ⟨i, hi, rfl⟩, rfl⟩
    · exact fourSimplexBoundaryPiLinearMap_basisVertex h i

theorem continuous_fourSimplexBoundaryPiLinearMap (a b c d e : Nat) :
    Continuous (fourSimplexBoundaryPiLinearMap a b c d e) := by
  unfold fourSimplexBoundaryPiLinearMap
  change Continuous (fun p : Nat → ℝ ↦ ∑ i : Fin 5,
    p (fourSimplexBoundaryLabel a b c d e i) • fourSimplexAffineBasis i)
  apply continuous_finset_sum Finset.univ
  intro i _
  exact (continuous_apply (fourSimplexBoundaryLabel a b c d e i) :
    Continuous (fun p : Nat → ℝ ↦
      p (fourSimplexBoundaryLabel a b c d e i))).smul continuous_const

theorem fourSimplexBoundaryPiLinearMap_image_representedFacet
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    (sigma : Tet) (i : Fin 5)
    (hverts : sigma.verts.toFinset =
      (Finset.univ.erase i).image (fourSimplexBoundaryLabel a b c d e)) :
    fourSimplexBoundaryPiLinearMap a b c d e ''
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑sigma.verts.toFinset : Set Nat)) =
      convexHull ℝ (Set.range (fourSimplex.faceOpposite i).points) := by
  rw [hverts]
  rw [fourSimplexFaceOpposite_vertexSet_eq_image_erase]
  simpa only [fourSimplex_points_eq_affineBasis, Finset.coe_image] using
    fourSimplexBoundaryPiLinearMap_image_convexHull h
      (↑(Finset.univ.erase i) : Set (Fin 5))

/-- Carrier points have total coordinate one on the five certified vertices. -/
theorem triangulationTopologicalGeometricCarrier_sum_label_coordinates
    {K : Triangulation} {a b c d e : Nat}
    (hnodup : [a, b, c, d, e].Nodup)
    (hcover : ∀ sigma ∈ K.tets,
      sigma.verts.toFinset ⊆
        (Finset.univ.image (fourSimplexBoundaryLabel a b c d e)))
    (p : Nat → ℝ)
    (hp : p ∈ (triangulationTopologicalGeometricComplex K).space) :
    ∑ i : Fin 5, p (fourSimplexBoundaryLabel a b c d e i) = 1 := by
  classical
  obtain ⟨F, _hFne, ⟨sigma, hsigma, hFsigma⟩, hpF⟩ :=
    (mem_triangulationTopologicalGeometricCarrier_iff K p).1 hp
  apply convexHull_min _ (convex_hyperplane
    ⟨fun x y ↦ by simp [Finset.sum_add_distrib],
      fun r x ↦ by simp [Finset.mul_sum]⟩ (1 : ℝ)) hpF
  rintro _ ⟨y, hyF, rfl⟩
  have hyimage : y ∈ Finset.univ.image
      (fourSimplexBoundaryLabel a b c d e) :=
    hcover sigma hsigma (hFsigma hyF)
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hyimage
  change ∑ j : Fin 5,
    triangulationTopologicalGeometricVertex
      (fourSimplexBoundaryLabel a b c d e i)
      (fourSimplexBoundaryLabel a b c d e j) = 1
  rw [Fintype.sum_eq_single i]
  · simp [triangulationTopologicalGeometricVertex]
  · intro j hji
    have hne := fun heq => hji ((fourSimplexBoundaryLabel_injective hnodup) heq)
    simp [triangulationTopologicalGeometricVertex, Ne.symm hne]

/-- Carrier points vanish away from the five certified coordinates. -/
theorem triangulationTopologicalGeometricCarrier_coordinate_eq_zero
    {K : Triangulation} {a b c d e : Nat}
    (hcover : ∀ sigma ∈ K.tets,
      sigma.verts.toFinset ⊆
        (Finset.univ.image (fourSimplexBoundaryLabel a b c d e)))
    (p : Nat → ℝ)
    (hp : p ∈ (triangulationTopologicalGeometricComplex K).space)
    (y : Nat) (hy : y ∉ Set.range (fourSimplexBoundaryLabel a b c d e)) :
    p y = 0 := by
  classical
  obtain ⟨F, _hFne, ⟨sigma, hsigma, hFsigma⟩, hpF⟩ :=
    (mem_triangulationTopologicalGeometricCarrier_iff K p).1 hp
  apply convexHull_min _ (convex_hyperplane
    ⟨fun x z ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hpF
  rintro _ ⟨z, hzF, rfl⟩
  have hzimage := hcover sigma hsigma (hFsigma hzF)
  obtain ⟨i, _hi, hzi⟩ := Finset.mem_image.mp hzimage
  have hzy : z ≠ y := by
    intro h
    apply hy
    exact ⟨i, hzi.trans h⟩
  simp [triangulationTopologicalGeometricVertex, hzy]

theorem fourSimplexBoundaryPiLinearMap_injOn_carrier
    {K : Triangulation} {a b c d e : Nat}
    (hnodup : [a, b, c, d, e].Nodup)
    (hcover : ∀ sigma ∈ K.tets,
      sigma.verts.toFinset ⊆
        (Finset.univ.image (fourSimplexBoundaryLabel a b c d e))) :
    Set.InjOn (fourSimplexBoundaryPiLinearMap a b c d e)
      (triangulationTopologicalGeometricComplex K).space := by
  classical
  intro p hp q hq hpq
  have hpsum := triangulationTopologicalGeometricCarrier_sum_label_coordinates
    hnodup hcover p hp
  have hqsum := triangulationTopologicalGeometricCarrier_sum_label_coordinates
    hnodup hcover q hq
  have hcomb :
      Finset.univ.affineCombination ℝ fourSimplexAffineBasis
          (fun i ↦ p (fourSimplexBoundaryLabel a b c d e i)) =
        Finset.univ.affineCombination ℝ fourSimplexAffineBasis
          (fun i ↦ q (fourSimplexBoundaryLabel a b c d e i)) := by
    rw [Finset.affineCombination_eq_linear_combination
        Finset.univ _ _ (by simpa using hpsum),
      Finset.affineCombination_eq_linear_combination
        Finset.univ _ _ (by simpa using hqsum)]
    exact hpq
  have hweights : ∀ i : Fin 5,
      p (fourSimplexBoundaryLabel a b c d e i) =
        q (fourSimplexBoundaryLabel a b c d e i) := by
    intro i
    exact (fourSimplexAffineBasis.ind.affineCombination_eq_iff_eq
      (by simpa using hpsum) (by simpa using hqsum)).1 hcomb i (Finset.mem_univ i)
  funext y
  by_cases hy : y ∈ Set.range (fourSimplexBoundaryLabel a b c d e)
  · obtain ⟨i, rfl⟩ := hy
    exact hweights i
  · rw [triangulationTopologicalGeometricCarrier_coordinate_eq_zero
        hcover p hp y hy,
      triangulationTopologicalGeometricCarrier_coordinate_eq_zero
        hcover q hq y hy]

set_option maxHeartbeats 1000000 in
theorem ClosedTriangulationCore.exists_fourSimplexBoundary_realizationChange
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    (hconn : TetrahedronVertexOverlapConnected K)
    {tau : Tet} (htauK : tau ∈ K.tets) (htau : tau.verts.Nodup) :
    ∃ e, [tau.v0, tau.v1, tau.v2, tau.v3, e].Nodup ∧
      let L := fourSimplexBoundaryPiLinearMap
        tau.v0 tau.v1 tau.v2 tau.v3 e
      L '' (triangulationTopologicalGeometricComplex K).space =
        frontier fourSimplexBody ∧
      Set.InjOn L (triangulationTopologicalGeometricComplex K).space := by
  classical
  obtain ⟨rho012, rho013, rho023, rho123, e,
    h012K, h013K, h023K, h123K, _he, hnodup, _hsupport,
    _hsupportFinset, _htetsFinset, htauFinset, h012Finset,
    h013Finset, h023Finset, h123Finset, hglobal⟩ :=
      hcore.exists_fourSimplexBoundary_combinatorial_certificate
        hPhi hconn htauK htau
  let label := fourSimplexBoundaryLabel tau.v0 tau.v1 tau.v2 tau.v3 e
  let L := fourSimplexBoundaryPiLinearMap tau.v0 tau.v1 tau.v2 tau.v3 e
  have hlabels : Finset.univ.image label =
      {tau.v0, tau.v1, tau.v2, tau.v3, e} := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [label]
    · intro hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [label]⟩
      · exact ⟨1, by simp [label]⟩
      · exact ⟨2, by simp [label]⟩
      · exact ⟨3, by simp [label]⟩
      · exact ⟨4, by simp [label]⟩
  have hcover : ∀ sigma ∈ K.tets,
      sigma.verts.toFinset ⊆ Finset.univ.image label := by
    intro sigma hsigma
    rw [hlabels]
    rcases hglobal sigma hsigma with h | h | h | h | h
    all_goals rw [h]
    all_goals intro y hy
    all_goals simp_all
    all_goals aesop
  have htauFacet : L '' convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑tau.verts.toFinset : Set Nat)) =
      convexHull ℝ (Set.range (fourSimplex.faceOpposite (4 : Fin 5)).points) := by
    apply fourSimplexBoundaryPiLinearMap_image_representedFacet hnodup tau 4
    rw [htauFinset]
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨3, by simp⟩
    · rintro ⟨j, hj, rfl⟩
      fin_cases j <;> simp_all
  have h012Facet : L '' convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑rho012.verts.toFinset : Set Nat)) =
      convexHull ℝ (Set.range (fourSimplex.faceOpposite (3 : Fin 5)).points) := by
    apply fourSimplexBoundaryPiLinearMap_image_representedFacet hnodup rho012 3
    rw [h012Finset]
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨4, by simp⟩
    · rintro ⟨j, hj, rfl⟩
      fin_cases j <;> simp_all
  have h013Facet : L '' convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑rho013.verts.toFinset : Set Nat)) =
      convexHull ℝ (Set.range (fourSimplex.faceOpposite (2 : Fin 5)).points) := by
    apply fourSimplexBoundaryPiLinearMap_image_representedFacet hnodup rho013 2
    rw [h013Finset]
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨3, by simp⟩
      · exact ⟨4, by simp⟩
    · rintro ⟨j, hj, rfl⟩
      fin_cases j <;> simp_all
  have h023Facet : L '' convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑rho023.verts.toFinset : Set Nat)) =
      convexHull ℝ (Set.range (fourSimplex.faceOpposite (1 : Fin 5)).points) := by
    apply fourSimplexBoundaryPiLinearMap_image_representedFacet hnodup rho023 1
    rw [h023Finset]
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨3, by simp⟩
      · exact ⟨4, by simp⟩
    · rintro ⟨j, hj, rfl⟩
      fin_cases j <;> simp_all
  have h123Facet : L '' convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑rho123.verts.toFinset : Set Nat)) =
      convexHull ℝ (Set.range (fourSimplex.faceOpposite (0 : Fin 5)).points) := by
    apply fourSimplexBoundaryPiLinearMap_image_representedFacet hnodup rho123 0
    rw [h123Finset]
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨3, by simp⟩
      · exact ⟨4, by simp⟩
    · rintro ⟨j, hj, rfl⟩
      fin_cases j <;> simp_all
  refine ⟨e, hnodup, ?_, ?_⟩
  · rw [fourSimplexFrontier_eq_facetUnion]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion] at hq
      simp only [Set.mem_iUnion] at hq
      obtain ⟨sigma, hsigma, hqface⟩ := hq
      rcases hglobal sigma hsigma with h | h | h | h | h
      · have hp : L q ∈ L '' convexHull ℝ
            (triangulationTopologicalGeometricVertex ''
              (↑tau.verts.toFinset : Set Nat)) :=
          ⟨q, by rw [htauFinset, ← h]; exact hqface, rfl⟩
        rw [htauFacet] at hp
        exact ⟨4, hp⟩
      · have hp : L q ∈ L '' convexHull ℝ
            (triangulationTopologicalGeometricVertex ''
              (↑rho012.verts.toFinset : Set Nat)) :=
          ⟨q, by rw [h012Finset, ← h]; exact hqface, rfl⟩
        rw [h012Facet] at hp
        exact ⟨3, hp⟩
      · have hp : L q ∈ L '' convexHull ℝ
            (triangulationTopologicalGeometricVertex ''
              (↑rho013.verts.toFinset : Set Nat)) :=
          ⟨q, by rw [h013Finset, ← h]; exact hqface, rfl⟩
        rw [h013Facet] at hp
        exact ⟨2, hp⟩
      · have hp : L q ∈ L '' convexHull ℝ
            (triangulationTopologicalGeometricVertex ''
              (↑rho023.verts.toFinset : Set Nat)) :=
          ⟨q, by rw [h023Finset, ← h]; exact hqface, rfl⟩
        rw [h023Facet] at hp
        exact ⟨1, hp⟩
      · have hp : L q ∈ L '' convexHull ℝ
            (triangulationTopologicalGeometricVertex ''
              (↑rho123.verts.toFinset : Set Nat)) :=
          ⟨q, by rw [h123Finset, ← h]; exact hqface, rfl⟩
        rw [h123Facet] at hp
        exact ⟨0, hp⟩
    · rintro ⟨i, hp⟩
      fin_cases i
      · change p ∈ convexHull ℝ
          (Set.range (fourSimplex.faceOpposite (0 : Fin 5)).points) at hp
        rw [← h123Facet] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        refine ⟨q, ?_, rfl⟩
        rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
        simp only [Set.mem_iUnion]
        exact ⟨rho123, h123K, hq⟩
      · change p ∈ convexHull ℝ
          (Set.range (fourSimplex.faceOpposite (1 : Fin 5)).points) at hp
        rw [← h023Facet] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        refine ⟨q, ?_, rfl⟩
        rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
        simp only [Set.mem_iUnion]
        exact ⟨rho023, h023K, hq⟩
      · change p ∈ convexHull ℝ
          (Set.range (fourSimplex.faceOpposite (2 : Fin 5)).points) at hp
        rw [← h013Facet] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        refine ⟨q, ?_, rfl⟩
        rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
        simp only [Set.mem_iUnion]
        exact ⟨rho013, h013K, hq⟩
      · change p ∈ convexHull ℝ
          (Set.range (fourSimplex.faceOpposite (3 : Fin 5)).points) at hp
        rw [← h012Facet] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        refine ⟨q, ?_, rfl⟩
        rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
        simp only [Set.mem_iUnion]
        exact ⟨rho012, h012K, hq⟩
      · change p ∈ convexHull ℝ
          (Set.range (fourSimplex.faceOpposite (4 : Fin 5)).points) at hp
        rw [← htauFacet] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        refine ⟨q, ?_, rfl⟩
        rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
        simp only [Set.mem_iUnion]
        exact ⟨tau, htauK, hq⟩
  · exact fourSimplexBoundaryPiLinearMap_injOn_carrier hnodup hcover

/-- The actual topology-bearing Pi-space carrier of a normalized triangulation
is homeomorphic to the frontier of the standard affine four-simplex. -/
theorem ClosedTriangulationCore.nonempty_homeomorph_fourSimplexFrontier
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    (hconn : TetrahedronVertexOverlapConnected K)
    {tau : Tet} (htauK : tau ∈ K.tets) (htau : tau.verts.Nodup) :
    Nonempty
      (triangulationTopologicalGeometricCarrier K ≃ₜ
        ↥(frontier fourSimplexBody)) := by
  classical
  obtain ⟨e, _hnodup, himage, hinj⟩ :=
    hcore.exists_fourSimplexBoundary_realizationChange
      hPhi hconn htauK htau
  let L := fourSimplexBoundaryPiLinearMap tau.v0 tau.v1 tau.v2 tau.v3 e
  let f : triangulationTopologicalGeometricCarrier K →
      ↥(frontier fourSimplexBody) := fun p ↦
    ⟨L p.1, himage ▸ Set.mem_image_of_mem L p.2⟩
  have hfcont : Continuous f :=
    Continuous.subtype_mk
      ((continuous_fourSimplexBoundaryPiLinearMap
        tau.v0 tau.v1 tau.v2 tau.v3 e).comp continuous_subtype_val) _
  have hfinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact hinj p.2 q.2 (Subtype.ext_iff.mp hpq)
  have hfsurj : Function.Surjective f := by
    intro q
    have hq : q.1 ∈ L '' (triangulationTopologicalGeometricComplex K).space := by
      rw [himage]
      exact q.2
    obtain ⟨p, hp, hpq⟩ := hq
    refine ⟨⟨p, hp⟩, Subtype.ext ?_⟩
    exact hpq
  exact ⟨IsHomeomorph.homeomorph f
    ((isHomeomorph_iff_continuous_bijective).2
      ⟨hfcont, hfinj, hfsurj⟩)⟩

end Poincare
