
import Mathlib
import Poincare.Validity
import Poincare.TriangulationTopologicalGeometricCarrier
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

namespace Poincare.PR199G2

open Set

/-- The actual uniform barycenter of a finite
nonempty vertex set in the canonical Pi-space. -/
noncomputable def finiteBarycenter
    (A : Finset Nat) : Nat → ℝ :=
  ∑ i : A,
    (A.card : ℝ)⁻¹ •
      triangulationTopologicalGeometricVertex i

/-- The uniform finite weights sum to one. -/
theorem finiteBarycenter_weights_sum_one
    (A : Finset Nat) (hA : A.Nonempty) :
    (∑ _i : A, (A.card : ℝ)⁻¹) = 1 := by
  have hc : A.card ≠ 0 :=
    Finset.card_ne_zero.mpr hA
  simp [Fintype.card_coe, hc, nsmul_eq_mul]

/-- Every nonempty finite vertex-set barycenter
lies in the convex hull of its vertices. -/
theorem finiteBarycenter_mem_convexHull
    (A : Finset Nat) (hA : A.Nonempty) :
    finiteBarycenter A ∈
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑A : Set Nat)) := by
  classical
  apply mem_convexHull_of_exists_fintype
    (w := fun _i : A => (A.card : ℝ)⁻¹)
    (z := fun i : A =>
      triangulationTopologicalGeometricVertex i)
  · intro i
    positivity
  · exact finiteBarycenter_weights_sum_one A hA
  · intro i
    exact ⟨i.1, i.2, rfl⟩
  · rfl

/-- The barycenter of any nonempty face of a
represented tetrahedron is inside that tetrahedron. -/
theorem finiteBarycenter_mem_tetHull
    (τ : Tet)
    (A : Finset Nat)
    (hA : A.Nonempty)
    (hsub : A ⊆ τ.verts.toFinset) :
    finiteBarycenter A ∈
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑τ.verts.toFinset : Set Nat)) := by
  have hvertices :
      (↑A : Set Nat) ⊆
        (↑τ.verts.toFinset : Set Nat) :=
    Finset.coe_subset.mpr hsub
  have himages :
      triangulationTopologicalGeometricVertex ''
        (↑A : Set Nat) ⊆
      triangulationTopologicalGeometricVertex ''
        (↑τ.verts.toFinset : Set Nat) :=
    Set.image_mono hvertices
  exact (convexHull_mono himages)
    (finiteBarycenter_mem_convexHull A hA)

#print axioms finiteBarycenter_weights_sum_one
#print axioms finiteBarycenter_mem_convexHull
#print axioms finiteBarycenter_mem_tetHull

def flagTriangle
    (be bf bt : Nat → ℝ) : Set (Nat → ℝ) :=
  convexHull ℝ ({be, bf, bt} : Set (Nat → ℝ))

/--
An actual geometric flag triangle lies in the
carrier whenever its three barycenters lie
inside the corresponding represented tetrahedron.
-/
theorem flagTriangle_subset_geometricCarrier
    (K : Triangulation)
    (τ : Tet)
    (hτ : τ ∈ K.tets)
    (be bf bt : Nat → ℝ)
    (he :
      be ∈ convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑τ.verts.toFinset : Set Nat)))
    (hf :
      bf ∈ convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑τ.verts.toFinset : Set Nat)))
    (ht :
      bt ∈ convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑τ.verts.toFinset : Set Nat))) :
    flagTriangle be bf bt ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  let C : Set (Nat → ℝ) :=
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑τ.verts.toFinset : Set Nat))
  have hpoints :
      ({be, bf, bt} : Set (Nat → ℝ)) ⊆ C := by
    intro p hp
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact he
    · exact hf
    · exact ht
  have hflag : flagTriangle be bf bt ⊆ C := by
    exact convexHull_min hpoints (convex_convexHull ℝ _)
  intro p hp
  apply
    (mem_triangulationTopologicalGeometricCarrier_iff
      K p).2
  refine ⟨τ.verts.toFinset, ?_,
    ⟨τ, hτ, Finset.Subset.rfl⟩, hflag hp⟩
  exact ⟨τ.v0, by simp [Tet.verts]⟩




/--
Each genuine barycentric flag triangle of a represented
tetrahedron lies inside the actual geometric carrier.
No barycenter containment hypotheses are assumed.
-/
theorem actualFlagTriangle_subset_geometricCarrier
    (K : Triangulation)
    (τ : Tet)
    (hτ : τ ∈ K.tets)
    (e f : Finset Nat)
    (he : e.Nonempty)
    (hf : f.Nonempty)
    (hef : e ⊆ f)
    (hft : f ⊆ τ.verts.toFinset) :
    flagTriangle
        (finiteBarycenter e)
        (finiteBarycenter f)
        (finiteBarycenter τ.verts.toFinset)
      ⊆
        (triangulationTopologicalGeometricComplex K).space := by
  have het : e ⊆ τ.verts.toFinset :=
    hef.trans hft

  have ht : τ.verts.toFinset.Nonempty := by
    exact ⟨τ.v0, by simp [Tet.verts]⟩

  exact flagTriangle_subset_geometricCarrier
    K τ hτ
    (finiteBarycenter e)
    (finiteBarycenter f)
    (finiteBarycenter τ.verts.toFinset)
    (finiteBarycenter_mem_tetHull τ e he het)
    (finiteBarycenter_mem_tetHull τ f hf hft)
    (finiteBarycenter_mem_tetHull
      τ τ.verts.toFinset ht Finset.Subset.rfl)

#print axioms actualFlagTriangle_subset_geometricCarrier

#print axioms flagTriangle_subset_geometricCarrier

/--
A genuine incidence flag consisting of a represented
tetrahedron and a triangular face containing the fixed edge.
-/
structure BarycentricDualFlag
    (K : Triangulation)
    (e : Finset Nat) where
  face : Finset Nat
  tet : Tet
  edge_card : e.card = 2
  face_card : face.card = 3
  tet_mem : tet ∈ K.tets
  edge_sub_face : e ⊆ face
  face_sub_tet : face ⊆ tet.verts.toFinset

/-- The actual geometric flag triangle. -/
noncomputable def barycentricDualFlagTriangle
    {K : Triangulation}
    {e : Finset Nat}
    (a : BarycentricDualFlag K e) :
    Set (Nat → ℝ) :=
  flagTriangle
    (finiteBarycenter e)
    (finiteBarycenter a.face)
    (finiteBarycenter a.tet.verts.toFinset)

/--
The assembled barycentric edge-dual cell:
the union of all genuine incidence flag triangles.
-/
noncomputable def barycentricEdgeDualCell
    (K : Triangulation)
    (e : Finset Nat) :
    Set (Nat → ℝ) :=
  ⋃ a : BarycentricDualFlag K e,
    barycentricDualFlagTriangle a

/--
Every genuine flag triangle is contained
in the actual geometric realization.
-/
theorem barycentricDualFlagTriangle_subset_carrier
    {K : Triangulation}
    {e : Finset Nat}
    (a : BarycentricDualFlag K e) :
    barycentricDualFlagTriangle a ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  have he : e.Nonempty := by
    apply Finset.card_pos.mp
    rw [a.edge_card]
    omega
  have hf : a.face.Nonempty := by
    apply Finset.card_pos.mp
    rw [a.face_card]
    omega
  exact actualFlagTriangle_subset_geometricCarrier
    K a.tet a.tet_mem
    e a.face
    he hf
    a.edge_sub_face
    a.face_sub_tet

/--
The entire assembled barycentric edge-dual cell
lies in the actual topological carrier.
-/
theorem barycentricEdgeDualCell_subset_carrier
    (K : Triangulation)
    (e : Finset Nat) :
    barycentricEdgeDualCell K e ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  intro p hp
  change
    p ∈
      (⋃ a : BarycentricDualFlag K e,
        barycentricDualFlagTriangle a) at hp
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
  exact
    barycentricDualFlagTriangle_subset_carrier a ha

#print axioms barycentricDualFlagTriangle_subset_carrier
#print axioms barycentricEdgeDualCell_subset_carrier


/--
Exact coordinates of the canonical finite barycenter.
No geometric membership assumption is required.
-/
theorem finiteBarycenter_apply
    (A : Finset Nat) (i : Nat) :
    finiteBarycenter A i =
      if i ∈ A then (A.card : ℝ)⁻¹ else 0 := by
  classical
  simp only [finiteBarycenter,
    triangulationTopologicalGeometricVertex,
    Finset.sum_apply,
    Pi.smul_apply,
    Pi.single_apply,
    smul_eq_mul, mul_one, mul_zero]
  by_cases hi : i ∈ A
  · let j : {x : Nat // x ∈ A} := ⟨i, hi⟩
    have hsum :
        (∑ x ∈ A.attach,
          if i = (x : Nat)
          then (A.card : ℝ)⁻¹ else 0) =
          (if i = (j : Nat)
           then (A.card : ℝ)⁻¹ else 0) := by
      apply Finset.sum_eq_single j
      · intro x hx hne
        have hix : i ≠ (x : Nat) := by
          intro he
          apply hne
          exact Subtype.ext he.symm
        simp [hix]
      · intro hnot
        exact False.elim
          (hnot (Finset.mem_attach A j))
    simpa [hi, j] using hsum
  · have hix (x : {n : Nat // n ∈ A}) :
        i ≠ (x : Nat) := by
      intro he
      apply hi
      simpa [← he] using x.property
    simp [hi, hix]

#print axioms finiteBarycenter_apply


/--
The two barycentric directions belonging to a strict
three-stage flag are linearly independent.

The witnesses p and q identify new vertices at successive
stages. No affine-independence assumption is introduced.
-/
theorem barycentric_flag_direction_independent
    (e f t : Finset Nat)
    (p q : Nat)
    (hef : e ⊆ f)
    (hft : f ⊆ t)
    (hp : p ∈ f)
    (hpe : p ∉ e)
    (hq : q ∈ t)
    (hqf : q ∉ f)
    (hf : f.Nonempty)
    (ht : t.Nonempty)
    (a b : ℝ)
    (hlin :
      a • (finiteBarycenter f - finiteBarycenter e) +
      b • (finiteBarycenter t - finiteBarycenter e) =
        (0 : Nat → ℝ)) :
    a = 0 ∧ b = 0 := by
  have hqe : q ∉ e := by
    intro h
    exact hqf (hef h)
  have hpt : p ∈ t := hft hp
  have htcard : (t.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ht)
  have hfcard : (f.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hf)

  have hqcoord :=
    congrArg (fun z : Nat → ℝ => z q) hlin

  have hbinv :
      b * (t.card : ℝ)⁻¹ = 0 := by
    simpa [finiteBarycenter_apply,
      hq, hqf, hqe,
      Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
      using hqcoord

  have hb : b = 0 :=
    (mul_eq_zero.mp hbinv).resolve_right
      (inv_ne_zero htcard)

  have hpcoord :=
    congrArg (fun z : Nat → ℝ => z p) hlin

  have hainv :
      a * (f.card : ℝ)⁻¹ = 0 := by
    simpa [finiteBarycenter_apply,
      hp, hpe, hpt, hb,
      Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
      using hpcoord

  have ha : a = 0 :=
    (mul_eq_zero.mp hainv).resolve_right
      (inv_ne_zero hfcard)

  exact ⟨ha, hb⟩

#print axioms barycentric_flag_direction_independent


/--
Affine coordinates for the actual barycentric flag triangle.
The parameters range over R²; the triangle itself corresponds
to nonnegative parameters with a + b <= 1.
-/
noncomputable def barycentricFlagChart
    (e f t : Finset Nat)
    (a b : ℝ) : Nat → ℝ :=
  finiteBarycenter e +
    a • (finiteBarycenter f - finiteBarycenter e) +
    b • (finiteBarycenter t - finiteBarycenter e)

/--
A strict barycentric flag has unique affine coefficients.

This excludes self-overlap within the parameterization of
one flag triangle. It makes no claim about intersections
of different flag triangles.
-/
theorem barycentricFlagChart_coeff_unique
    (e f t : Finset Nat)
    (p q : Nat)
    (hef : e ⊆ f)
    (hft : f ⊆ t)
    (hp : p ∈ f)
    (hpe : p ∉ e)
    (hq : q ∈ t)
    (hqf : q ∉ f)
    (hf : f.Nonempty)
    (ht : t.Nonempty)
    (a₁ b₁ a₂ b₂ : ℝ)
    (h :
      barycentricFlagChart e f t a₁ b₁ =
      barycentricFlagChart e f t a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  dsimp [barycentricFlagChart] at h
  have hlin :
      (a₁ - a₂) •
          (finiteBarycenter f - finiteBarycenter e) +
        (b₁ - b₂) •
          (finiteBarycenter t - finiteBarycenter e) =
        (0 : Nat → ℝ) := by
    rw [sub_smul, sub_smul]
    calc
      a₁ • (finiteBarycenter f - finiteBarycenter e) -
          a₂ • (finiteBarycenter f - finiteBarycenter e) +
        (b₁ • (finiteBarycenter t - finiteBarycenter e) -
          b₂ • (finiteBarycenter t - finiteBarycenter e)) =
          (finiteBarycenter e +
              a₁ • (finiteBarycenter f - finiteBarycenter e) +
              b₁ • (finiteBarycenter t - finiteBarycenter e)) -
            (finiteBarycenter e +
              a₂ • (finiteBarycenter f - finiteBarycenter e) +
              b₂ • (finiteBarycenter t - finiteBarycenter e)) := by
              abel
      _ = 0 := sub_eq_zero.mpr h

  obtain ⟨ha, hb⟩ :=
    barycentric_flag_direction_independent
      e f t p q hef hft hp hpe hq hqf hf ht
      (a₁ - a₂) (b₁ - b₂) hlin

  exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb⟩

#print axioms barycentricFlagChart_coeff_unique


/--
Exact intersection coefficients for two distinct triangular
faces containing the same edge inside the same tetrahedron.

The face-direction coefficients must be nonnegative.
The theorem proves equality of chart parameters on their
shared edge-to-tetrahedron barycentric segment.
-/
theorem barycentricFlagChart_distinctFaces_intersection
    (e f g t : Finset Nat)
    (p q : Nat)
    (hef : e ⊆ f)
    (heg : e ⊆ g)
    (hft : f ⊆ t)
    (hgt : g ⊆ t)
    (hp : p ∈ f)
    (hpg : p ∉ g)
    (hq : q ∈ g)
    (hqf : q ∉ f)
    (hfcard : f.card = 3)
    (hgcard : g.card = 3)
    (htcard : t.card = 4)
    (a b c d : ℝ)
    (ha0 : 0 ≤ a)
    (hc0 : 0 ≤ c)
    (heq :
      barycentricFlagChart e f t a b =
      barycentricFlagChart e g t c d) :
    a = 0 ∧ c = 0 ∧ b = d := by
  have hpe : p ∉ e := by
    intro h
    exact hpg (heg h)
  have hqe : q ∉ e := by
    intro h
    exact hqf (hef h)
  have hpt : p ∈ t := hft hp
  have hqt : q ∈ t := hgt hq

  have hpc :=
    congrArg (fun z : Nat → ℝ => z p) heq
  have hqc :=
    congrArg (fun z : Nat → ℝ => z q) heq

  have hpEq :
      a / 3 + b / 4 = d / 4 := by
    simp [barycentricFlagChart,
      finiteBarycenter_apply,
      hpe, hp, hpg, hpt,
      hfcard, hgcard, htcard,
      Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hpc
    norm_num at hpc
    linarith

  have hqEq :
      b / 4 = c / 3 + d / 4 := by
    simp [barycentricFlagChart,
      finiteBarycenter_apply,
      hqe, hq, hqf, hqt,
      hfcard, hgcard, htcard,
      Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hqc
    norm_num at hqc
    linarith

  have hac : a + c = 0 := by
    linarith [hpEq, hqEq]
  have ha : a = 0 := by
    linarith
  have hc : c = 0 := by
    linarith
  have hbd : b = d := by
    rw [ha] at hpEq
    linarith

  exact ⟨ha, hc, hbd⟩

#print axioms barycentricFlagChart_distinctFaces_intersection


/--
Two genuine barycentric flag charts sharing the same edge
and triangular face, but with distinct tetrahedron supports,
have equal images only when both tetrahedron-direction
coefficients vanish.

The witnesses r and s distinguish the tetrahedra.
-/
theorem barycentricFlagChart_distinctTets_sameFace_intersection
    (e f t u : Finset Nat)
    (p r s : Nat)
    (hef : e ⊆ f)
    (hft : f ⊆ t)
    (hfu : f ⊆ u)
    (hp : p ∈ f)
    (hpe : p ∉ e)
    (hr : r ∈ t)
    (hru : r ∉ u)
    (hs : s ∈ u)
    (hst : s ∉ t)
    (hfcard : f.card = 3)
    (htcard : t.card = 4)
    (hucard : u.card = 4)
    (a b c d : ℝ)
    (heq :
      barycentricFlagChart e f t a b =
      barycentricFlagChart e f u c d) :
    b = 0 ∧ d = 0 ∧ a = c := by

  have hre : r ∉ e := by
    intro h
    exact hru (hfu (hef h))
  have hrf : r ∉ f := by
    intro h
    exact hru (hfu h)
  have hse : s ∉ e := by
    intro h
    exact hst (hft (hef h))
  have hsf : s ∉ f := by
    intro h
    exact hst (hft h)

  have hrcoord :=
    congrArg (fun z : Nat → ℝ => z r) heq

  have hb : b = 0 := by
    simp [barycentricFlagChart,
      finiteBarycenter_apply,
      hre, hrf, hr, hru,
      htcard, hucard,
      Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hrcoord
    norm_num at hrcoord
    linarith

  have hscoord :=
    congrArg (fun z : Nat → ℝ => z s) heq

  have hd : d = 0 := by
    simp [barycentricFlagChart,
      finiteBarycenter_apply,
      hse, hsf, hs, hst,
      htcard, hucard,
      Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hscoord
    norm_num at hscoord
    linarith

  have hpt : p ∈ t := hft hp
  have hpu : p ∈ u := hfu hp

  have hpcoord :=
    congrArg (fun z : Nat → ℝ => z p) heq

  have hac : a = c := by
    simp [barycentricFlagChart,
      finiteBarycenter_apply,
      hp, hpe, hpt, hpu,
      hfcard, htcard, hucard,
      hb, hd,
      Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hpcoord
    norm_num at hpcoord
    linarith

  exact ⟨hb, hd, hac⟩

#print axioms barycentricFlagChart_distinctTets_sameFace_intersection


/--
Different triangular faces in different tetrahedra.

The two flags share e, but f and g have private vertices,
and t and u each have a vertex outside the other.

Under nonnegative face and tetrahedron coefficients,
the only common chart point is the barycenter of e.
-/
theorem barycentricFlagChart_distinctFaces_distinctTets_intersection
    (e f g t u : Finset Nat)
    (p q r s : Nat)
    (hef : e ⊆ f)
    (heg : e ⊆ g)
    (hft : f ⊆ t)
    (hgu : g ⊆ u)
    (hp : p ∈ f)
    (hpg : p ∉ g)
    (hq : q ∈ g)
    (hqf : q ∉ f)
    (hr : r ∈ t)
    (hru : r ∉ u)
    (hs : s ∈ u)
    (hst : s ∉ t)
    (hfcard : f.card = 3)
    (hgcard : g.card = 3)
    (htcard : t.card = 4)
    (hucard : u.card = 4)
    (a b c d : ℝ)
    (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b)
    (hc0 : 0 ≤ c)
    (hd0 : 0 ≤ d)
    (heq :
      barycentricFlagChart e f t a b =
      barycentricFlagChart e g u c d) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by

  have hre : r ∉ e := by
    intro h
    exact hru (hgu (heg h))
  have hrg : r ∉ g := by
    intro h
    exact hru (hgu h)
  have hse : s ∉ e := by
    intro h
    exact hst (hft (hef h))
  have hsf : s ∉ f := by
    intro h
    exact hst (hft h)

  have hrcoord :=
    congrArg (fun z : Nat → ℝ => z r) heq

  have hb : b = 0 := by
    by_cases hrf : r ∈ f
    · simp [barycentricFlagChart,
        finiteBarycenter_apply,
        hre, hrg, hr, hru, hrf,
        hfcard, hgcard, htcard, hucard,
        Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul] at hrcoord
      norm_num at hrcoord
      linarith
    · simp [barycentricFlagChart,
        finiteBarycenter_apply,
        hre, hrg, hr, hru, hrf,
        hfcard, hgcard, htcard, hucard,
        Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul] at hrcoord
      norm_num at hrcoord
      linarith

  have hscoord :=
    congrArg (fun z : Nat → ℝ => z s) heq

  have hd : d = 0 := by
    by_cases hsg : s ∈ g
    · simp [barycentricFlagChart,
        finiteBarycenter_apply,
        hse, hsf, hs, hst, hsg,
        hfcard, hgcard, htcard, hucard,
        Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul] at hscoord
      norm_num at hscoord
      linarith
    · simp [barycentricFlagChart,
        finiteBarycenter_apply,
        hse, hsf, hs, hst, hsg,
        hfcard, hgcard, htcard, hucard,
        Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul] at hscoord
      norm_num at hscoord
      linarith

  have hpe : p ∉ e := by
    intro h
    exact hpg (heg h)
  have hqe : q ∉ e := by
    intro h
    exact hqf (hef h)

  have hpcoord :=
    congrArg (fun z : Nat → ℝ => z p) heq

  have ha : a = 0 := by
    simp [barycentricFlagChart,
      finiteBarycenter_apply,
      hpe, hp, hpg, hb, hd,
      hfcard, hgcard,
      Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hpcoord
    norm_num at hpcoord
    linarith

  have hqcoord :=
    congrArg (fun z : Nat → ℝ => z q) heq

  have hc : c = 0 := by
    simp [barycentricFlagChart,
      finiteBarycenter_apply,
      hqe, hq, hqf, hb, hd,
      hfcard, hgcard,
      Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hqcoord
    norm_num at hqcoord
    linarith

  exact ⟨ha, hb, hc, hd⟩

#print axioms barycentricFlagChart_distinctFaces_distinctTets_intersection


/--
Different finite supports of equal cardinality have
a private vertex in each direction.
-/
theorem equalCard_distinct_privateVertices
    (A B : Finset Nat)
    (hcard : A.card = B.card)
    (hne : A ≠ B) :
    (∃ p, p ∈ A ∧ p ∉ B) ∧
    (∃ q, q ∈ B ∧ q ∉ A) := by
  classical
  have hAB : ¬ A ⊆ B := by
    intro hab
    apply hne
    exact Finset.eq_of_subset_of_card_le hab
      (by omega)
  have hBA : ¬ B ⊆ A := by
    intro hba
    apply hne
    exact (Finset.eq_of_subset_of_card_le hba
      (by omega)).symm
  exact ⟨Finset.not_subset.mp hAB,
    Finset.not_subset.mp hBA⟩

/--
Private vertices for the two independently differing
levels of barycentric flags.
-/
theorem distinctFlagSupports_have_witnesses
    (f g t u : Finset Nat)
    (hfcard : f.card = 3)
    (hgcard : g.card = 3)
    (htcard : t.card = 4)
    (hucard : u.card = 4)
    (hfg : f ≠ g)
    (htu : t ≠ u) :
    ∃ p q r s : Nat,
      p ∈ f ∧ p ∉ g ∧
      q ∈ g ∧ q ∉ f ∧
      r ∈ t ∧ r ∉ u ∧
      s ∈ u ∧ s ∉ t := by
  obtain ⟨⟨p, hpf, hpg⟩,
      ⟨q, hqg, hqf⟩⟩ :=
    equalCard_distinct_privateVertices
      f g (by omega) hfg
  obtain ⟨⟨r, hrt, hru⟩,
      ⟨s, hsu, hst⟩⟩ :=
    equalCard_distinct_privateVertices
      t u (by omega) htu
  exact ⟨p, q, r, s,
    hpf, hpg, hqg, hqf, hrt, hru, hsu, hst⟩

#print axioms equalCard_distinct_privateVertices
#print axioms distinctFlagSupports_have_witnesses


/--
Exhaustive intersection classification for two barycentric
flag charts with a common edge.

Every distinct-support witness is derived from the finite
set cardinalities; no private vertices are assumed.
-/
theorem barycentricFlagChart_allSupportCases
    (e f g t u : Finset Nat)
    (hecard : e.card = 2)
    (hfcard : f.card = 3)
    (hgcard : g.card = 3)
    (htcard : t.card = 4)
    (hucard : u.card = 4)
    (hef : e ⊆ f)
    (heg : e ⊆ g)
    (hft : f ⊆ t)
    (hgu : g ⊆ u)
    (a b c d : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hd : 0 ≤ d)
    (heq :
      barycentricFlagChart e f t a b =
      barycentricFlagChart e g u c d) :
    (f = g → t = u → a = c ∧ b = d) ∧
    (f ≠ g → t = u → a = 0 ∧ c = 0 ∧ b = d) ∧
    (f = g → t ≠ u → b = 0 ∧ d = 0 ∧ a = c) ∧
    (f ≠ g → t ≠ u →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hfg htu
    subst g
    subst u
    have hnotfe : ¬ f ⊆ e := by
      intro hsub
      have hle := Finset.card_le_card hsub
      omega
    obtain ⟨p, hp, hpe⟩ :=
      Finset.not_subset.mp hnotfe
    have hnottf : ¬ t ⊆ f := by
      intro hsub
      have hle := Finset.card_le_card hsub
      omega
    obtain ⟨q, hq, hqf⟩ :=
      Finset.not_subset.mp hnottf
    have hfn : f.Nonempty :=
      Finset.card_pos.mp (by omega)
    have htn : t.Nonempty :=
      Finset.card_pos.mp (by omega)
    exact barycentricFlagChart_coeff_unique
      e f t p q hef hft hp hpe hq hqf
      hfn htn a b c d heq
  · intro hfg htu
    subst u
    obtain ⟨⟨p, hp, hpg⟩, ⟨q, hq, hqf⟩⟩ :=
      equalCard_distinct_privateVertices
        f g (by omega) hfg
    exact barycentricFlagChart_distinctFaces_intersection
      e f g t p q hef heg hft hgu
      hp hpg hq hqf hfcard hgcard htcard
      a b c d ha hc heq
  · intro hfg htu
    subst g
    have hnotfe : ¬ f ⊆ e := by
      intro hsub
      have hle := Finset.card_le_card hsub
      omega
    obtain ⟨p, hp, hpe⟩ :=
      Finset.not_subset.mp hnotfe
    obtain ⟨⟨r, hr, hru⟩, ⟨s, hs, hst⟩⟩ :=
      equalCard_distinct_privateVertices
        t u (by omega) htu
    exact barycentricFlagChart_distinctTets_sameFace_intersection
      e f t u p r s hef hft hgu
      hp hpe hr hru hs hst
      hfcard htcard hucard
      a b c d heq
  · intro hfg htu
    obtain ⟨p, q, r, s,
      hp, hpg, hq, hqf, hr, hru, hs, hst⟩ :=
      distinctFlagSupports_have_witnesses
        f g t u hfcard hgcard htcard hucard
        hfg htu
    exact barycentricFlagChart_distinctFaces_distinctTets_intersection
      e f g t u p q r s
      hef heg hft hgu
      hp hpg hq hqf hr hru hs hst
      hfcard hgcard htcard hucard
      a b c d ha hb hc hd heq

#print axioms barycentricFlagChart_allSupportCases


/--
Instantiate the complete support classification for
two actual incidence-certified barycentric dual flags.

The tetrahedron-cardinality assumptions are explicit
until established from the concrete Tet representation.
-/
theorem actualDualFlags_allSupportCases
    (K : Triangulation)
    (e : Finset Nat)
    (A B : BarycentricDualFlag K e)
    (hAt : A.tet.verts.toFinset.card = 4)
    (hBt : B.tet.verts.toFinset.card = 4)
    (a b c d : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hd : 0 ≤ d)
    (heq :
      barycentricFlagChart
        e A.face A.tet.verts.toFinset a b =
      barycentricFlagChart
        e B.face B.tet.verts.toFinset c d) :
    (A.face = B.face →
      A.tet.verts.toFinset = B.tet.verts.toFinset →
      a = c ∧ b = d) ∧
    (A.face ≠ B.face →
      A.tet.verts.toFinset = B.tet.verts.toFinset →
      a = 0 ∧ c = 0 ∧ b = d) ∧
    (A.face = B.face →
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset →
      b = 0 ∧ d = 0 ∧ a = c) ∧
    (A.face ≠ B.face →
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  exact barycentricFlagChart_allSupportCases
    e A.face B.face
    A.tet.verts.toFinset B.tet.verts.toFinset
    A.edge_card A.face_card B.face_card
    hAt hBt
    A.edge_sub_face B.edge_sub_face
    A.face_sub_tet B.face_sub_tet
    a b c d ha hb hc hd heq

#print axioms actualDualFlags_allSupportCases


/-- A tetrahedron record may have only three distinct vertices. -/
theorem degenerateTet_threeVertices :
    (⟨0, 0, 1, 2⟩ : Tet).verts.toFinset.card = 3 := by
  decide

/--
Even an actual incidence-certified barycentric dual flag
does not imply that its tetrahedron has four distinct vertices.
-/
theorem actualDualFlag_can_have_degenerateTet :
    ∃ (K : Triangulation) (e : Finset Nat)
      (A : BarycentricDualFlag K e),
      A.tet.verts.toFinset.card ≠ 4 := by
  let τ : Tet := ⟨0, 0, 1, 2⟩
  let K : Triangulation := ⟨[τ]⟩
  let e : Finset Nat := {0, 1}
  let f : Finset Nat := {0, 1, 2}
  have he : e.card = 2 := by decide
  have hf : f.card = 3 := by decide
  have hτ : τ ∈ K.tets := by simp [K]
  have hef : e ⊆ f := by decide
  have hft : f ⊆ τ.verts.toFinset := by decide
  let A : BarycentricDualFlag K e :=
    ⟨f, τ, he, hf, hτ, hef, hft⟩
  refine ⟨K, e, A, ?_⟩
  have hcard : τ.verts.toFinset.card = 3 := by decide
  change τ.verts.toFinset.card ≠ 4
  omega

#print axioms degenerateTet_threeVertices
#print axioms actualDualFlag_can_have_degenerateTet


/--
A duplicate-free concrete Tet has exactly four
distinct vertices in its finite-set support.
-/
theorem tet_card_four_of_nodup
    (τ : Tet) (h : τ.verts.Nodup) :
    τ.verts.toFinset.card = 4 := by
  simpa [Tet.verts] using
    (List.toFinset_card_of_nodup h)

/--
Apply the complete four-case chart classification to
two actual flags, assuming only that their concrete
tetrahedron vertex lists have no duplicates.
-/
theorem actualDualFlags_allSupportCases_of_nodup
    (K : Triangulation)
    (e : Finset Nat)
    (A B : BarycentricDualFlag K e)
    (hA : A.tet.verts.Nodup)
    (hB : B.tet.verts.Nodup)
    (a b c d : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hd : 0 ≤ d)
    (heq :
      barycentricFlagChart
        e A.face A.tet.verts.toFinset a b =
      barycentricFlagChart
        e B.face B.tet.verts.toFinset c d) :
    (A.face = B.face →
      A.tet.verts.toFinset = B.tet.verts.toFinset →
      a = c ∧ b = d) ∧
    (A.face ≠ B.face →
      A.tet.verts.toFinset = B.tet.verts.toFinset →
      a = 0 ∧ c = 0 ∧ b = d) ∧
    (A.face = B.face →
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset →
      b = 0 ∧ d = 0 ∧ a = c) ∧
    (A.face ≠ B.face →
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  exact actualDualFlags_allSupportCases
    K e A B
    (tet_card_four_of_nodup A.tet hA)
    (tet_card_four_of_nodup B.tet hB)
    a b c d ha hb hc hd heq

#print axioms tet_card_four_of_nodup
#print axioms actualDualFlags_allSupportCases_of_nodup


/--
The exact closed-core validity predicate discharges
tetrahedron nondegeneracy for every represented dual flag.
-/
theorem closedCore_dualFlag_nodup
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {e : Finset Nat}
    (A : BarycentricDualFlag K e) :
    A.tet.verts.Nodup := by
  exact hcore.1 A.tet A.tet_mem

/--
Every actual barycentric dual flag in a closed core
has exactly four distinct tetrahedron vertices.
-/
theorem closedCore_dualFlag_tet_card_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {e : Finset Nat}
    (A : BarycentricDualFlag K e) :
    A.tet.verts.toFinset.card = 4 := by
  exact tet_card_four_of_nodup A.tet
    (closedCore_dualFlag_nodup hcore A)

/--
Complete four-case intersection classification for
actual barycentric dual flags in a closed triangulation.

No separate tetrahedron cardinality or Nodup
hypotheses are required.
-/
theorem closedCore_actualDualFlags_allSupportCases
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (e : Finset Nat)
    (A B : BarycentricDualFlag K e)
    (a b c d : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hd : 0 ≤ d)
    (heq :
      barycentricFlagChart
        e A.face A.tet.verts.toFinset a b =
      barycentricFlagChart
        e B.face B.tet.verts.toFinset c d) :
    (A.face = B.face →
      A.tet.verts.toFinset = B.tet.verts.toFinset →
      a = c ∧ b = d) ∧
    (A.face ≠ B.face →
      A.tet.verts.toFinset = B.tet.verts.toFinset →
      a = 0 ∧ c = 0 ∧ b = d) ∧
    (A.face = B.face →
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset →
      b = 0 ∧ d = 0 ∧ a = c) ∧
    (A.face ≠ B.face →
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  exact actualDualFlags_allSupportCases_of_nodup
    K e A B
    (closedCore_dualFlag_nodup hcore A)
    (closedCore_dualFlag_nodup hcore B)
    a b c d ha hb hc hd heq

#print axioms closedCore_dualFlag_nodup
#print axioms closedCore_dualFlag_tet_card_four
#print axioms closedCore_actualDualFlags_allSupportCases

theorem convexHull_three_exists_simplexChart
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u v w p : E)
    (hp : p ∈ convexHull ℝ ({u, v, w} : Set E)) :
    ∃ a b : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 ∧
      p = (1 - a - b) • u + a • v + b • w := by
  rw [← convexJoin_singleton_segment u v w] at hp
  rcases mem_convexJoin.mp hp with
    ⟨x, hx, y, hy, hxy⟩
  have hxu : x = u := by
    simpa only [Set.mem_singleton_iff] using hx
  subst x
  rw [segment_eq_image ℝ v w] at hy
  rcases hy with ⟨r, hr, rfl⟩
  rw [segment_eq_image ℝ u
    ((1 - r) • v + r • w)] at hxy
  rcases hxy with ⟨s, hs, hsp⟩
  refine ⟨s * (1 - r), s * r, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg hs.1 (sub_nonneg.mpr hr.2)
  · exact mul_nonneg hs.1 hr.1
  · nlinarith [hs.2]
  · calc
      p = (1 - s) • u +
          s • ((1 - r) • v + r • w) := hsp.symm
      _ = (1 - s * (1 - r) - s * r) • u +
          (s * (1 - r)) • v + (s * r) • w := by
        have h :
            (1 - s : ℝ) =
              1 - s * (1 - r) - s * r := by
          ring
        rw [← h]
        simp only [smul_add, smul_smul]
        abel

#print axioms convexHull_three_exists_simplexChart


theorem simplexCombination_mem_convexHull
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u v w : E) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    (1 - a - b) • u + a • v + b • w ∈
      convexHull ℝ ({u, v, w} : Set E) := by
  let weights : Fin 3 → ℝ := ![1 - a - b, a, b]
  let vertices : Fin 3 → E := ![u, v, w]
  refine mem_convexHull_of_exists_fintype
    weights vertices ?_ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [weights] <;> linarith
  · simp [weights, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> simp [vertices]
  · simp [weights, vertices, Fin.sum_univ_succ]
    abel

#print axioms simplexCombination_mem_convexHull



/--
Exact two-parameter representation of the convex hull
of three points in an arbitrary real module.

Both directions are constructed from previously
kernel-verified convex-combination certificates.
-/
theorem convexHull_three_iff_simplexCombination
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u v w p : E) :
    p ∈ convexHull ℝ ({u, v, w} : Set E) ↔
      ∃ a b : ℝ,
        0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 ∧
        p = (1 - a - b) • u + a • v + b • w := by
  constructor
  · intro hp
    exact convexHull_three_exists_simplexChart
      u v w p hp
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact simplexCombination_mem_convexHull
      u v w a b ha hb hab

#print axioms convexHull_three_iff_simplexCombination



/-- Exact algebraic identification of the actual
    barycentric flag chart with its convex weights. -/
theorem actualChart_eq_threeCombination
    (e f t : Finset Nat) (a b : ℝ) :
    barycentricFlagChart e f t a b =
      (1 - a - b) • finiteBarycenter e +
      a • finiteBarycenter f +
      b • finiteBarycenter t := by
  simp only [barycentricFlagChart,
    smul_sub, sub_smul, one_smul]
  abel

/-- Exact membership in the hull of three actual
    barycenters, with no nondegeneracy assumptions. -/
theorem actualChart_hull_membership_iff
    (e f t : Finset Nat) (p : Nat → ℝ) :
    p ∈ convexHull ℝ
        ({finiteBarycenter e,
          finiteBarycenter f,
          finiteBarycenter t} : Set (Nat → ℝ)) ↔
      ∃ a b : ℝ,
        0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 ∧
        p = barycentricFlagChart e f t a b := by
  constructor
  · intro hp
    rcases convexHull_three_exists_simplexChart
      (finiteBarycenter e)
      (finiteBarycenter f)
      (finiteBarycenter t) p hp with
      ⟨a, b, ha, hb, hab, hrepresentation⟩
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rw [actualChart_eq_threeCombination]
    exact hrepresentation
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    rw [actualChart_eq_threeCombination]
    exact simplexCombination_mem_convexHull
      (finiteBarycenter e)
      (finiteBarycenter f)
      (finiteBarycenter t)
      a b ha hb hab

#print axioms actualChart_eq_threeCombination
#print axioms actualChart_hull_membership_iff


/--
Two geometric barycentric dual-flag triangles sharing
the primal edge, but having distinct face and tetrahedron
supports, intersect exactly at the edge barycenter.
-/
theorem closedCore_distinctFlags_triangle_intersection_singleton
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (e : Finset Nat)
    (A B : BarycentricDualFlag K e)
    (hface : A.face ≠ B.face)
    (htet :
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset) :
    barycentricDualFlagTriangle A ∩
      barycentricDualFlagTriangle B =
        ({finiteBarycenter e} : Set (Nat → ℝ)) := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpA, hpB⟩
    have hA :
        p ∈ convexHull ℝ
          ({finiteBarycenter e,
            finiteBarycenter A.face,
            finiteBarycenter A.tet.verts.toFinset} :
              Set (Nat → ℝ)) := by
      simpa only [barycentricDualFlagTriangle,
        flagTriangle] using hpA
    have hB :
        p ∈ convexHull ℝ
          ({finiteBarycenter e,
            finiteBarycenter B.face,
            finiteBarycenter B.tet.verts.toFinset} :
              Set (Nat → ℝ)) := by
      simpa only [barycentricDualFlagTriangle,
        flagTriangle] using hpB
    rcases (actualChart_hull_membership_iff
      e A.face A.tet.verts.toFinset p).mp hA with
      ⟨a, b, ha, hb, hab, hpa⟩
    rcases (actualChart_hull_membership_iff
      e B.face B.tet.verts.toFinset p).mp hB with
      ⟨c, d, hc, hd, hcd, hpb⟩
    have heq :
        barycentricFlagChart
          e A.face A.tet.verts.toFinset a b =
        barycentricFlagChart
          e B.face B.tet.verts.toFinset c d :=
      hpa.symm.trans hpb
    have hcases :=
      closedCore_actualDualFlags_allSupportCases
        hcore e A B a b c d ha hb hc hd heq
    obtain ⟨ha0, hb0, hc0, hd0⟩ :=
      hcases.2.2.2 hface htet
    have hpoint : p = finiteBarycenter e := by
      simpa [barycentricFlagChart, ha0, hb0]
        using hpa
    exact Set.mem_singleton_iff.mpr hpoint
  · intro hp
    have hpoint : p = finiteBarycenter e :=
      Set.mem_singleton_iff.mp hp
    subst p
    constructor
    · have hmem :
          finiteBarycenter e ∈ convexHull ℝ
            ({finiteBarycenter e,
              finiteBarycenter A.face,
              finiteBarycenter A.tet.verts.toFinset} :
                Set (Nat → ℝ)) := by
        apply (actualChart_hull_membership_iff
          e A.face A.tet.verts.toFinset
          (finiteBarycenter e)).mpr
        refine ⟨0, 0, by norm_num, by norm_num,
          by norm_num, ?_⟩
        simp [barycentricFlagChart]
      simpa only [barycentricDualFlagTriangle,
        flagTriangle] using hmem
    · have hmem :
          finiteBarycenter e ∈ convexHull ℝ
            ({finiteBarycenter e,
              finiteBarycenter B.face,
              finiteBarycenter B.tet.verts.toFinset} :
                Set (Nat → ℝ)) := by
        apply (actualChart_hull_membership_iff
          e B.face B.tet.verts.toFinset
          (finiteBarycenter e)).mpr
        refine ⟨0, 0, by norm_num, by norm_num,
          by norm_num, ?_⟩
        simp [barycentricFlagChart]
      simpa only [barycentricDualFlagTriangle,
        flagTriangle] using hmem

#print axioms closedCore_distinctFlags_triangle_intersection_singleton



-- ============================================================
-- Exact geometric intersection classification of dual flags
-- ============================================================

/--
Membership in an actual dual-flag triangle is equivalent
to membership through the verified two-parameter chart.
-/
theorem dualFlagTriangle_mem_iff_chart
    {K : Triangulation}
    {e : Finset Nat}
    (A : BarycentricDualFlag K e)
    (p : Nat → ℝ) :
    p ∈ barycentricDualFlagTriangle A ↔
      ∃ a b : ℝ,
        0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 ∧
        p = barycentricFlagChart
          e A.face A.tet.verts.toFinset a b := by
  simpa only [barycentricDualFlagTriangle,
    flagTriangle] using
    (actualChart_hull_membership_iff
      e A.face A.tet.verts.toFinset p)

/--
The face-direction chart with the tetrahedron
coefficient zero is an ordinary segment point.
-/
theorem barycentricFlagChart_zero_tetCoefficient
    (e f t : Finset Nat) (a : ℝ) :
    barycentricFlagChart e f t a 0 =
      (1 - a) • finiteBarycenter e +
      a • finiteBarycenter f := by
  simp only [barycentricFlagChart,
    zero_smul, add_zero,
    smul_sub, sub_smul, one_smul]
  all_goals abel

/--
The tetrahedron-direction chart with face coefficient
zero is an ordinary segment point.
-/
theorem barycentricFlagChart_zero_faceCoefficient
    (e f t : Finset Nat) (b : ℝ) :
    barycentricFlagChart e f t 0 b =
      (1 - b) • finiteBarycenter e +
      b • finiteBarycenter t := by
  simp only [barycentricFlagChart,
    zero_smul, zero_add,
    smul_sub, sub_smul, one_smul]
  all_goals abel

/--
Every edge-to-face barycenter segment belongs to
its corresponding actual flag triangle.
-/
theorem edgeFaceSegment_subset_dualFlagTriangle
    {K : Triangulation}
    {e : Finset Nat}
    (A : BarycentricDualFlag K e) :
    segment ℝ (finiteBarycenter e)
      (finiteBarycenter A.face) ⊆
        barycentricDualFlagTriangle A := by
  intro p hp
  rw [segment_eq_image ℝ
    (finiteBarycenter e)
    (finiteBarycenter A.face)] at hp
  rcases hp with ⟨a, ha, rfl⟩
  apply (dualFlagTriangle_mem_iff_chart A _).mpr
  refine ⟨a, 0, ha.1, by norm_num, ?_, ?_⟩
  · simpa using ha.2
  · exact
      (barycentricFlagChart_zero_tetCoefficient
        e A.face A.tet.verts.toFinset a).symm

/--
Every edge-to-tetrahedron barycenter segment belongs
to its corresponding actual flag triangle.
-/
theorem edgeTetSegment_subset_dualFlagTriangle
    {K : Triangulation}
    {e : Finset Nat}
    (A : BarycentricDualFlag K e) :
    segment ℝ (finiteBarycenter e)
      (finiteBarycenter A.tet.verts.toFinset) ⊆
        barycentricDualFlagTriangle A := by
  intro p hp
  rw [segment_eq_image ℝ
    (finiteBarycenter e)
    (finiteBarycenter A.tet.verts.toFinset)] at hp
  rcases hp with ⟨b, hb, rfl⟩
  apply (dualFlagTriangle_mem_iff_chart A _).mpr
  refine ⟨0, b, by norm_num, hb.1, ?_, ?_⟩
  · simpa using hb.2
  · exact
      (barycentricFlagChart_zero_faceCoefficient
        e A.face A.tet.verts.toFinset b).symm

/--
Case 2:
Equal face supports, distinct tetrahedron supports.

The exact intersection is the closed segment joining
the common edge barycenter to the common face barycenter.
-/
theorem closedCore_sameFace_distinctTets_intersection_segment
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (e : Finset Nat)
    (A B : BarycentricDualFlag K e)
    (hface : A.face = B.face)
    (htet :
      A.tet.verts.toFinset ≠
        B.tet.verts.toFinset) :
    barycentricDualFlagTriangle A ∩
      barycentricDualFlagTriangle B =
        segment ℝ (finiteBarycenter e)
          (finiteBarycenter A.face) := by
  apply Set.Subset.antisymm
  · intro p hp
    rcases hp with ⟨hpA, hpB⟩
    rcases (dualFlagTriangle_mem_iff_chart A p).mp hpA with
      ⟨a, b, ha, hb, hab, hpa⟩
    rcases (dualFlagTriangle_mem_iff_chart B p).mp hpB with
      ⟨c, d, hc, hd, hcd, hpb⟩
    have heq :
        barycentricFlagChart
          e A.face A.tet.verts.toFinset a b =
        barycentricFlagChart
          e B.face B.tet.verts.toFinset c d :=
      hpa.symm.trans hpb
    have hcases :=
      closedCore_actualDualFlags_allSupportCases
        hcore e A B a b c d ha hb hc hd heq
    obtain ⟨hb0, hd0, hac⟩ :=
      hcases.2.2.1 hface htet
    have hpsegment :
        p = (1 - a) • finiteBarycenter e +
          a • finiteBarycenter A.face := by
      simpa only [
        hb0,
        barycentricFlagChart_zero_tetCoefficient
      ] using hpa
    rw [segment_eq_image ℝ
      (finiteBarycenter e)
      (finiteBarycenter A.face)]
    refine ⟨a, ⟨ha, ?_⟩, hpsegment.symm⟩
    linarith
  · intro p hp
    constructor
    · exact edgeFaceSegment_subset_dualFlagTriangle
        A hp
    · have hpB :
          p ∈ segment ℝ (finiteBarycenter e)
            (finiteBarycenter B.face) := by
        simpa only [hface] using hp
      exact edgeFaceSegment_subset_dualFlagTriangle
        B hpB

/--
Case 3:
Distinct face supports, equal tetrahedron supports.

The exact intersection is the closed segment joining
the common edge barycenter to the tetrahedron barycenter.
-/
theorem closedCore_distinctFaces_sameTet_intersection_segment
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (e : Finset Nat)
    (A B : BarycentricDualFlag K e)
    (hface : A.face ≠ B.face)
    (htet :
      A.tet.verts.toFinset =
        B.tet.verts.toFinset) :
    barycentricDualFlagTriangle A ∩
      barycentricDualFlagTriangle B =
        segment ℝ (finiteBarycenter e)
          (finiteBarycenter A.tet.verts.toFinset) := by
  apply Set.Subset.antisymm
  · intro p hp
    rcases hp with ⟨hpA, hpB⟩
    rcases (dualFlagTriangle_mem_iff_chart A p).mp hpA with
      ⟨a, b, ha, hb, hab, hpa⟩
    rcases (dualFlagTriangle_mem_iff_chart B p).mp hpB with
      ⟨c, d, hc, hd, hcd, hpb⟩
    have heq :
        barycentricFlagChart
          e A.face A.tet.verts.toFinset a b =
        barycentricFlagChart
          e B.face B.tet.verts.toFinset c d :=
      hpa.symm.trans hpb
    have hcases :=
      closedCore_actualDualFlags_allSupportCases
        hcore e A B a b c d ha hb hc hd heq
    obtain ⟨ha0, hc0, hbd⟩ :=
      hcases.2.1 hface htet
    have hpsegment :
        p = (1 - b) • finiteBarycenter e +
          b • finiteBarycenter A.tet.verts.toFinset := by
      simpa only [
        ha0,
        barycentricFlagChart_zero_faceCoefficient
      ] using hpa
    rw [segment_eq_image ℝ
      (finiteBarycenter e)
      (finiteBarycenter A.tet.verts.toFinset)]
    refine ⟨b, ⟨hb, ?_⟩, hpsegment.symm⟩
    linarith
  · intro p hp
    constructor
    · exact edgeTetSegment_subset_dualFlagTriangle
        A hp
    · have hpB :
          p ∈ segment ℝ (finiteBarycenter e)
            (finiteBarycenter B.tet.verts.toFinset) := by
        simpa only [htet] using hp
      exact edgeTetSegment_subset_dualFlagTriangle
        B hpB

/--
Case 4:
Equal face supports and equal tetrahedron supports.

The two geometric triangle sets coincide; their
intersection is therefore the entire triangle.
-/
theorem sameSupports_dualFlagTriangle_intersection
    {K : Triangulation}
    (e : Finset Nat)
    (A B : BarycentricDualFlag K e)
    (hface : A.face = B.face)
    (htet :
      A.tet.verts.toFinset =
        B.tet.verts.toFinset) :
    barycentricDualFlagTriangle A ∩
      barycentricDualFlagTriangle B =
        barycentricDualFlagTriangle A := by
  have hEq :
      barycentricDualFlagTriangle A =
        barycentricDualFlagTriangle B := by
    simp [barycentricDualFlagTriangle,
      flagTriangle, hface, htet]
  rw [← hEq]
  exact Set.inter_self _

#print axioms dualFlagTriangle_mem_iff_chart
#print axioms barycentricFlagChart_zero_tetCoefficient
#print axioms barycentricFlagChart_zero_faceCoefficient
#print axioms edgeFaceSegment_subset_dualFlagTriangle
#print axioms edgeTetSegment_subset_dualFlagTriangle
#print axioms closedCore_distinctFlags_triangle_intersection_singleton
#print axioms closedCore_sameFace_distinctTets_intersection_segment
#print axioms closedCore_distinctFaces_sameTet_intersection_segment
#print axioms sameSupports_dualFlagTriangle_intersection

end Poincare.PR199G2
