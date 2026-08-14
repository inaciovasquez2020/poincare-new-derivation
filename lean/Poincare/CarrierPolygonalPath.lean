import Poincare.Move23ActualRegions
import Poincare.TriangulationTopologicalSimplyConnected
import Poincare.TriangulationTopologicalEdgeLocalModel
import Mathlib.Analysis.Convex.PathConnected

open Set
open scoped unitInterval

namespace Poincare

/-- A represented vertex belongs to the filled body of its tetrahedron. -/
theorem triangulationTopologicalGeometricVertex_mem_tetBody
    {v : Nat} {tau : Tet} (hv : v ∈ tau.verts) :
    triangulationTopologicalGeometricVertex v ∈
      triangulationTopologicalTetBody tau := by
  apply subset_convexHull ℝ
  exact ⟨v, List.mem_toFinset.mpr hv, rfl⟩

/-- The midpoint of two represented vertices belongs to every tetrahedron
containing both endpoints. -/
theorem triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody
    {v w : Nat} {tau : Tet} (hv : v ∈ tau.verts) (hw : w ∈ tau.verts) :
    triangulationTopologicalGeometricEdgeMidpoint v w ∈
      triangulationTopologicalTetBody tau := by
  rw [triangulationTopologicalGeometricEdgeMidpoint]
  have hv' := triangulationTopologicalGeometricVertex_mem_tetBody hv
  have hw' := triangulationTopologicalGeometricVertex_mem_tetBody hw
  convert (convex_convexHull ℝ _).lineMap_mem hv' hw'
    (show (2 : ℝ)⁻¹ ∈ Set.Icc (0 : ℝ) 1 by norm_num) using 1 <;>
    ext j <;>
    simp [AffineMap.lineMap_apply,
      triangulationTopologicalGeometricEdgeMidpoint_apply,
      triangulationTopologicalGeometricVertex] <;>
    ring

/-- A tetrahedron occurring in `K` has its whole geometric body in the carrier. -/
theorem triangulationTopologicalTetBody_subset_carrier
    (K : Triangulation) {tau : Tet} (htau : tau ∈ K.tets) :
    triangulationTopologicalTetBody tau ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  intro x hx
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  exact Set.mem_iUnion_of_mem tau (Set.mem_iUnion_of_mem htau hx)

/-- The straight affine segment between two carrier points lying in one
represented tetrahedron, bundled as a path in the carrier. -/
noncomputable def carrierSegmentInTet
    (K : Triangulation) (tau : Tet) (htau : tau ∈ K.tets)
    (p q : triangulationTopologicalGeometricCarrier K)
    (hp : p.1 ∈ triangulationTopologicalTetBody tau)
    (hq : q.1 ∈ triangulationTopologicalTetBody tau) : Path p q where
  toFun t :=
    ⟨Path.segment p.1 q.1 t,
      triangulationTopologicalTetBody_subset_carrier K htau
        ((convex_convexHull ℝ _).lineMap_mem hp hq t.2)⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

@[simp] theorem carrierSegmentInTet_coe
    (K : Triangulation) (tau : Tet) (htau : tau ∈ K.tets)
    (p q : triangulationTopologicalGeometricCarrier K)
    (hp : p.1 ∈ triangulationTopologicalTetBody tau)
    (hq : q.1 ∈ triangulationTopologicalTetBody tau)
    (t : unitInterval) :
    (carrierSegmentInTet K tau htau p q hp hq t).1 =
      AffineMap.lineMap p.1 q.1 (t : ℝ) := rfl

/-- Every point of the canonical carrier segment remains in its supporting
represented tetrahedron. -/
theorem carrierSegmentInTet_mem
    (K : Triangulation) (tau : Tet) (htau : tau ∈ K.tets)
    (p q : triangulationTopologicalGeometricCarrier K)
    (hp : p.1 ∈ triangulationTopologicalTetBody tau)
    (hq : q.1 ∈ triangulationTopologicalTetBody tau)
    (t : unitInterval) :
    (carrierSegmentInTet K tau htau p q hp hq t).1 ∈
      triangulationTopologicalTetBody tau := by
  exact (convex_convexHull ℝ _).lineMap_mem hp hq t.2

/-- Two carrier points supported in a common represented tetrahedron are
joined by a path whose full range stays in that tetrahedron. -/
theorem exists_carrierPath_range_subset_tetBody
    (K : Triangulation) (tau : Tet) (htau : tau ∈ K.tets)
    (p q : triangulationTopologicalGeometricCarrier K)
    (hp : p.1 ∈ triangulationTopologicalTetBody tau)
    (hq : q.1 ∈ triangulationTopologicalTetBody tau) :
    ∃ gamma : Path p q,
      Set.range gamma ⊆ Subtype.val ⁻¹' triangulationTopologicalTetBody tau := by
  refine ⟨carrierSegmentInTet K tau htau p q hp hq, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact carrierSegmentInTet_mem K tau htau p q hp hq t

/-- Concatenating two supported carrier paths preserves the union of their
support sets.  This is the elementary finite-concatenation step used by
polygonal traces. -/
theorem carrierPath_trans_range_subset
    {K : Triangulation} {p q r : triangulationTopologicalGeometricCarrier K}
    (alpha : Path p q) (beta : Path q r)
    {A B : Set (triangulationTopologicalGeometricCarrier K)}
    (ha : Set.range alpha ⊆ A) (hb : Set.range beta ⊆ B) :
    Set.range (alpha.trans beta) ⊆ A ∪ B := by
  rw [Path.trans_range]
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (ha hx)
  · exact Or.inr (hb hx)

/-- A finite, endpoint-indexed trace in which every step is certified to lie
in one represented tetrahedron.  Endpoint indices make concatenation usable
without transports or endpoint casts. -/
inductive CarrierSimplexTrace (K : Triangulation) :
    triangulationTopologicalGeometricCarrier K →
      triangulationTopologicalGeometricCarrier K → Type
  | refl (p) : CarrierSimplexTrace K p p
  | step {p q r} (tau : Tet) (htau : tau ∈ K.tets)
      (hp : p.1 ∈ triangulationTopologicalTetBody tau)
      (hq : q.1 ∈ triangulationTopologicalTetBody tau)
      (tail : CarrierSimplexTrace K q r) : CarrierSimplexTrace K p r

/-- Realize a finite certified simplex trace as a carrier polygonal path. -/
noncomputable def CarrierSimplexTrace.toPath
    {K : Triangulation} {p q : triangulationTopologicalGeometricCarrier K} :
    CarrierSimplexTrace K p q → Path p q
  | .refl _ => Path.refl _
  | .step tau htau hp hq tail =>
      (carrierSegmentInTet K tau htau _ _ hp hq).trans tail.toPath

/-- The finite dependent recursion theorem requested by geometric traces:
every finite list of certified common-tetrahedron steps has an exact path
between its indexed endpoints. -/
theorem exists_carrierPolygonalPath_of_simplexTrace
    {K : Triangulation} {p q : triangulationTopologicalGeometricCarrier K}
    (trace : CarrierSimplexTrace K p q) : Nonempty (Path p q) := by
  exact ⟨trace.toPath⟩

@[simp] theorem CarrierSimplexTrace.toPath_refl
    {K : Triangulation} (p : triangulationTopologicalGeometricCarrier K) :
    (CarrierSimplexTrace.refl p).toPath = Path.refl p := rfl

theorem CarrierSimplexTrace.toPath_step_range
    {K : Triangulation}
    {p q r : triangulationTopologicalGeometricCarrier K}
    (tau : Tet) (htau : tau ∈ K.tets)
    (hp : p.1 ∈ triangulationTopologicalTetBody tau)
    (hq : q.1 ∈ triangulationTopologicalTetBody tau)
    (tail : CarrierSimplexTrace K q r) :
    Set.range (CarrierSimplexTrace.step tau htau hp hq tail).toPath =
      Set.range (carrierSegmentInTet K tau htau p q hp hq) ∪
        Set.range tail.toPath := by
  exact Path.trans_range _ _

end Poincare
