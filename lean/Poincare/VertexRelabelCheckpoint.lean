import Mathlib.Data.List.Count
import Mathlib.Logic.Equiv.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Poincare.TriangulationTopologicalSimplyConnected

/-!
# Vertex relabeling verification checkpoint

This module collects the exact theorem statements and proof bodies checked
in isolated Lean 4.30.0-rc1 runs against Mathlib 05c4d64, using JIID
revision 2afb688b737de237fbf84fac4d88221c58338093.

IMPORTANT: the combined module and this branch have NOT been compiled.
No full geometric-carrier homeomorphism is claimed here. This draft must
remain unpromoted pending an exact-head compilation and permitted-axiom audit.
-/

namespace Poincare

def Tet.relabel (e : Nat ≃ Nat) (t : Tet) : Tet :=
  ⟨e t.v0, e t.v1, e t.v2, e t.v3⟩

def Triangulation.relabel
    (e : Nat ≃ Nat) (K : Triangulation) :
    Triangulation :=
  ⟨K.tets.map (Tet.relabel e)⟩

theorem Tet.verts_relabel
    (e : Nat ≃ Nat) (t : Tet) :
    (t.relabel e).verts = t.verts.map e := by
  cases t
  rfl

theorem allVerts_relabel
    (e : Nat ≃ Nat) (K : Triangulation) :
    allVerts (K.relabel e) =
      (allVerts K).map e := by
  cases K with
  | mk ts =>
    change (ts.map (Tet.relabel e)).flatMap Tet.verts =
      (ts.flatMap Tet.verts).map e
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.map_cons, List.flatMap_cons,
        List.map_append, Tet.verts_relabel, ih]

theorem vertexDegree_relabel
    (e : Nat ≃ Nat) (K : Triangulation)
    (v : Nat) :
    vertexDegree (K.relabel e) (e v) =
      vertexDegree K v := by
  rw [vertexDegree, vertexDegree, allVerts_relabel]
  exact List.count_map_of_injective
    (allVerts K) e e.injective v

theorem vertexDefect_relabel
    (e : Nat ≃ Nat) (K : Triangulation)
    (v : Nat) :
    vertexDefect (K.relabel e) (e v) =
      vertexDefect K v := by
  simp only [vertexDefect, vertexDegree_relabel]

theorem mem_vertexSupport_relabel_iff
    (e : Nat ≃ Nat) (K : Triangulation)
    (v : Nat) :
    e v ∈ vertexSupport (K.relabel e) ↔
      v ∈ vertexSupport K := by
  rw [mem_vertexSupport_iff, mem_vertexSupport_iff,
    allVerts_relabel]
  simp only [List.mem_map]
  constructor
  · rintro ⟨w, hw, heq⟩
    have : w = v := e.injective heq
    simpa [this] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem eraseDups_map_relabel
    (e : Nat ≃ Nat) (l : List Nat) :
    (l.map e).eraseDups =
      l.eraseDups.map e := by
  cases l with
  | nil =>
      rfl
  | cons a xs =>
      simp only [List.map_cons, List.eraseDups_cons]
      have hp :
          (fun z : Nat => !(e z == e a)) =
          (fun z : Nat => !(z == a)) := by
        funext z
        simp [e.injective.eq_iff]
      have hf :
          ((xs.map e).filter
            (fun z => !(z == e a))) =
          (xs.filter (fun z => !(z == a))).map e := by
        rw [List.filter_map]
        simp only [Function.comp_def]
        rw [hp]
      rw [hf]
      congr 1
      exact eraseDups_map_relabel e
        (xs.filter (fun z => !(z == a)))
termination_by l.length
decreasing_by
  simp_wf
  exact Nat.lt_succ_of_le
    (List.length_filter_le _ _)

theorem vertexSupport_relabel
    (e : Nat ≃ Nat) (K : Triangulation) :
    vertexSupport (K.relabel e) =
      (vertexSupport K).map e := by
  simp only [vertexSupport, allVerts_relabel,
    eraseDups_map_relabel]

theorem PhiSupport_relabel
    (e : Nat ≃ Nat) (K : Triangulation) :
    PhiSupport (K.relabel e) = PhiSupport K := by
  have hfold :
      ∀ (xs : List Nat) (a : Nat),
        (xs.map e).foldl
          (fun acc v =>
            acc + vertexDefect (K.relabel e) v) a =
        xs.foldl
          (fun acc v => acc + vertexDefect K v) a := by
    intro xs
    induction xs with
    | nil =>
        intro a
        rfl
    | cons v vs ih =>
        intro a
        simp only [List.map_cons, List.foldl_cons,
          vertexDefect_relabel]
        exact ih _
  unfold PhiSupport
  rw [vertexSupport_relabel]
  exact hfold (vertexSupport K) 0

noncomputable def coordinateRelabel
    (e : Nat ≃ Nat) :
    (Nat → ℝ) ≃ₜ (Nat → ℝ) :=
  Homeomorph.piCongrLeft
    (Y := fun _ : Nat => ℝ) e

theorem coordinateRelabel_apply
    (e : Nat ≃ Nat) (x : Nat → ℝ) (i : Nat) :
    coordinateRelabel e x (e i) = x i := by
  exact Homeomorph.piCongrLeft_apply_apply
    (Y := fun _ : Nat => ℝ) e x i

theorem coordinateRelabel_apply_symm
    (e : Nat ≃ Nat)
    (x : Nat → ℝ) (j : Nat) :
    coordinateRelabel e x j = x (e.symm j) := by
  simpa using
    coordinateRelabel_apply e x (e.symm j)

theorem coordinateRelabel_linear
    (e : Nat ≃ Nat) :
    IsLinearMap ℝ (coordinateRelabel e) := by
  constructor
  · intro x y
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp only [Pi.add_apply, coordinateRelabel_apply]
  · intro c x
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp only [Pi.smul_apply, smul_eq_mul,
      coordinateRelabel_apply]

theorem coordinateRelabel_vertex
    (e : Nat ≃ Nat) (v : Nat) :
    coordinateRelabel e
      (triangulationTopologicalGeometricVertex v) =
    triangulationTopologicalGeometricVertex (e v) := by
  ext j
  obtain ⟨i, rfl⟩ := e.surjective j
  rw [coordinateRelabel_apply]
  simp [triangulationTopologicalGeometricVertex,
    Pi.single_apply, e.injective.eq_iff]

theorem coordinateRelabel_convexHull
    (e : Nat ≃ Nat) (s : Set (Nat → ℝ)) :
    coordinateRelabel e '' convexHull ℝ s =
      convexHull ℝ (coordinateRelabel e '' s) := by
  exact (coordinateRelabel_linear e).image_convexHull s

theorem coordinateRelabel_faceVertex_image
    (e : Nat ≃ Nat) (F : Finset Nat) :
    coordinateRelabel e ''
      (triangulationTopologicalGeometricVertex ''
        (↑F : Set Nat)) =
      triangulationTopologicalGeometricVertex ''
        (↑(F.image e) : Set Nat) := by
  simp only [Finset.coe_image, Set.image_image]
  congr 1
  funext i
  exact coordinateRelabel_vertex e i

theorem coordinateRelabel_faceHull
    (e : Nat ≃ Nat) (F : Finset Nat) :
    coordinateRelabel e ''
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑F : Set Nat)) =
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑(F.image e) : Set Nat)) := by
  rw [coordinateRelabel_convexHull,
    coordinateRelabel_faceVertex_image]

#print axioms Tet.verts_relabel
#print axioms allVerts_relabel
#print axioms vertexDegree_relabel
#print axioms vertexDefect_relabel
#print axioms mem_vertexSupport_relabel_iff
#print axioms vertexSupport_relabel
#print axioms PhiSupport_relabel
#print axioms coordinateRelabel_apply
#print axioms coordinateRelabel_apply_symm
#print axioms coordinateRelabel_linear
#print axioms coordinateRelabel_vertex
#print axioms coordinateRelabel_convexHull
#print axioms coordinateRelabel_faceVertex_image
#print axioms coordinateRelabel_faceHull

end Poincare
