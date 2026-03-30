import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic

universe u

inductive LoopReduction {V : Type u} (Faces : Set (List V)) :
  List V → List V → Prop
| face_reduction (u v w : V) (L1 L2 : List V) :
    [u, v, w] ∈ Faces →
    LoopReduction Faces (L1 ++ [u, v, w] ++ L2) (L1 ++ [u, w] ++ L2)

abbrev ReductionPath {V : Type u} (Faces : Set (List V)) :=
  Relation.ReflTransGen (LoopReduction Faces)

theorem reduction_refl {V : Type u} (F : Set (List V)) (L : List V) :
  ReductionPath F L L :=
  Relation.ReflTransGen.refl

theorem reduction_single {V : Type u} (F : Set (List V)) (L₁ L₂ : List V)
    (h : LoopReduction F L₁ L₂) :
    ReductionPath F L₁ L₂ :=
  Relation.ReflTransGen.single h
