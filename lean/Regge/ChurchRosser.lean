import Regge.Reduction
import Regge.ChurchRosserAxioms

universe u

theorem church_rosser_reduction
  {V : Type u} (Faces : Set (List V))
  (L L1 L2 : List V) :
  ReductionPath Faces L L1 →
  ReductionPath Faces L L2 →
  ∃ L', ReductionPath Faces L1 L' ∧ ReductionPath Faces L2 L' :=
  church_rosser_axiom Faces L L1 L2
