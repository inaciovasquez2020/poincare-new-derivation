import Regge.Reduction

axiom church_rosser_axiom
  {V : Type u} (Faces : Set (List V))
  (L L1 L2 : List V) :
  ReductionPath Faces L L1 →
  ReductionPath Faces L L2 →
  ∃ L', ReductionPath Faces L1 L' ∧ ReductionPath Faces L2 L'
