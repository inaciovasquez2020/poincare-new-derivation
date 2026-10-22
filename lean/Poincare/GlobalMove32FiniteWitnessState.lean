import Poincare.GlobalMove32WitnessedSourceFaceReentry
import Mathlib.Tactic

namespace Poincare

/-- A vertex code whose value belongs to the finite support of K. -/
abbrev FiniteMove32Vertex (K : Triangulation) :=
  ↥((vertexSupport K).toFinset)

/-- The five site coordinates, all drawn from the represented vertex support. -/
structure Move32SiteCode (K : Triangulation) where
  a : FiniteMove32Vertex K
  b : FiniteMove32Vertex K
  c : FiniteMove32Vertex K
  d : FiniteMove32Vertex K
  e : FiniteMove32Vertex K
  deriving Fintype

/-- Decode finite coordinates into the existing, unmodified site definition. -/
def Move32SiteCode.decode {K : Triangulation} (q : Move32SiteCode K) :
    Move32Site :=
  ⟨q.a.1, q.b.1, q.c.1, q.d.1, q.e.1⟩

/-- Finite codes restricted to sites explicitly realized in K. -/
def FiniteRealizedMove32Site (K : Triangulation) :=
  {q : Move32SiteCode K // q.decode.RealizedIn K}

noncomputable instance finiteRealizedMove32SiteFintype (K : Triangulation) :
    Fintype (FiniteRealizedMove32Site K) := by
  classical
  unfold FiniteRealizedMove32Site
  infer_instance

/-- A tetrahedron together with its representation in the finite triangulation. -/
abbrev FiniteMove32Tet (K : Triangulation) := {tau : Tet // tau ∈ K.tets}

/-- Complete finite carrier for a witnessed transition. The five geometric
witness values are retained as data rather than hidden in an existential. -/
structure Move32WitnessState (K : Triangulation) where
  source : FiniteRealizedMove32Site K
  target : FiniteRealizedMove32Site K
  tau : FiniteMove32Tet K
  rho : FiniteMove32Tet K
  x : FiniteMove32Vertex K
  y : FiniteMove32Vertex K
  sigma : FiniteMove32Tet K
  deriving Fintype

/-- The existing witnessed relation, with its source-realization condition
made explicit. This is a specification, not yet the finite-data
correspondence theorem. -/
def RealizedSourceWitnessedReentry
    (K : Triangulation) (s s' : Move32Site) : Prop :=
  s.RealizedIn K ∧ Move32SourceFaceWitnessedReentry K s s'

theorem realizedSourceWitnessedReentry_implies_reentry
    {K : Triangulation} {s s' : Move32Site}
    (h : RealizedSourceWitnessedReentry K s s') :
    Move32SourceFaceReentry K s s' :=
  Move32SourceFaceWitnessedReentry.toSourceFaceReentry h.2

end Poincare
