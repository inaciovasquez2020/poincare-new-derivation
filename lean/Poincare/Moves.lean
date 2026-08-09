import Poincare.Triangulation

namespace Poincare

inductive PachnerMove where
| move23
| move32
| move14
| move41


structure Move23Site where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  distinct :
    [a, b, c, d, e].Nodup

def Move23Site.leftTet (s : Move23Site) : Tet :=
  ⟨s.a, s.b, s.c, s.d⟩

def Move23Site.rightTet (s : Move23Site) : Tet :=
  ⟨s.a, s.b, s.c, s.e⟩

def Move23Site.newTet₀ (s : Move23Site) : Tet :=
  ⟨s.a, s.b, s.d, s.e⟩

def Move23Site.newTet₁ (s : Move23Site) : Tet :=
  ⟨s.a, s.c, s.d, s.e⟩

def Move23Site.newTet₂ (s : Move23Site) : Tet :=
  ⟨s.b, s.c, s.d, s.e⟩


def SameTetVertices (τ σ : Tet) : Prop :=
  ∀ v : Nat, v ∈ τ.verts ↔ v ∈ σ.verts

def Move23Site.RealizedIn (s : Move23Site) (K : Triangulation) : Prop :=
  (∃ τ ∈ K.tets, SameTetVertices τ s.leftTet) ∧
  (∃ τ ∈ K.tets, SameTetVertices τ s.rightTet)


def Move23Site.NewEdgeAbsent (s : Move23Site) (K : Triangulation) : Prop :=
  ∀ τ ∈ K.tets, ¬ (s.d ∈ τ.verts ∧ s.e ∈ τ.verts)


def Move23Site.SharedFaceExactlyTwo
    (s : Move23Site) (K : Triangulation) : Prop :=
  (K.tets.filter
      (fun τ =>
        s.a ∈ τ.verts ∧
        s.b ∈ τ.verts ∧
        s.c ∈ τ.verts)).length = 2


def Move23Site.LegalIn (s : Move23Site) (K : Triangulation) : Prop :=
  s.RealizedIn K ∧
  s.SharedFaceExactlyTwo K ∧
  s.NewEdgeAbsent K


def sameTetVerticesBool (τ σ : Tet) : Bool :=
  τ.verts.all (fun v => σ.verts.contains v) &&
  σ.verts.all (fun v => τ.verts.contains v)


theorem sameTetVerticesBool_eq_true_iff
    (τ σ : Tet) :
    sameTetVerticesBool τ σ = true ↔ SameTetVertices τ σ := by
  simp [sameTetVerticesBool, SameTetVertices]
  constructor
  · rintro ⟨hτσ, hστ⟩ v
    constructor
    · exact hτσ v
    · exact hστ v
  · intro h
    constructor
    · intro v hv
      exact (h v).1 hv
    · intro v hv
      exact (h v).2 hv

def eraseFirstSameTet (target : Tet) : List Tet → List Tet
  | [] => []
  | τ :: rest =>
      if sameTetVerticesBool τ target then
        rest
      else
        τ :: eraseFirstSameTet target rest

def Move23Site.replace (s : Move23Site) (K : Triangulation) : Triangulation :=
  let afterLeft := eraseFirstSameTet s.leftTet K.tets
  let afterRight := eraseFirstSameTet s.rightTet afterLeft
  { tets :=
      s.newTet₀ ::
      s.newTet₁ ::
      s.newTet₂ ::
      afterRight }

def applyMove (T : Triangulation) (_ : PachnerMove) : Triangulation := T
def selectMove (_T : Triangulation) : PachnerMove := PachnerMove.move23

end Poincare
