import Poincare.GlobalMove32SourceFaceReentryStep
import Mathlib.Tactic

namespace Poincare

abbrev SupportedVertexState
    (K : Triangulation) :=
  ↥((vertexSupport K).toFinset)

/--
A canonical represented-edge state is an ordered pair of distinct vertices
drawn from the finite represented vertex support.

The strict inequality makes the state an unordered ambient edge represented
in canonical increasing order.
-/
def SupportedEdgeState
    (K : Triangulation) :=
  {p : SupportedVertexState K × SupportedVertexState K //
    (p.1 : Nat) < (p.2 : Nat)}

noncomputable instance supportedEdgeStateFintype
    (K : Triangulation) :
    Fintype (SupportedEdgeState K) := by
  classical
  unfold SupportedEdgeState
  infer_instance

def canonicalEdgeKey
    (a b : Nat) :
    Nat × Nat :=
  if a < b then
    (a, b)
  else
    (b, a)

/--
Equality of canonical unordered-edge keys is exactly equality of the
unordered endpoint pair.
-/
theorem canonicalEdgeKey_eq_iff
    (a b c d : Nat)
    (hab : a ≠ b)
    (hcd : c ≠ d) :
    canonicalEdgeKey a b =
        canonicalEdgeKey c d ↔
      ((a = c ∧ b = d) ∨
       (a = d ∧ b = c)) := by
  unfold canonicalEdgeKey

  by_cases hablt : a < b <;>
    by_cases hcdlt : c < d <;>
      simp [hablt, hcdlt] <;>
      omega

def SupportedEdgeState.key
    {K : Triangulation}
    (q : SupportedEdgeState K) :
    Nat × Nat :=
  ((q.1.1 : Nat), (q.1.2 : Nat))

/--
Construct the canonical supported-edge state from two distinct supported
vertices.
-/
def supportedEdgeStateOfDistinct
    (K : Triangulation)
    (a b : Nat)
    (ha : a ∈ vertexSupport K)
    (hb : b ∈ vertexSupport K)
    (hab : a ≠ b) :
    SupportedEdgeState K := by
  have haFin :
      a ∈ (vertexSupport K).toFinset :=
    List.mem_toFinset.mpr ha

  have hbFin :
      b ∈ (vertexSupport K).toFinset :=
    List.mem_toFinset.mpr hb

  by_cases hablt : a < b

  · exact
      ⟨(
        ⟨a, haFin⟩,
        ⟨b, hbFin⟩
      ),
      hablt⟩

  · have hbalt :
        b < a := by
      omega

    exact
      ⟨(
        ⟨b, hbFin⟩,
        ⟨a, haFin⟩
      ),
      hbalt⟩

@[simp]
theorem supportedEdgeStateOfDistinct_key
    (K : Triangulation)
    (a b : Nat)
    (ha : a ∈ vertexSupport K)
    (hb : b ∈ vertexSupport K)
    (hab : a ≠ b) :
    (supportedEdgeStateOfDistinct
        K a b ha hb hab).key =
      canonicalEdgeKey a b := by
  by_cases hablt : a < b

  · simp [
      supportedEdgeStateOfDistinct,
      SupportedEdgeState.key,
      canonicalEdgeKey,
      hablt
    ]

  · simp [
      supportedEdgeStateOfDistinct,
      SupportedEdgeState.key,
      canonicalEdgeKey,
      hablt
    ]

/--
The shared edge of every realized Move32 site has two distinct endpoints
lying in the represented vertex support.
-/
theorem
    ClosedTriangulationCore.move32_sharedEdge_supported
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K) :
    s.d ∈ vertexSupport K ∧
      s.e ∈ vertexSupport K ∧
      s.d ≠ s.e := by
  have hfive :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct
      s hrealized

  have hde :
      s.d ≠ s.e := by
    have h := hfive
    simp at h
    omega

  obtain ⟨tau, htauK, hmatch⟩ :=
    hrealized.1

  have hdSupport :
      s.d ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [
      allVerts,
      List.mem_flatMap
    ]

    exact
      ⟨tau,
        htauK,
        (hmatch s.d).2
          (by
            simp [
              Move32Site.targetTet₀,
              Tet.verts
            ])⟩

  have heSupport :
      s.e ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [
      allVerts,
      List.mem_flatMap
    ]

    exact
      ⟨tau,
        htauK,
        (hmatch s.e).2
          (by
            simp [
              Move32Site.targetTet₀,
              Tet.verts
            ])⟩

  exact
    ⟨hdSupport,
      heSupport,
      hde⟩

/--
Canonical finite state attached to the shared edge of a realized Move32
site.
-/
def sharedSupportedEdgeState
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K) :
    SupportedEdgeState K :=
  supportedEdgeStateOfDistinct
    K
    s.d
    s.e
    (hcore.move32_sharedEdge_supported
      s hrealized).1
    (hcore.move32_sharedEdge_supported
      s hrealized).2.1
    (hcore.move32_sharedEdge_supported
      s hrealized).2.2

@[simp]
theorem sharedSupportedEdgeState_key
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K) :
    (sharedSupportedEdgeState
        hcore s hrealized).key =
      canonicalEdgeKey s.d s.e := by
  unfold sharedSupportedEdgeState

  exact
    supportedEdgeStateOfDistinct_key
      K
      s.d
      s.e
      (hcore.move32_sharedEdge_supported
        s hrealized).1
      (hcore.move32_sharedEdge_supported
        s hrealized).2.1
      (hcore.move32_sharedEdge_supported
        s hrealized).2.2

/--
A genuinely nonself Move32 reentry changes the canonical finite shared-edge
state.
-/
theorem
    ClosedTriangulationCore.sharedSupportedEdgeState_ne_of_nonself
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s s' : Move32Site)
    (hrealized : s.RealizedIn K)
    (hrealized' : s'.RealizedIn K)
    (hnonself :
      ¬ (
        (s'.d = s.d ∧
         s'.e = s.e) ∨
        (s'.d = s.e ∧
         s'.e = s.d)
      )) :
    sharedSupportedEdgeState
        hcore s' hrealized' ≠
      sharedSupportedEdgeState
        hcore s hrealized := by
  intro hstate

  have hkey :
      canonicalEdgeKey s'.d s'.e =
        canonicalEdgeKey s.d s.e := by
    calc
      canonicalEdgeKey s'.d s'.e =
          (sharedSupportedEdgeState
            hcore s' hrealized').key :=
        (sharedSupportedEdgeState_key
          hcore s' hrealized').symm

      _ =
          (sharedSupportedEdgeState
            hcore s hrealized).key :=
        congrArg
          (fun q : SupportedEdgeState K =>
            q.key)
          hstate

      _ =
          canonicalEdgeKey s.d s.e :=
        sharedSupportedEdgeState_key
          hcore s hrealized

  have hde' :
      s'.d ≠ s'.e :=
    (hcore.move32_sharedEdge_supported
      s' hrealized').2.2

  have hde :
      s.d ≠ s.e :=
    (hcore.move32_sharedEdge_supported
      s hrealized).2.2

  have hendpoints :
      (s'.d = s.d ∧
       s'.e = s.e) ∨
      (s'.d = s.e ∧
       s'.e = s.d) :=
    (canonicalEdgeKey_eq_iff
      s'.d
      s'.e
      s.d
      s.e
      hde'
      hde).1 hkey

  exact
    hnonself hendpoints

end Poincare
