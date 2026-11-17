import Poincare.GlobalEdgeCyclicFan
import Mathlib
import Poincare.Validity
import Poincare.TriangulationTopologicalGeometricCarrier
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

namespace Poincare.PR199G2

theorem ambientFan_distinct_indices_distinct_support
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    {sigma rho}
    (hne : sigma ≠ rho) :
    ¬ SameTetVertices
        (F.tetAt sigma) (F.tetAt rho) := by
  intro hsame
  apply hne
  apply F.tetAt_injective
  exact hcore.eq_of_mem_of_sameTetVertices
    (F.tetAt_mem sigma)
    (F.tetAt_mem rho)
    hsame

theorem unique_face_incident_pair
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {a b c : Nat}
    (habc : [a, b, c].Nodup)
    {tau rho eta : Tet}
    (htau : tau ∈ K.tets)
    (hrho : rho ∈ K.tets)
    (heta : eta ∈ K.tets)
    (htauFace :
      a ∈ tau.verts ∧
      b ∈ tau.verts ∧
      c ∈ tau.verts)
    (hrhoFace :
      a ∈ rho.verts ∧
      b ∈ rho.verts ∧
      c ∈ rho.verts)
    (hetaFace :
      a ∈ eta.verts ∧
      b ∈ eta.verts ∧
      c ∈ eta.verts)
    (hne : tau ≠ rho) :
    eta = tau ∨ eta = rho := by
  let incident :=
    K.tets.filter (fun t =>
      a ∈ t.verts ∧
      b ∈ t.verts ∧
      c ∈ t.verts)
  have hlen : incident.length = 2 :=
    hcore.2.2 a b c habc
      ⟨tau, htau, htauFace⟩
  have ht : tau ∈ incident := by
    simp [incident, htau, htauFace]
  have hr : rho ∈ incident := by
    simp [incident, hrho, hrhoFace]
  have he : eta ∈ incident := by
    simp [incident, heta, hetaFace]
  cases hi : incident with
  | nil =>
      simp [hi] at hlen
  | cons p tail =>
      cases tail with
      | nil =>
          simp [hi] at hlen
      | cons q rest =>
          cases rest with
          | cons r rs =>
              simp [hi] at hlen
          | nil =>
              have hp : tau = p ∨ tau = q := by
                simpa [hi] using ht
              have hq : rho = p ∨ rho = q := by
                simpa [hi] using hr
              have he' : eta = p ∨ eta = q := by
                simpa [hi] using he
              rcases hp with hp | hp
              · rcases hq with hq | hq
                · exact (hne (hp.trans hq.symm)).elim
                · rcases he' with he' | he'
                  · exact Or.inl (he'.trans hp.symm)
                  · exact Or.inr (he'.trans hq.symm)
              · rcases hq with hq | hq
                · rcases he' with he' | he'
                  · exact Or.inr (he'.trans hq.symm)
                  · exact Or.inl (he'.trans hp.symm)
                · exact (hne (hp.trans hq.symm)).elim

theorem ambientFan_shared_face_unique_index_pair
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x a b c : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (habc : [a, b, c].Nodup)
    (sigma rho alpha beta :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x})
    (hsr : sigma ≠ rho)
    (hab : alpha ≠ beta)
    (hfaceS :
      a ∈ (F.tetAt sigma).verts ∧
      b ∈ (F.tetAt sigma).verts ∧
      c ∈ (F.tetAt sigma).verts)
    (hfaceR :
      a ∈ (F.tetAt rho).verts ∧
      b ∈ (F.tetAt rho).verts ∧
      c ∈ (F.tetAt rho).verts)
    (hfaceA :
      a ∈ (F.tetAt alpha).verts ∧
      b ∈ (F.tetAt alpha).verts ∧
      c ∈ (F.tetAt alpha).verts)
    (hfaceB :
      a ∈ (F.tetAt beta).verts ∧
      b ∈ (F.tetAt beta).verts ∧
      c ∈ (F.tetAt beta).verts) :
    (sigma = alpha ∧ rho = beta) ∨
    (sigma = beta ∧ rho = alpha) := by

  have htetNe :
      F.tetAt sigma ≠ F.tetAt rho := by
    intro heq
    exact hsr (F.tetAt_injective heq)

  have hclass
      (eta :
        {t : LinkTriangle //
          t ∈ vertexLinkStarTriangles K v x})
      (hetaFace :
        a ∈ (F.tetAt eta).verts ∧
        b ∈ (F.tetAt eta).verts ∧
        c ∈ (F.tetAt eta).verts) :
      eta = sigma ∨ eta = rho := by

    have h :=
      unique_face_incident_pair
        hcore habc
        (F.tetAt_mem sigma)
        (F.tetAt_mem rho)
        (F.tetAt_mem eta)
        hfaceS hfaceR hetaFace htetNe

    rcases h with h | h
    · exact Or.inl (F.tetAt_injective h)
    · exact Or.inr (F.tetAt_injective h)

  rcases hclass alpha hfaceA with hA | hA
  · rcases hclass beta hfaceB with hB | hB
    · exact False.elim (hab (hA.trans hB.symm))
    · exact Or.inl ⟨hA.symm, hB.symm⟩
  · rcases hclass beta hfaceB with hB | hB
    · exact Or.inr ⟨hB.symm, hA.symm⟩
    · exact False.elim (hab (hA.trans hB.symm))

theorem ambientFan_each_face_has_distinct_index_pair
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x y : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (hface : [v, x, y].Nodup)
    (hrepresented :
      ∃ tau ∈ K.tets,
        v ∈ tau.verts ∧
        x ∈ tau.verts ∧
        y ∈ tau.verts) :
    ∃ sigma rho,
      sigma ≠ rho ∧
      v ∈ (F.tetAt sigma).verts ∧
      x ∈ (F.tetAt sigma).verts ∧
      y ∈ (F.tetAt sigma).verts ∧
      v ∈ (F.tetAt rho).verts ∧
      x ∈ (F.tetAt rho).verts ∧
      y ∈ (F.tetAt rho).verts := by
  obtain ⟨tau, ht, hv, hx, hy⟩ := hrepresented
  obtain ⟨rho, hr, hnot, hvr, hxr, hyr⟩ :=
    hcore.exists_other_tet_across_triangle
      hface ht hv hx hy
  obtain ⟨sigma, hsigma⟩ :=
    F.covers_ambient tau ht hv hx
  obtain ⟨beta, hbeta⟩ :=
    F.covers_ambient rho hr hvr hxr
  have hne : sigma ≠ beta := by
    intro heq
    have htEq : tau = rho := by
      calc
        tau = F.tetAt sigma := hsigma.symm
        _ = F.tetAt beta := congrArg F.tetAt heq
        _ = rho := hbeta
    apply hnot
    rw [htEq]
    intro w
    exact Iff.rfl
  refine ⟨sigma, beta, hne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hsigma] using hv
  · simpa [hsigma] using hx
  · simpa [hsigma] using hy
  · simpa [hbeta] using hvr
  · simpa [hbeta] using hxr
  · simpa [hbeta] using hyr

theorem ambientFan_adjacency_iff_shared_face
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (sigma rho :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x}) :
    (vertexLinkStarGraph K v x).Adj sigma rho ↔
      sigma ≠ rho ∧
      ∃ y, [v, x, y].Nodup ∧
        v ∈ (F.tetAt sigma).verts ∧
        x ∈ (F.tetAt sigma).verts ∧
        y ∈ (F.tetAt sigma).verts ∧
        v ∈ (F.tetAt rho).verts ∧
        x ∈ (F.tetAt rho).verts ∧
        y ∈ (F.tetAt rho).verts := by
  constructor
  · intro hadj
    obtain ⟨y, hn, hvs, hxs, hys,
        hvr, hxr, hyr⟩ :=
      hcore.ambientEdgeCyclicFan_adjacent_tets_share_face
        F hadj
    exact ⟨hadj.ne, y, hn, hvs, hxs, hys,
      hvr, hxr, hyr⟩
  · rintro ⟨hne, y, hn, _, _, hys,
        _, _, hyr⟩
    have hyv : y ≠ v := by
      simp only [List.nodup_cons, List.mem_cons,
        List.mem_singleton] at hn
      aesop
    have hyx : y ≠ x := by
      simp only [List.nodup_cons, List.mem_cons,
        List.mem_singleton] at hn
      aesop
    have hySigma : y ∈ sigma.1.verts :=
      ((F.tetAt sigma).mem_linkTriangleAt?_iff
        v y sigma.1 (F.tetAt_link sigma) hyv).2 hys
    have hyRho : y ∈ rho.1.verts :=
      ((F.tetAt rho).mem_linkTriangleAt?_iff
        v y rho.1 (F.tetAt_link rho) hyv).2 hyr
    apply (vertexLinkStarGraph_adj K v x sigma rho).2
    exact ⟨hne, sigma.2, rho.2,
      y, hyx, hySigma, hyRho⟩




/--
Four distinct common vertices force two tetrahedra
to have the same vertex support.
-/
theorem four_common_vertices_force_same_support
    (τ ρ : Tet)
    (v x y z : Nat)
    (hfour : [v, x, y, z].Nodup)
    (hτ : ∀ q ∈ [v, x, y, z], q ∈ τ.verts)
    (hρ : ∀ q ∈ [v, x, y, z], q ∈ ρ.verts) :
    SameTetVertices τ ρ := by
  classical
  let s : Finset Nat := [v, x, y, z].toFinset
  have hs : s.card = 4 := by
    simpa [s] using
      (List.toFinset_card_of_nodup hfour)

  have hsubτ : s ⊆ τ.verts.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr
      (hτ q (List.mem_toFinset.mp hq))

  have hsubρ : s ⊆ ρ.verts.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr
      (hρ q (List.mem_toFinset.mp hq))

  have hboundτ : τ.verts.toFinset.card ≤ s.card := by
    calc
      τ.verts.toFinset.card ≤ τ.verts.length :=
        List.toFinset_card_le _
      _ = 4 := rfl
      _ = s.card := hs.symm

  have hboundρ : ρ.verts.toFinset.card ≤ s.card := by
    calc
      ρ.verts.toFinset.card ≤ ρ.verts.length :=
        List.toFinset_card_le _
      _ = 4 := rfl
      _ = s.card := hs.symm

  have heqτ : s = τ.verts.toFinset :=
    Finset.eq_of_subset_of_card_le hsubτ hboundτ

  have heqρ : s = ρ.verts.toFinset :=
    Finset.eq_of_subset_of_card_le hsubρ hboundρ

  have heq :
      τ.verts.toFinset = ρ.verts.toFinset :=
    heqτ.symm.trans heqρ

  intro q
  have hp :
      (q ∈ τ.verts) = (q ∈ ρ.verts) := by
    simpa only [List.mem_toFinset] using
      (congrArg (fun t : Finset Nat => q ∈ t) heq)
  exact Eq.to_iff hp

/--
Two tetrahedra with distinct vertex supports cannot
have two different shared triangular faces containing
the same edge {v,x}.
-/
theorem unique_shared_face_third_vertex
    (τ ρ : Tet)
    (v x y z : Nat)
    (hnot : ¬ SameTetVertices τ ρ)
    (hvx : v ≠ x)
    (hyv : y ≠ v)
    (hyx : y ≠ x)
    (hzv : z ≠ v)
    (hzx : z ≠ x)
    (hvτ : v ∈ τ.verts)
    (hxτ : x ∈ τ.verts)
    (hyτ : y ∈ τ.verts)
    (hzτ : z ∈ τ.verts)
    (hvρ : v ∈ ρ.verts)
    (hxρ : x ∈ ρ.verts)
    (hyρ : y ∈ ρ.verts)
    (hzρ : z ∈ ρ.verts) :
    y = z := by
  by_contra hyz
  have hfour : [v, x, y, z].Nodup := by
    simp [List.nodup_cons]
    omega
  have hallτ :
      ∀ q ∈ [v, x, y, z], q ∈ τ.verts := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hvτ
    · exact hxτ
    · exact hyτ
    · exact hzτ
  have hallρ :
      ∀ q ∈ [v, x, y, z], q ∈ ρ.verts := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hvρ
    · exact hxρ
    · exact hyρ
    · exact hzρ
  exact hnot
    (four_common_vertices_force_same_support
      τ ρ v x y z hfour hallτ hallρ)


/-
A two-sided uniquely determined incidence relation
defines a genuine equivalence of its endpoint types.

This generic theorem does not assume that any particular
G2 face-edge relation is total or unique.
-/

noncomputable def uniqueRelationEquiv
    {A B : Type*}
    (R : A → B → Prop)
    (hAB : ∀ a, ∃! b, R a b)
    (hBA : ∀ b, ∃! a, R a b) :
    A ≃ B where
  toFun := fun a => Classical.choose (hAB a)
  invFun := fun b => Classical.choose (hBA b)
  left_inv := by
    intro a
    let b := Classical.choose (hAB a)
    have hab : R a b :=
      (Classical.choose_spec (hAB a)).1
    exact ((Classical.choose_spec (hBA b)).2 a hab).symm
  right_inv := by
    intro b
    let a := Classical.choose (hBA b)
    have hab : R a b :=
      (Classical.choose_spec (hBA b)).1
    exact ((Classical.choose_spec (hAB a)).2 b hab).symm


#print axioms ambientFan_distinct_indices_distinct_support
#print axioms unique_face_incident_pair
#print axioms ambientFan_shared_face_unique_index_pair
#print axioms ambientFan_each_face_has_distinct_index_pair
#print axioms ambientFan_adjacency_iff_shared_face
#print axioms four_common_vertices_force_same_support
#print axioms unique_shared_face_third_vertex
#print axioms uniqueRelationEquiv



/- Actual represented triangular faces through the central edge. -/

def RepresentedEdgeFace
    (K : Triangulation) (v x : Nat) :=
  {y : Nat //
    [v, x, y].Nodup ∧
    ∃ tau ∈ K.tets,
      v ∈ tau.verts ∧
      x ∈ tau.verts ∧
      y ∈ tau.verts}

/- Unordered pairs of fan indices. -/

noncomputable def fanUnorderedPair
    {K : Triangulation} {v x : Nat}
    (sigma rho :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x}) :
    Finset
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x} := by
  classical
  exact {sigma, rho}

/- Only genuine edges of the fan graph are admitted. -/

def FanUnorderedGraphEdge
    (K : Triangulation) (v x : Nat) :=
  {s : Finset
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x} //
    ∃ sigma rho,
      (vertexLinkStarGraph K v x).Adj sigma rho ∧
      s = fanUnorderedPair sigma rho}

/- Concrete incidence of a represented face and an unordered edge. -/

def faceEdgeIncident
    {K : Triangulation}
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x)
    (e : FanUnorderedGraphEdge K v x) : Prop :=
  ∃ sigma rho,
    e.1 = fanUnorderedPair sigma rho ∧
    v ∈ (F.tetAt sigma).verts ∧
    x ∈ (F.tetAt sigma).verts ∧
    f.1 ∈ (F.tetAt sigma).verts ∧
    v ∈ (F.tetAt rho).verts ∧
    x ∈ (F.tetAt rho).verts ∧
    f.1 ∈ (F.tetAt rho).verts

theorem representedFace_has_incident_graphEdge
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x) :
    ∃ e : FanUnorderedGraphEdge K v x,
      faceEdgeIncident F f e := by
  obtain ⟨sigma, rho, hne,
      hvs, hxs, hys, hvr, hxr, hyr⟩ :=
    ambientFan_each_face_has_distinct_index_pair
      hcore F f.2.1 f.2.2
  have hadj :
      (vertexLinkStarGraph K v x).Adj sigma rho :=
    (ambientFan_adjacency_iff_shared_face
      hcore F sigma rho).2
      ⟨hne, f.1, f.2.1,
        hvs, hxs, hys, hvr, hxr, hyr⟩
  let e : FanUnorderedGraphEdge K v x :=
    ⟨fanUnorderedPair sigma rho,
      ⟨sigma, rho, hadj, rfl⟩⟩
  exact ⟨e, sigma, rho, rfl,
    hvs, hxs, hys, hvr, hxr, hyr⟩

theorem graphEdge_has_incident_representedFace
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (e : FanUnorderedGraphEdge K v x) :
    ∃ f : RepresentedEdgeFace K v x,
      faceEdgeIncident F f e := by
  obtain ⟨sigma, rho, hadj, he⟩ := e.2
  obtain ⟨hne, y, hn,
      hvs, hxs, hys, hvr, hxr, hyr⟩ :=
    (ambientFan_adjacency_iff_shared_face
      hcore F sigma rho).1 hadj
  let f : RepresentedEdgeFace K v x :=
    ⟨y, hn,
      ⟨F.tetAt sigma,
        F.tetAt_mem sigma,
        hvs, hxs, hys⟩⟩
  exact ⟨f, sigma, rho, he,
    hvs, hxs, hys, hvr, hxr, hyr⟩

#print axioms representedFace_has_incident_graphEdge
#print axioms graphEdge_has_incident_representedFace




def faceEdgeIncidentStrict
    {K : Triangulation} {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x)
    (e : FanUnorderedGraphEdge K v x) : Prop :=
  ∃ sigma rho,
    (vertexLinkStarGraph K v x).Adj sigma rho ∧
    e.1 = fanUnorderedPair sigma rho ∧
    v ∈ (F.tetAt sigma).verts ∧
    x ∈ (F.tetAt sigma).verts ∧
    f.1 ∈ (F.tetAt sigma).verts ∧
    v ∈ (F.tetAt rho).verts ∧
    x ∈ (F.tetAt rho).verts ∧
    f.1 ∈ (F.tetAt rho).verts

theorem representedFace_has_strict_incident_edge
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x) :
    ∃ e : FanUnorderedGraphEdge K v x,
      faceEdgeIncidentStrict F f e := by
  obtain ⟨sigma, rho, hne,
      hvs, hxs, hys, hvr, hxr, hyr⟩ :=
    ambientFan_each_face_has_distinct_index_pair
      hcore F f.2.1 f.2.2
  have hadj :
      (vertexLinkStarGraph K v x).Adj sigma rho :=
    (ambientFan_adjacency_iff_shared_face
      hcore F sigma rho).2
      ⟨hne, f.1, f.2.1,
        hvs, hxs, hys, hvr, hxr, hyr⟩
  let e : FanUnorderedGraphEdge K v x :=
    ⟨fanUnorderedPair sigma rho,
      ⟨sigma, rho, hadj, rfl⟩⟩
  exact ⟨e, sigma, rho, hadj, rfl,
    hvs, hxs, hys, hvr, hxr, hyr⟩

theorem strict_incidence_unique_edge
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x)
    (e₁ e₂ : FanUnorderedGraphEdge K v x)
    (h₁ : faceEdgeIncidentStrict F f e₁)
    (h₂ : faceEdgeIncidentStrict F f e₂) :
    e₁ = e₂ := by
  obtain ⟨sigma, rho, hadj, he,
      hvs, hxs, hys, hvr, hxr, hyr⟩ := h₁
  obtain ⟨alpha, beta, hadj', he',
      hva, hxa, hya, hvb, hxb, hyb⟩ := h₂
  have hunique :=
    ambientFan_shared_face_unique_index_pair
      hcore F f.2.1 sigma rho alpha beta
      hadj.ne hadj'.ne
      ⟨hvs, hxs, hys⟩
      ⟨hvr, hxr, hyr⟩
      ⟨hva, hxa, hya⟩
      ⟨hvb, hxb, hyb⟩
  apply Subtype.ext
  calc
    e₁.1 = fanUnorderedPair sigma rho := he
    _ = fanUnorderedPair alpha beta := by
      rcases hunique with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb]
      · rw [ha, hb]
        exact Finset.pair_comm beta alpha
    _ = e₂.1 := he'.symm

#print axioms representedFace_has_strict_incident_edge
#print axioms strict_incidence_unique_edge
#check unique_shared_face_third_vertex




theorem strict_incidence_support_at_index
    {K : Triangulation} {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x)
    (e : FanUnorderedGraphEdge K v x)
    (h : faceEdgeIncidentStrict F f e)
    (sigma :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x})
    (hsigma : sigma ∈ e.1) :
    v ∈ (F.tetAt sigma).verts ∧
    x ∈ (F.tetAt sigma).verts ∧
    f.1 ∈ (F.tetAt sigma).verts := by
  obtain ⟨a, b, _, he, hva, hxa, hya,
      hvb, hxb, hyb⟩ := h
  have hs : sigma = a ∨ sigma = b := by
    rw [he] at hsigma
    simpa [fanUnorderedPair] using hsigma
  rcases hs with hs | hs
  · subst sigma
    exact ⟨hva, hxa, hya⟩
  · subst sigma
    exact ⟨hvb, hxb, hyb⟩

theorem strict_incidence_unique_face
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (e : FanUnorderedGraphEdge K v x)
    (f g : RepresentedEdgeFace K v x)
    (hf : faceEdgeIncidentStrict F f e)
    (hg : faceEdgeIncidentStrict F g e) :
    f = g := by
  obtain ⟨sigma, rho, hadj, he⟩ := e.2
  have hsigma : sigma ∈ e.1 := by
    rw [he]
    simp [fanUnorderedPair]
  have hrho : rho ∈ e.1 := by
    rw [he]
    simp [fanUnorderedPair]
  have hfs :=
    strict_incidence_support_at_index
      F f e hf sigma hsigma
  have hfr :=
    strict_incidence_support_at_index
      F f e hf rho hrho
  have hgs :=
    strict_incidence_support_at_index
      F g e hg sigma hsigma
  have hgr :=
    strict_incidence_support_at_index
      F g e hg rho hrho
  have hnot :
      ¬ SameTetVertices
          (F.tetAt sigma) (F.tetAt rho) :=
    ambientFan_distinct_indices_distinct_support
      hcore F hadj.ne
  have hvx : v ≠ x := by
    have hn := f.2.1
    simp only [List.nodup_cons, List.mem_cons,
      List.mem_singleton] at hn
    aesop
  have hyv : f.1 ≠ v := by
    have hn := f.2.1
    simp only [List.nodup_cons, List.mem_cons,
      List.mem_singleton] at hn
    aesop
  have hyx : f.1 ≠ x := by
    have hn := f.2.1
    simp only [List.nodup_cons, List.mem_cons,
      List.mem_singleton] at hn
    aesop
  have hzv : g.1 ≠ v := by
    have hn := g.2.1
    simp only [List.nodup_cons, List.mem_cons,
      List.mem_singleton] at hn
    aesop
  have hzx : g.1 ≠ x := by
    have hn := g.2.1
    simp only [List.nodup_cons, List.mem_cons,
      List.mem_singleton] at hn
    aesop
  have hyz : f.1 = g.1 :=
    unique_shared_face_third_vertex
      (F.tetAt sigma) (F.tetAt rho)
      v x f.1 g.1
      hnot hvx hyv hyx hzv hzx
      hfs.1 hfs.2.1 hfs.2.2 hgs.2.2
      hfr.1 hfr.2.1 hfr.2.2 hgr.2.2
  exact Subtype.ext hyz

theorem graphEdge_has_strict_incident_face
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (e : FanUnorderedGraphEdge K v x) :
    ∃ f : RepresentedEdgeFace K v x,
      faceEdgeIncidentStrict F f e := by
  obtain ⟨sigma, rho, hadj, he⟩ := e.2
  obtain ⟨_, y, hn, hvs, hxs, hys,
      hvr, hxr, hyr⟩ :=
    (ambientFan_adjacency_iff_shared_face
      hcore F sigma rho).1 hadj
  let f : RepresentedEdgeFace K v x :=
    ⟨y, hn,
      ⟨F.tetAt sigma,
        F.tetAt_mem sigma,
        hvs, hxs, hys⟩⟩
  exact ⟨f, sigma, rho, hadj, he,
    hvs, hxs, hys, hvr, hxr, hyr⟩

noncomputable def concreteFaceEdgeEquiv
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    RepresentedEdgeFace K v x ≃
      FanUnorderedGraphEdge K v x := by
  classical
  apply uniqueRelationEquiv (faceEdgeIncidentStrict F)
  · intro f
    obtain ⟨e, he⟩ :=
      representedFace_has_strict_incident_edge
        hcore F f
    refine ⟨e, he, ?_⟩
    intro e' he'
    exact strict_incidence_unique_edge
      hcore F f e' e he' he
  · intro e
    obtain ⟨f, hf⟩ :=
      graphEdge_has_strict_incident_face
        hcore F e
    refine ⟨f, hf, ?_⟩
    intro f' hf'
    exact strict_incidence_unique_face
      hcore F e f' f hf' hf

#print axioms strict_incidence_support_at_index
#print axioms strict_incidence_unique_face
#print axioms graphEdge_has_strict_incident_face
#print axioms concreteFaceEdgeEquiv




/-
Abstract vertices of the cone over the edge-link graph.

none    = the central cone vertex
some σ  = a vertex corresponding to fan index σ
-/

abbrev FanConeVertex
    (K : Triangulation) (v x : Nat) :=
  Option
    {t : LinkTriangle //
      t ∈ vertexLinkStarTriangles K v x}

/-
Each unoriented fan graph edge determines one triangle.
The graph edge is a two-element Finset.
-/

noncomputable def fanConeTriangle
    (K : Triangulation) (v x : Nat)
    (e : FanUnorderedGraphEdge K v x) :
    Finset (FanConeVertex K v x) := by
  classical
  exact insert none (e.1.image some)

/- The cone vertex belongs to every triangle. -/

theorem fanConeTriangle_center_mem
    {K : Triangulation} {v x : Nat}
    (e : FanUnorderedGraphEdge K v x) :
    (none : FanConeVertex K v x) ∈
      fanConeTriangle K v x e := by
  classical
  simp [fanConeTriangle]

/- Both graph-edge endpoints belong to its cone triangle. -/

theorem fanConeTriangle_endpoint_mem
    {K : Triangulation} {v x : Nat}
    (e : FanUnorderedGraphEdge K v x)
    (sigma :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x})
    (hsigma : sigma ∈ e.1) :
    (some sigma : FanConeVertex K v x) ∈
      fanConeTriangle K v x e := by
  classical
  simp only [fanConeTriangle, Finset.mem_insert,
    Finset.mem_image]
  right
  exact ⟨sigma, hsigma, rfl⟩

/- Every abstract cone triangle has exactly three vertices. -/

theorem fanConeTriangle_card_three
    {K : Triangulation} {v x : Nat}
    (e : FanUnorderedGraphEdge K v x) :
    (fanConeTriangle K v x e).card = 3 := by
  classical
  obtain ⟨sigma, rho, hadj, he⟩ := e.2
  have hne : sigma ≠ rho := hadj.ne
  simp [fanConeTriangle, he,
    fanUnorderedPair, hne]

/-
The already proved face-edge equivalence now indexes
the abstract cone triangles by actual represented faces.
-/

noncomputable def representedFaceConeTriangle
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x) :
    Finset (FanConeVertex K v x) :=
  fanConeTriangle K v x
    ((concreteFaceEdgeEquiv hcore F) f)

theorem representedFaceConeTriangle_card_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x) :
    (representedFaceConeTriangle hcore F f).card = 3 := by
  exact fanConeTriangle_card_three
    ((concreteFaceEdgeEquiv hcore F) f)

#print axioms fanConeTriangle_center_mem
#print axioms fanConeTriangle_endpoint_mem
#print axioms fanConeTriangle_card_three
#print axioms representedFaceConeTriangle_card_three




/- Exact intersection of two abstract cone triangles. -/

theorem fanConeTriangle_intersection
    {K : Triangulation} {v x : Nat}
    (e f : FanUnorderedGraphEdge K v x) :
    fanConeTriangle K v x e ∩
      fanConeTriangle K v x f =
    insert none ((e.1 ∩ f.1).image some) := by
  classical
  ext z
  cases z with
  | none =>
      simp [fanConeTriangle]
  | some sigma =>
      simp [fanConeTriangle]

/- Distinct graph edges produce distinct cone triangles. -/

theorem fanConeTriangle_injective
    {K : Triangulation} {v x : Nat}
    (e f : FanUnorderedGraphEdge K v x)
    (h : fanConeTriangle K v x e =
      fanConeTriangle K v x f) :
    e = f := by
  classical
  apply Subtype.ext
  ext sigma
  have hm := congrArg
    (fun s : Finset (FanConeVertex K v x) =>
      (some sigma : FanConeVertex K v x) ∈ s) h
  simpa [fanConeTriangle] using hm

/- The down-closed family generated by all cone triangles. -/

def IsFanConeSimplex
    (K : Triangulation) (v x : Nat)
    (s : Finset (FanConeVertex K v x)) : Prop :=
  ∃ e : FanUnorderedGraphEdge K v x,
    s ⊆ fanConeTriangle K v x e

theorem fanCone_simplex_downward_closed
    {K : Triangulation} {v x : Nat}
    {s t : Finset (FanConeVertex K v x)}
    (hs : IsFanConeSimplex K v x s)
    (hts : t ⊆ s) :
    IsFanConeSimplex K v x t := by
  obtain ⟨e, he⟩ := hs
  exact ⟨e, hts.trans he⟩

theorem fanCone_triangle_is_simplex
    {K : Triangulation} {v x : Nat}
    (e : FanUnorderedGraphEdge K v x) :
    IsFanConeSimplex K v x
      (fanConeTriangle K v x e) := by
  exact ⟨e, Finset.Subset.rfl⟩

#print axioms fanConeTriangle_intersection
#print axioms fanConeTriangle_injective
#print axioms fanCone_simplex_downward_closed
#print axioms fanCone_triangle_is_simplex




/- The abstract radial edge from the cone center to a fan index. -/

noncomputable def fanRadialEdge
    {K : Triangulation} {v x : Nat}
    (sigma :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x}) :
    Finset (FanConeVertex K v x) := by
  classical
  exact {none, some sigma}

theorem fanRadialEdge_card_two
    {K : Triangulation} {v x : Nat}
    (sigma :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x}) :
    (fanRadialEdge sigma).card = 2 := by
  classical
  simp [fanRadialEdge]

theorem fanRadialEdge_subset_triangle_iff
    {K : Triangulation} {v x : Nat}
    (sigma :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x})
    (e : FanUnorderedGraphEdge K v x) :
    fanRadialEdge sigma ⊆
        fanConeTriangle K v x e ↔
      sigma ∈ e.1 := by
  classical
  constructor
  · intro h
    have hs :
        (some sigma : FanConeVertex K v x) ∈
          fanConeTriangle K v x e :=
      h (by simp [fanRadialEdge])
    simpa [fanConeTriangle] using hs
  · intro hs
    intro z hz
    simp only [fanRadialEdge, Finset.mem_insert,
      Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · subst z
      exact fanConeTriangle_center_mem e
    · subst z
      exact fanConeTriangle_endpoint_mem e sigma hs

theorem fanRadialEdge_is_simplex_of_incident
    {K : Triangulation} {v x : Nat}
    (sigma :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x})
    (e : FanUnorderedGraphEdge K v x)
    (h : sigma ∈ e.1) :
    IsFanConeSimplex K v x
      (fanRadialEdge sigma) := by
  exact ⟨e,
    (fanRadialEdge_subset_triangle_iff sigma e).2 h⟩

/-
No degree-two assumption is used here.
This is the precise combinatorial radial-incidence law.
-/

#print axioms fanRadialEdge_card_two
#print axioms fanRadialEdge_subset_triangle_iff
#print axioms fanRadialEdge_is_simplex_of_incident




theorem ambientFan_graph_degree_two
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    VertexLinkStarDegreeTwo K v x := by
  have hrep : VertexLinkVertexRepresented K v x :=
    (vertexLinkVertexRepresented_iff_star_nonempty
      K v x).2
      ⟨F.start.1, F.start.2⟩
  exact hcore.vertexLinkStarDegreeTwo hrep

theorem ambientFan_graph_isCycles
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    (vertexLinkStarGraph K v x).IsCycles := by
  exact
    (ambientFan_graph_degree_two hcore F).isCycles K v x

#print axioms ambientFan_graph_degree_two
#print axioms ambientFan_graph_isCycles




theorem fanRadialEdge_exactly_two_triangles
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (sigma :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x}) :
    ∃ e₁ e₂ : FanUnorderedGraphEdge K v x,
      e₁ ≠ e₂ ∧
      ∀ e : FanUnorderedGraphEdge K v x,
        fanRadialEdge sigma ⊆
          fanConeTriangle K v x e ↔
        e = e₁ ∨ e = e₂ := by
  classical
  have hdeg := ambientFan_graph_degree_two hcore F
  obtain ⟨rho₁, rho₂, h₁ne, h₂ne, h₁₂,
      hadj₁, hadj₂, hall⟩ :=
    hdeg sigma.1 sigma.2
  have hmem₁ :
      rho₁ ∈ vertexLinkStarTriangles K v x :=
    (VertexLinkStarAdjacent.right_mem
      K v x sigma.1 rho₁ hadj₁)
  have hmem₂ :
      rho₂ ∈ vertexLinkStarTriangles K v x :=
    (VertexLinkStarAdjacent.right_mem
      K v x sigma.1 rho₂ hadj₂)
  let r₁ :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x} :=
    ⟨rho₁, hmem₁⟩
  let r₂ :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x} :=
    ⟨rho₂, hmem₂⟩
  have hs₁ : sigma ≠ r₁ := by
    intro h
    exact h₁ne (congrArg Subtype.val h.symm)
  have hs₂ : sigma ≠ r₂ := by
    intro h
    exact h₂ne (congrArg Subtype.val h.symm)
  have hr₁₂ : r₁ ≠ r₂ := by
    intro h
    exact h₁₂ (congrArg Subtype.val h)
  have ha₁ :
      (vertexLinkStarGraph K v x).Adj sigma r₁ :=
    (vertexLinkStarGraph_adj K v x sigma r₁).2
      ⟨hs₁, hadj₁⟩
  have ha₂ :
      (vertexLinkStarGraph K v x).Adj sigma r₂ :=
    (vertexLinkStarGraph_adj K v x sigma r₂).2
      ⟨hs₂, hadj₂⟩
  let e₁ : FanUnorderedGraphEdge K v x :=
    ⟨fanUnorderedPair sigma r₁,
      ⟨sigma, r₁, ha₁, rfl⟩⟩
  let e₂ : FanUnorderedGraphEdge K v x :=
    ⟨fanUnorderedPair sigma r₂,
      ⟨sigma, r₂, ha₂, rfl⟩⟩
  have hdistinct : e₁ ≠ e₂ := by
    intro heq
    have hm : r₁ ∈ e₂.1 := by
      have h₁ : r₁ ∈ e₁.1 := by
        simp [e₁, fanUnorderedPair]
      rw [← congrArg Subtype.val heq]
      exact h₁
    simp only [e₂, fanUnorderedPair,
      Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact hs₁ h.symm
    · exact hr₁₂ h
  refine ⟨e₁, e₂, hdistinct, ?_⟩
  intro e
  rw [fanRadialEdge_subset_triangle_iff]
  constructor
  · intro hs
    obtain ⟨a, b, hab, he⟩ := e.2
    have hpair : sigma = a ∨ sigma = b := by
      rw [he] at hs
      simpa [fanUnorderedPair] using hs
    rcases hpair with hsa | hsb
    · subst a
      have hstar :=
        (vertexLinkStarGraph_adj K v x sigma b).1 hab
      have hneVal : b.1 ≠ sigma.1 := by
        intro h
        exact hstar.1 (Subtype.ext h.symm)
      rcases hall b.1 hneVal hstar.2 with h | h
      · left
        apply Subtype.ext
        change e.1 = e₁.1
        rw [he]
        have hb : b = r₁ := Subtype.ext h
        rw [hb]
      · right
        apply Subtype.ext
        change e.1 = e₂.1
        rw [he]
        have hb : b = r₂ := Subtype.ext h
        rw [hb]
    · subst b
      have hstar :=
        (vertexLinkStarGraph_adj K v x sigma a).1 hab.symm
      have hneVal : a.1 ≠ sigma.1 := by
        intro h
        exact hstar.1 (Subtype.ext h.symm)
      rcases hall a.1 hneVal hstar.2 with h | h
      · left
        apply Subtype.ext
        change e.1 = e₁.1
        rw [he]
        have ha : a = r₁ := Subtype.ext h
        rw [ha]
        exact Finset.pair_comm r₁ sigma
      · right
        apply Subtype.ext
        change e.1 = e₂.1
        rw [he]
        have ha : a = r₂ := Subtype.ext h
        rw [ha]
        exact Finset.pair_comm r₂ sigma
  · intro h
    rcases h with rfl | rfl
    · simp [e₁, fanUnorderedPair]
    · simp [e₂, fanUnorderedPair]

#print axioms fanRadialEdge_exactly_two_triangles




/-
An outer boundary edge consists of the two
noncentral vertices of a fan graph edge.
-/

noncomputable def fanBoundaryEdge
    {K : Triangulation} {v x : Nat}
    (e : FanUnorderedGraphEdge K v x) :
    Finset (FanConeVertex K v x) := by
  classical
  exact e.1.image some

theorem fanBoundaryEdge_card_two
    {K : Triangulation} {v x : Nat}
    (e : FanUnorderedGraphEdge K v x) :
    (fanBoundaryEdge e).card = 2 := by
  classical
  obtain ⟨sigma, rho, hadj, he⟩ := e.2
  simp [fanBoundaryEdge, he,
    fanUnorderedPair, hadj.ne]

/-
An outer graph edge belongs to exactly its
own cone triangle.
-/

theorem fanBoundaryEdge_subset_triangle_iff
    {K : Triangulation} {v x : Nat}
    (e f : FanUnorderedGraphEdge K v x) :
    fanBoundaryEdge e ⊆
      fanConeTriangle K v x f ↔
    e = f := by
  classical
  constructor
  · intro h
    have hsub : e.1 ⊆ f.1 := by
      intro sigma hsigma
      have himage :
          (some sigma : FanConeVertex K v x) ∈
            fanBoundaryEdge e := by
        exact Finset.mem_image.mpr
          ⟨sigma, hsigma, rfl⟩
      have htriangle :
          (some sigma : FanConeVertex K v x) ∈
            fanConeTriangle K v x f :=
        h himage
      simpa [fanConeTriangle] using htriangle
    obtain ⟨a, b, hab, he⟩ := e.2
    obtain ⟨c, d, hcd, hf⟩ := f.2
    have hcardE : e.1.card = 2 := by
      rw [he]
      simp [fanUnorderedPair, hab.ne]
    have hcardF : f.1.card = 2 := by
      rw [hf]
      simp [fanUnorderedPair, hcd.ne]
    have hle : f.1.card ≤ e.1.card := by
      omega
    have heq : e.1 = f.1 :=
      Finset.eq_of_subset_of_card_le hsub hle
    exact Subtype.ext heq
  · intro heq
    subst f
    intro z hz
    change z ∈ insert none (e.1.image some)
    exact Finset.mem_insert_of_mem
      (show z ∈ e.1.image some from hz)

theorem fanBoundaryEdge_unique_incident_triangle
    {K : Triangulation} {v x : Nat}
    (e : FanUnorderedGraphEdge K v x) :
    ∃! f : FanUnorderedGraphEdge K v x,
      fanBoundaryEdge e ⊆
        fanConeTriangle K v x f := by
  refine ⟨e, ?_, ?_⟩
  · exact
      (fanBoundaryEdge_subset_triangle_iff e e).2 rfl
  · intro f hf
    exact
      (fanBoundaryEdge_subset_triangle_iff e f).1 hf |>.symm

#print axioms fanBoundaryEdge_card_two
#print axioms fanBoundaryEdge_subset_triangle_iff
#print axioms fanBoundaryEdge_unique_incident_triangle

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

theorem three_face_unique_extra_vertex
    (e f : Finset Nat)
    (he : e.card = 2)
    (hf : f.card = 3)
    (hef : e ⊆ f) :
    ∃! y : Nat,
      y ∉ e ∧ f = insert y e := by
  classical

  have hcard : (f \ e).card = 1 := by
    rw [Finset.card_sdiff_of_subset hef, hf, he]

  obtain ⟨y, hy⟩ :=
    Finset.card_eq_one.mp hcard

  have hym : y ∈ f \ e := by
    rw [hy]
    simp

  have hyf : y ∈ f :=
    (Finset.mem_sdiff.mp hym).1

  have hyne : y ∉ e :=
    (Finset.mem_sdiff.mp hym).2

  refine ⟨y, ⟨hyne, ?_⟩, ?_⟩

  · apply Finset.ext
    intro z
    constructor
    · intro hz
      by_cases hze : z ∈ e
      · simp [hze]
      · have hzm : z ∈ f \ e :=
          Finset.mem_sdiff.mpr ⟨hz, hze⟩
        rw [hy] at hzm
        have hzy : z = y := by
          simpa using hzm
        subst z
        simp
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl | hze
      · exact hyf
      · exact hef hze

  · intro z hz
    have hzf : z ∈ f := by
      rw [hz.2]
      simp
    have hzm : z ∈ f \ e :=
      Finset.mem_sdiff.mpr ⟨hzf, hz.1⟩
    rw [hy] at hzm
    simpa using hzm

theorem barycentricFlag_exists_representedFace
    {K : Triangulation}
    {v x : Nat}
    (a : BarycentricDualFlag K ({v, x} : Finset Nat)) :
    ∃ f : RepresentedEdgeFace K v x,
      a.face = insert f.1 ({v, x} : Finset Nat) := by
  classical

  obtain ⟨y, ⟨hy, hface⟩, _⟩ :=
    three_face_unique_extra_vertex
      ({v, x} : Finset Nat)
      a.face a.edge_card a.face_card a.edge_sub_face

  have hvx : v ≠ x := by
    intro h
    subst x
    have hc := a.edge_card
    simp at hc

  have hyv : y ≠ v := by
    intro h
    apply hy
    simp [h]

  have hyx : y ≠ x := by
    intro h
    apply hy
    simp [h]

  have hnodup : [v, x, y].Nodup := by
    simp [List.nodup_cons, hvx, hyv.symm, hyx.symm]

  have hvface : v ∈ a.face :=
    a.edge_sub_face (by simp)

  have hxface : x ∈ a.face :=
    a.edge_sub_face (by simp)

  have hyface : y ∈ a.face := by
    rw [hface]
    simp

  have hvT : v ∈ a.tet.verts := by
    simpa using a.face_sub_tet hvface

  have hxT : x ∈ a.tet.verts := by
    simpa using a.face_sub_tet hxface

  have hyT : y ∈ a.tet.verts := by
    simpa using a.face_sub_tet hyface

  refine ⟨⟨y, ⟨hnodup, ?_⟩⟩, hface⟩
  exact ⟨a.tet, a.tet_mem, hvT, hxT, hyT⟩

#print axioms three_face_unique_extra_vertex
#print axioms barycentricFlag_exists_representedFace

end Poincare.PR199G2

namespace Poincare.PR199G2

private theorem representedFace_extra_not_mem
    {K : Triangulation} {v x : Nat}
    (f : RepresentedEdgeFace K v x) :
    f.1 ∉ ({v, x} : Finset Nat) := by
  have hn := f.2.1
  simp only [List.nodup_cons, List.mem_cons,
    List.mem_singleton] at hn
  simp only [Finset.mem_insert, Finset.mem_singleton]
  aesop

private theorem representedFace_edge_distinct
    {K : Triangulation} {v x : Nat}
    (f : RepresentedEdgeFace K v x) :
    v ≠ x := by
  have hn := f.2.1
  simp only [List.nodup_cons, List.mem_cons,
    List.mem_singleton] at hn
  aesop

noncomputable def incidentPairToBarycentricFlag
    {K : Triangulation} {v x : Nat} :
    (Σ f : RepresentedEdgeFace K v x,
      {tau : Tet //
        tau ∈ K.tets ∧
        v ∈ tau.verts ∧
        x ∈ tau.verts ∧
        f.1 ∈ tau.verts})
    → BarycentricDualFlag K ({v, x} : Finset Nat) := by
  intro p
  let f := p.1
  let t := p.2
  have hvx := representedFace_edge_distinct f
  have hyne := representedFace_extra_not_mem f
  exact {
    face := insert f.1 ({v, x} : Finset Nat)
    tet := t.1
    edge_card := Finset.card_pair hvx
    face_card := by
      simp [hyne, Finset.card_pair hvx]
    tet_mem := t.2.1
    edge_sub_face := Finset.subset_insert _ _
    face_sub_tet := by
      intro z hz
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simpa using t.2.2.2.2
      · simpa using t.2.2.1
      · simpa using t.2.2.2.1
  }

theorem incidentPairToBarycentricFlag_bijective
    {K : Triangulation} {v x : Nat} :
    Function.Bijective
      (incidentPairToBarycentricFlag (K := K) (v := v) (x := x)) := by
  constructor
  · intro p q hpq
    have hface :
        insert p.1.1 ({v, x} : Finset Nat) =
        insert q.1.1 ({v, x} : Finset Nat) :=
      congrArg BarycentricDualFlag.face hpq
    have hnq := representedFace_extra_not_mem q.1
    have hthird : p.1.1 = q.1.1 := by
      have hm :
          q.1.1 ∈ insert p.1.1 ({v, x} : Finset Nat) := by
        rw [hface]
        simp
      rcases Finset.mem_insert.mp hm with h | h
      · exact h.symm
      · exact False.elim (hnq h)
    have hf : p.1 = q.1 := Subtype.ext hthird
    have ht : p.2.1 = q.2.1 :=
      congrArg BarycentricDualFlag.tet hpq
    cases p with
    | mk pf pt =>
      cases q with
      | mk qf qt =>
        cases hf
        cases pt with
        | mk ta hta =>
          cases qt with
          | mk tb htb =>
            cases ht
            rfl
  · intro a
    obtain ⟨f, hf⟩ :=
      barycentricFlag_exists_representedFace a
    have hv : v ∈ a.tet.verts := by
      simpa using
        (a.face_sub_tet
          (a.edge_sub_face (by simp : v ∈ ({v, x} : Finset Nat))))
    have hx : x ∈ a.tet.verts := by
      simpa using
        (a.face_sub_tet
          (a.edge_sub_face (by simp : x ∈ ({v, x} : Finset Nat))))
    have hy : f.1 ∈ a.tet.verts := by
      have hmem : f.1 ∈ a.face := by
        rw [hf]
        simp
      simpa using (a.face_sub_tet hmem)
    let t :
        {tau : Tet //
          tau ∈ K.tets ∧
          v ∈ tau.verts ∧
          x ∈ tau.verts ∧
          f.1 ∈ tau.verts} :=
      ⟨a.tet, a.tet_mem, hv, hx, hy⟩
    refine ⟨⟨f, t⟩, ?_⟩
    cases a with
    | mk face tet hc hfcard htm hes hft =>
      dsimp at hf
      subst face
      rfl

noncomputable def barycentricFlagIncidentEquiv
    {K : Triangulation} {v x : Nat} :
    BarycentricDualFlag K ({v, x} : Finset Nat)
    ≃
    (Σ f : RepresentedEdgeFace K v x,
      {tau : Tet //
        tau ∈ K.tets ∧
        v ∈ tau.verts ∧
        x ∈ tau.verts ∧
        f.1 ∈ tau.verts}) :=
  (Equiv.ofBijective
    incidentPairToBarycentricFlag
    incidentPairToBarycentricFlag_bijective).symm

#print axioms representedFace_extra_not_mem
#print axioms incidentPairToBarycentricFlag_bijective
#print axioms barycentricFlagIncidentEquiv

end Poincare.PR199G2

namespace Poincare
namespace PR199G2

private theorem reverse_incidence_for_equiv
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x)
    (g : FanUnorderedGraphEdge K v x)
    (hfg : faceEdgeIncidentStrict F f g)
    (tau : Tet)
    (htau : tau ∈ K.tets)
    (hv : v ∈ tau.verts)
    (hx : x ∈ tau.verts)
    (hy : f.1 ∈ tau.verts) :
    ∃ sigma :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x},
      sigma ∈ g.1 ∧ F.tetAt sigma = tau := by
  classical
  obtain ⟨a, b, hadj, he,
    hva, hxa, hya, hvb, hxb, hyb⟩ := hfg
  have hab : a ≠ b := hadj.ne
  have htetne : F.tetAt a ≠ F.tetAt b := by
    intro h
    exact hab (F.tetAt_injective h)

  let incident :=
    K.tets.filter
      (fun t =>
        v ∈ t.verts ∧
        x ∈ t.verts ∧
        f.1 ∈ t.verts)

  have hlen : incident.length = 2 := by
    exact hcore.2.2 v x f.1 f.2.1 f.2.2

  obtain ⟨u, w, huw⟩ :=
    List.length_eq_two.mp hlen

  have hmem (t : Tet)
      (ht : t ∈ K.tets)
      (hvt : v ∈ t.verts)
      (hxt : x ∈ t.verts)
      (hyt : f.1 ∈ t.verts) :
      t ∈ [u, w] := by
    have hh : t ∈ incident := by
      simp [incident, ht, hvt, hxt, hyt]
    rw [huw] at hh
    exact hh

  have ha : F.tetAt a = u ∨ F.tetAt a = w := by
    simpa using
      hmem (F.tetAt a) (F.tetAt_mem a)
        hva hxa hya

  have hb : F.tetAt b = u ∨ F.tetAt b = w := by
    simpa using
      hmem (F.tetAt b) (F.tetAt_mem b)
        hvb hxb hyb

  have ht : tau = u ∨ tau = w := by
    simpa using hmem tau htau hv hx hy

  have hcases :
      tau = F.tetAt a ∨
      tau = F.tetAt b := by
    rcases ha with ha | ha <;>
    rcases hb with hb | hb <;>
    rcases ht with ht | ht
    all_goals
      first
      | exact Or.inl (ht.trans ha.symm)
      | exact Or.inr (ht.trans hb.symm)
      | exact False.elim (htetne (ha.trans hb.symm))

  rcases hcases with h | h
  · refine ⟨a, ?_, h.symm⟩
    rw [he]
    simp [fanUnorderedPair]
  · refine ⟨b, ?_, h.symm⟩
    rw [he]
    simp [fanUnorderedPair]

noncomputable def strictFaceEndpointTetEquiv
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x)
    (g : FanUnorderedGraphEdge K v x)
    (hfg : faceEdgeIncidentStrict F f g) :
    {sigma :
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x} //
      sigma ∈ g.1}
    ≃
    {tau : Tet //
      tau ∈ K.tets ∧
      v ∈ tau.verts ∧
      x ∈ tau.verts ∧
      f.1 ∈ tau.verts} := by
  let toTet :
      {sigma :
        {t : LinkTriangle //
          t ∈ vertexLinkStarTriangles K v x} //
        sigma ∈ g.1}
      →
      {tau : Tet //
        tau ∈ K.tets ∧
        v ∈ tau.verts ∧
        x ∈ tau.verts ∧
        f.1 ∈ tau.verts} :=
    fun sigma =>
      ⟨F.tetAt sigma.1,
        F.tetAt_mem sigma.1,
        strict_incidence_support_at_index
          F f g hfg sigma.1 sigma.2⟩
  apply Equiv.ofBijective toTet
  constructor
  · intro sigma rho h
    apply Subtype.ext
    apply F.tetAt_injective
    exact congrArg Subtype.val h
  · intro tau
    obtain ⟨sigma, hsigma, heq⟩ :=
      reverse_incidence_for_equiv
        hcore F f g hfg tau.1
        tau.2.1 tau.2.2.1
        tau.2.2.2.1 tau.2.2.2.2
    refine ⟨⟨sigma, hsigma⟩, ?_⟩
    apply Subtype.ext
    exact heq

#print axioms strictFaceEndpointTetEquiv

end PR199G2
end Poincare

namespace Poincare
namespace PR199G2

noncomputable def graphEdgeForFace
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x) :
    FanUnorderedGraphEdge K v x :=
  Classical.choose
    (representedFace_has_strict_incident_edge hcore F f)

theorem graphEdgeForFace_strict
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (f : RepresentedEdgeFace K v x) :
    faceEdgeIncidentStrict F f
      (graphEdgeForFace hcore F f) :=
  Classical.choose_spec
    (representedFace_has_strict_incident_edge hcore F f)

noncomputable def globalFaceIndexedFlagEquiv
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    (Σ f : RepresentedEdgeFace K v x,
      {tau : Tet //
        tau ∈ K.tets ∧
        v ∈ tau.verts ∧
        x ∈ tau.verts ∧
        f.1 ∈ tau.verts})
    ≃
    (Σ f : RepresentedEdgeFace K v x,
      {sigma :
        {t : LinkTriangle //
          t ∈ vertexLinkStarTriangles K v x} //
        sigma ∈ (graphEdgeForFace hcore F f).1}) := by
  let localEquiv (f : RepresentedEdgeFace K v x) :=
    strictFaceEndpointTetEquiv
      hcore F f
      (graphEdgeForFace hcore F f)
      (graphEdgeForFace_strict hcore F f)
  exact {
    toFun := fun z =>
      ⟨z.1, (localEquiv z.1).symm z.2⟩
    invFun := fun z =>
      ⟨z.1, (localEquiv z.1) z.2⟩
    left_inv := by
      intro ⟨f, tau⟩
      simp
    right_inv := by
      intro ⟨f, sigma⟩
      simp
  }

#print axioms graphEdgeForFace_strict
#print axioms globalFaceIndexedFlagEquiv

end PR199G2
end Poincare

namespace Poincare
namespace PR199G2

theorem graphEdgeForFace_bijective
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    Function.Bijective
      (graphEdgeForFace hcore F) := by
  constructor
  · intro f g h
    apply strict_incidence_unique_face
      hcore F (graphEdgeForFace hcore F f)
      f g
      (graphEdgeForFace_strict hcore F f)
    rw [h]
    exact graphEdgeForFace_strict hcore F g
  · intro e
    obtain ⟨f, hf⟩ :=
      graphEdge_has_strict_incident_face hcore F e
    refine ⟨f, ?_⟩
    exact strict_incidence_unique_edge
      hcore F f
      (graphEdgeForFace hcore F f) e
      (graphEdgeForFace_strict hcore F f) hf

noncomputable def graphEdgeForFaceEquiv
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    RepresentedEdgeFace K v x ≃
      FanUnorderedGraphEdge K v x :=
  Equiv.ofBijective
    (graphEdgeForFace hcore F)
    (graphEdgeForFace_bijective hcore F)

#print axioms graphEdgeForFace_bijective
#print axioms graphEdgeForFaceEquiv

end PR199G2
end Poincare

namespace Poincare
namespace PR199G2

noncomputable def faceEndpointGraphEndpointEquiv
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    (Σ f : RepresentedEdgeFace K v x,
      {sigma :
        {t : LinkTriangle //
          t ∈ vertexLinkStarTriangles K v x} //
        sigma ∈ (graphEdgeForFace hcore F f).1})
    ≃
    (Σ g : FanUnorderedGraphEdge K v x,
      {sigma :
        {t : LinkTriangle //
          t ∈ vertexLinkStarTriangles K v x} //
        sigma ∈ g.1}) := by
  exact Equiv.sigmaCongr
    (graphEdgeForFaceEquiv hcore F)
    (fun _ => Equiv.refl _)

noncomputable def globalTetGraphEndpointEquiv
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    (Σ f : RepresentedEdgeFace K v x,
      {tau : Tet //
        tau ∈ K.tets ∧
        v ∈ tau.verts ∧
        x ∈ tau.verts ∧
        f.1 ∈ tau.verts})
    ≃
    (Σ g : FanUnorderedGraphEdge K v x,
      {sigma :
        {t : LinkTriangle //
          t ∈ vertexLinkStarTriangles K v x} //
        sigma ∈ g.1}) := by
  exact
    (globalFaceIndexedFlagEquiv hcore F).trans
      (faceEndpointGraphEndpointEquiv hcore F)

#print axioms faceEndpointGraphEndpointEquiv
#print axioms globalTetGraphEndpointEquiv

end PR199G2
end Poincare


namespace Poincare.PR199G2

noncomputable def barycentricFlagGraphEndpointEquiv
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    BarycentricDualFlag K ({v, x} : Finset Nat)
      ≃
    (Σ g : FanUnorderedGraphEdge K v x,
      {sigma :
        {t : LinkTriangle //
          t ∈ vertexLinkStarTriangles K v x} //
        sigma ∈ g.1}) :=
  (barycentricFlagIncidentEquiv
    (K := K) (v := v) (x := x)).trans
      (globalTetGraphEndpointEquiv hcore F)

#print axioms barycentricFlagGraphEndpointEquiv

end Poincare.PR199G2

namespace Poincare.PR199G2

/--
A union of convex sets sharing a common center
contains the segment from the center to every point.
-/
theorem convexFlagUnion_starShaped
    {ι : Type}
    (S : ι → Set (Nat → ℝ))
    (center : Nat → ℝ)
    (hconv : ∀ i, Convex ℝ (S i))
    (hcenter : ∀ i, center ∈ S i)
    {p : Nat → ℝ}
    (hp : p ∈ ⋃ i, S i)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    (1 - t) • center + t • p ∈ ⋃ i, S i := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  exact (hconv i) (hcenter i) hi
    (sub_nonneg.mpr ht1) ht0 (by ring)

#print axioms convexFlagUnion_starShaped

-- Inspect the exact realization interfaces.
#print barycentricDualFlagTriangle
#print barycentricEdgeDualCell
#print barycentricFlagGraphEndpointEquiv

end Poincare.PR199G2

namespace Poincare.PR199G2

theorem barycentricEdgeDualCell_star_segment
    (K : Triangulation)
    (e : Finset Nat)
    {p : Nat → ℝ}
    (hp : p ∈ barycentricEdgeDualCell K e)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    (1 - t) • finiteBarycenter e + t • p ∈
      barycentricEdgeDualCell K e := by
  unfold barycentricEdgeDualCell at hp ⊢
  apply convexFlagUnion_starShaped
    (S := fun a : BarycentricDualFlag K e =>
      barycentricDualFlagTriangle a)
    (center := finiteBarycenter e)
  · intro a
    unfold barycentricDualFlagTriangle
    unfold flagTriangle
    exact convex_convexHull ℝ _
  · intro a
    unfold barycentricDualFlagTriangle
    unfold flagTriangle
    apply subset_convexHull
    simp
  · exact hp
  · exact ht0
  · exact ht1

#print axioms barycentricEdgeDualCell_star_segment

end Poincare.PR199G2

namespace Poincare.PR199G2

/-- Every actual flag triangle contains the barycenter
of its central edge. -/
theorem dualFlagTriangle_contains_edgeBarycenter
    {K : Triangulation}
    {e : Finset Nat}
    (a : BarycentricDualFlag K e) :
    finiteBarycenter e ∈ barycentricDualFlagTriangle a := by
  unfold barycentricDualFlagTriangle flagTriangle
  apply subset_convexHull
  simp

#print axioms dualFlagTriangle_contains_edgeBarycenter

-- Exact intersection-theorem interfaces.
#check closedCore_actualDualFlags_allSupportCases
#check closedCore_sameFace_distinctTets_intersection_segment
#check closedCore_distinctFaces_sameTet_intersection_segment
#check closedCore_distinctFlags_triangle_intersection_singleton
#check sameSupports_dualFlagTriangle_intersection

-- Exact combinatorial correspondence.
#check barycentricFlagGraphEndpointEquiv

end Poincare.PR199G2

namespace Poincare.PR199G2

/--
The actual geometric dual cell is exactly the union
of geometric triangles indexed by cyclic-fan incidences.
-/
theorem barycentricEdgeDualCell_eq_graphIndexedUnion
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    barycentricEdgeDualCell K ({v, x} : Finset Nat) =
      ⋃ z :
        (Σ g : FanUnorderedGraphEdge K v x,
          {sigma :
            {t : LinkTriangle //
              t ∈ vertexLinkStarTriangles K v x} //
            sigma ∈ g.1}),
        barycentricDualFlagTriangle
          ((barycentricFlagGraphEndpointEquiv hcore F).symm z) := by
  classical
  let E := barycentricFlagGraphEndpointEquiv hcore F
  unfold barycentricEdgeDualCell
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨E a, ?_⟩
    change p ∈ barycentricDualFlagTriangle (E.symm (E a))
    simpa only [Equiv.symm_apply_apply] using ha
  · rintro ⟨z, hz⟩
    exact ⟨E.symm z, hz⟩

#print axioms barycentricEdgeDualCell_eq_graphIndexedUnion

end Poincare.PR199G2

namespace Poincare.PR199G2

/--
Complete geometric intersection classification
for two genuine barycentric dual flags in a
closed triangulation core.
-/
theorem closedCore_dualFlags_completeIntersection
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (e : Finset Nat)
    (A B : BarycentricDualFlag K e) :
    (A.face = B.face ∧
      A.tet.verts.toFinset = B.tet.verts.toFinset ∧
      barycentricDualFlagTriangle A ∩
        barycentricDualFlagTriangle B =
        barycentricDualFlagTriangle A)
    ∨
    (A.face = B.face ∧
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset ∧
      barycentricDualFlagTriangle A ∩
        barycentricDualFlagTriangle B =
        segment ℝ
          (finiteBarycenter e)
          (finiteBarycenter A.face))
    ∨
    (A.face ≠ B.face ∧
      A.tet.verts.toFinset = B.tet.verts.toFinset ∧
      barycentricDualFlagTriangle A ∩
        barycentricDualFlagTriangle B =
        segment ℝ
          (finiteBarycenter e)
          (finiteBarycenter A.tet.verts.toFinset))
    ∨
    (A.face ≠ B.face ∧
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset ∧
      barycentricDualFlagTriangle A ∩
        barycentricDualFlagTriangle B =
        {finiteBarycenter e}) := by
  classical
  by_cases hface : A.face = B.face
  · by_cases htet :
        A.tet.verts.toFinset = B.tet.verts.toFinset
    · left
      exact ⟨hface, htet,
        sameSupports_dualFlagTriangle_intersection
          e A B hface htet⟩
    · right
      left
      exact ⟨hface, htet,
        closedCore_sameFace_distinctTets_intersection_segment
          hcore e A B hface htet⟩
  · by_cases htet :
        A.tet.verts.toFinset = B.tet.verts.toFinset
    · right
      right
      left
      exact ⟨hface, htet,
        closedCore_distinctFaces_sameTet_intersection_segment
          hcore e A B hface htet⟩
    · right
      right
      right
      exact ⟨hface, htet,
        closedCore_distinctFlags_triangle_intersection_singleton
          hcore e A B hface htet⟩

/--
The complete geometric intersection classification,
transported through the verified cyclic-fan
flag-to-graph-endpoint equivalence.
-/
theorem closedCore_graphIndexed_completeIntersection
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (z w :
      Σ g : FanUnorderedGraphEdge K v x,
        {sigma :
          {t : LinkTriangle //
            t ∈ vertexLinkStarTriangles K v x} //
          sigma ∈ g.1}) :
    let E := barycentricFlagGraphEndpointEquiv hcore F
    let A := E.symm z
    let B := E.symm w
    (A.face = B.face ∧
      A.tet.verts.toFinset = B.tet.verts.toFinset ∧
      barycentricDualFlagTriangle A ∩
        barycentricDualFlagTriangle B =
        barycentricDualFlagTriangle A)
    ∨
    (A.face = B.face ∧
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset ∧
      barycentricDualFlagTriangle A ∩
        barycentricDualFlagTriangle B =
        segment ℝ
          (finiteBarycenter ({v, x} : Finset Nat))
          (finiteBarycenter A.face))
    ∨
    (A.face ≠ B.face ∧
      A.tet.verts.toFinset = B.tet.verts.toFinset ∧
      barycentricDualFlagTriangle A ∩
        barycentricDualFlagTriangle B =
        segment ℝ
          (finiteBarycenter ({v, x} : Finset Nat))
          (finiteBarycenter A.tet.verts.toFinset))
    ∨
    (A.face ≠ B.face ∧
      A.tet.verts.toFinset ≠ B.tet.verts.toFinset ∧
      barycentricDualFlagTriangle A ∩
        barycentricDualFlagTriangle B =
        {finiteBarycenter ({v, x} : Finset Nat)}) := by
  dsimp
  exact closedCore_dualFlags_completeIntersection
    hcore ({v, x} : Finset Nat)
    ((barycentricFlagGraphEndpointEquiv hcore F).symm z)
    ((barycentricFlagGraphEndpointEquiv hcore F).symm w)

#print axioms closedCore_dualFlags_completeIntersection
#print axioms closedCore_graphIndexed_completeIntersection
#print axioms barycentricEdgeDualCell_eq_graphIndexedUnion
#print axioms barycentricEdgeDualCell_star_segment
#print axioms barycentricFlagGraphEndpointEquiv

end Poincare.PR199G2

namespace Poincare.PR199G2

theorem finite_fan_vertices
    {K : Triangulation} {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    Finite
      {t : LinkTriangle //
        t ∈ vertexLinkStarTriangles K v x} := by
  classical
  apply Finite.of_injective
    (fun sigma =>
      (⟨F.tetAt sigma,
        List.mem_toFinset.mpr (F.tetAt_mem sigma)⟩ :
        K.tets.toFinset))
  intro a b h
  apply F.tetAt_injective
  exact congrArg Subtype.val h

/-- Finite incidences via an explicit injection into
finite subsets paired with finite fan vertices. -/
theorem finite_graph_incidence
    {K : Triangulation} {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    Finite
      (Σ g : FanUnorderedGraphEdge K v x,
        {sigma :
          {t : LinkTriangle //
            t ∈ vertexLinkStarTriangles K v x} //
          sigma ∈ g.1}) := by
  classical
  letI := finite_fan_vertices F
  haveI : Finite
      (Finset
        {t : LinkTriangle //
          t ∈ vertexLinkStarTriangles K v x}) :=
    inferInstance
  apply Finite.of_injective
    (fun z :
      (Σ g : FanUnorderedGraphEdge K v x,
        {sigma :
          {t : LinkTriangle //
            t ∈ vertexLinkStarTriangles K v x} //
          sigma ∈ g.1}) =>
      (z.1.1, z.2.1))
  intro a b h
  rcases a with ⟨⟨ga, hga⟩, ⟨sa, hsa⟩⟩
  rcases b with ⟨⟨gb, hgb⟩, ⟨sb, hsb⟩⟩
  have he : ga = gb := congrArg Prod.fst h
  have hs : sa = sb := congrArg Prod.snd h
  subst gb
  subst sb
  rfl

theorem finite_barycentric_flags
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    Finite (BarycentricDualFlag K ({v, x} : Finset Nat)) := by
  classical
  letI := finite_graph_incidence F
  exact Finite.of_injective
    (barycentricFlagGraphEndpointEquiv hcore F)
    (barycentricFlagGraphEndpointEquiv hcore F).injective

/-- Reverse: finiteness of barycentric flags
transfers back to graph incidences. -/
theorem finite_incidence_of_finite_flags
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    [Finite (BarycentricDualFlag K ({v, x} : Finset Nat))] :
    Finite
      (Σ g : FanUnorderedGraphEdge K v x,
        {sigma :
          {t : LinkTriangle //
            t ∈ vertexLinkStarTriangles K v x} //
          sigma ∈ g.1}) := by
  exact Finite.of_injective
    (barycentricFlagGraphEndpointEquiv hcore F).symm
    (barycentricFlagGraphEndpointEquiv hcore F).symm.injective

#print axioms finite_fan_vertices
#print axioms finite_graph_incidence
#print axioms finite_barycentric_flags
#print axioms finite_incidence_of_finite_flags

end Poincare.PR199G2

namespace Poincare.PR199G2

/-- Each actual geometric dual-flag triangle is compact. -/
theorem barycentricDualFlagTriangle_isCompact
    {K : Triangulation}
    {e : Finset Nat}
    (a : BarycentricDualFlag K e) :
    IsCompact (barycentricDualFlagTriangle a) := by
  unfold barycentricDualFlagTriangle flagTriangle
  have hs :
      ({finiteBarycenter e,
        finiteBarycenter a.face,
        finiteBarycenter a.tet.verts.toFinset}
        : Set (Nat → ℝ)).Finite := by
    simp
  exact hs.isCompact_convexHull ℝ

/-- The actual edge-dual cell is compact under
the closed-core and ambient cyclic-fan hypotheses. -/
theorem barycentricEdgeDualCell_isCompact
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x) :
    IsCompact
      (barycentricEdgeDualCell K
        ({v, x} : Finset Nat)) := by
  classical
  letI := finite_barycentric_flags hcore F
  unfold barycentricEdgeDualCell
  exact isCompact_iUnion
    (fun a : BarycentricDualFlag K
      ({v, x} : Finset Nat) =>
      barycentricDualFlagTriangle_isCompact a)

#print axioms barycentricDualFlagTriangle_isCompact
#print axioms barycentricEdgeDualCell_isCompact

end Poincare.PR199G2

namespace Poincare.PR199G2

/-- Three coordinate observations uniquely recover the
coefficients of a nested-support affine flag. -/
theorem flag_affine_coefficients_unique
    (be bf bt : Nat → ℝ)
    (p q r : Nat)
    (hpe : be p = 1 / 2)
    (hqe : be q = 0)
    (hre : be r = 0)
    (hpf : bf p = 1 / 3)
    (hqf : bf q = 1 / 3)
    (hrf : bf r = 0)
    (hpt : bt p = 1 / 4)
    (hqt : bt q = 1 / 4)
    (hrt : bt r = 1 / 4)
    (a b c a' b' c' : ℝ)
    (h :
      (fun n : Nat =>
        a * be n + b * bf n + c * bt n) =
      (fun n : Nat =>
        a' * be n + b' * bf n + c' * bt n)) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hp := congrFun h p
  have hq := congrFun h q
  have hr := congrFun h r
  rw [hpe, hpf, hpt] at hp
  rw [hqe, hqf, hqt] at hq
  rw [hre, hrf, hrt] at hr
  constructor
  · linarith
  constructor
  · linarith
  · linarith

#print axioms flag_affine_coefficients_unique

end Poincare.PR199G2

namespace Poincare.PR199G2

/-- Exact coordinate of the actual uniform barycenter
in the canonical Pi-space. -/
theorem finiteBarycenter_coordinate
    (A : Finset Nat) (j : Nat) :
    finiteBarycenter A j =
      if j ∈ A then (A.card : ℝ)⁻¹ else 0 := by
  classical
  simp [finiteBarycenter,
    triangulationTopologicalGeometricVertex,
    Pi.single_apply, eq_comm]
  by_cases hj : j ∈ A
  · rw [if_pos hj]
    rw [Finset.sum_eq_single (⟨j, hj⟩ : A)]
    · simp
    · intro b hb hne
      have hbj : (b : Nat) ≠ j := by
        intro he
        apply hne
        exact Subtype.ext he
      simp [Ne.symm hbj]
    · intro hnot
      exact (hnot (Finset.mem_attach A (⟨j, hj⟩ : A))).elim
  · rw [if_neg hj]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hne : j ≠ (b : Nat) := by
      intro he
      apply hj
      rw [he]
      exact b.property
    simp [hne]

#print axioms finiteBarycenter_coordinate

end Poincare.PR199G2

namespace Poincare.PR199G2

/-- Affine coefficient uniqueness for the actual
barycenters of a genuine edge-face-tetrahedron flag.

The hypotheses explicitly exhibit one vertex in each
successive support difference. -/
theorem actualFlag_affine_coefficients_unique
    {K : Triangulation}
    {e : Finset Nat}
    (a : BarycentricDualFlag K e)
    (htcard : a.tet.verts.toFinset.card = 4)
    (p q r : Nat)
    (hp : p ∈ e)
    (hqface : q ∈ a.face)
    (hqedge : q ∉ e)
    (hrtet : r ∈ a.tet.verts.toFinset)
    (hrface : r ∉ a.face)
    (α β γ α' β' γ' : ℝ)
    (heq :
      (fun n : Nat =>
        α * finiteBarycenter e n +
        β * finiteBarycenter a.face n +
        γ * finiteBarycenter a.tet.verts.toFinset n) =
      (fun n : Nat =>
        α' * finiteBarycenter e n +
        β' * finiteBarycenter a.face n +
        γ' * finiteBarycenter a.tet.verts.toFinset n)) :
    α = α' ∧ β = β' ∧ γ = γ' := by
  have hpface : p ∈ a.face := a.edge_sub_face hp
  have hptet : p ∈ a.tet.verts.toFinset :=
    a.face_sub_tet hpface
  have hqtet : q ∈ a.tet.verts.toFinset :=
    a.face_sub_tet hqface
  have hredge : r ∉ e := by
    intro hre
    exact hrface (a.edge_sub_face hre)

  have hpe : finiteBarycenter e p = 1 / 2 := by
    rw [finiteBarycenter_coordinate, if_pos hp, a.edge_card]
    norm_num
  have hqe : finiteBarycenter e q = 0 := by
    rw [finiteBarycenter_coordinate, if_neg hqedge]
  have hre : finiteBarycenter e r = 0 := by
    rw [finiteBarycenter_coordinate, if_neg hredge]

  have hpf : finiteBarycenter a.face p = 1 / 3 := by
    rw [finiteBarycenter_coordinate, if_pos hpface, a.face_card]
    norm_num
  have hqf : finiteBarycenter a.face q = 1 / 3 := by
    rw [finiteBarycenter_coordinate, if_pos hqface, a.face_card]
    norm_num
  have hrf : finiteBarycenter a.face r = 0 := by
    rw [finiteBarycenter_coordinate, if_neg hrface]

  have hpt : finiteBarycenter a.tet.verts.toFinset p = 1 / 4 := by
    rw [finiteBarycenter_coordinate, if_pos hptet, htcard]
    norm_num
  have hqt : finiteBarycenter a.tet.verts.toFinset q = 1 / 4 := by
    rw [finiteBarycenter_coordinate, if_pos hqtet, htcard]
    norm_num
  have hrt : finiteBarycenter a.tet.verts.toFinset r = 1 / 4 := by
    rw [finiteBarycenter_coordinate, if_pos hrtet, htcard]
    norm_num

  exact flag_affine_coefficients_unique
    (finiteBarycenter e)
    (finiteBarycenter a.face)
    (finiteBarycenter a.tet.verts.toFinset)
    p q r
    hpe hqe hre hpf hqf hrf hpt hqt hrt
    α β γ α' β' γ' heq

#print axioms actualFlag_affine_coefficients_unique

end Poincare.PR199G2

namespace Poincare.PR199G2

/-- A nested edge-face-tetrahedron flag has a
vertex at each successive support level. -/
theorem actualFlag_support_witnesses
    {K : Triangulation}
    {e : Finset Nat}
    (a : BarycentricDualFlag K e)
    (htcard : a.tet.verts.toFinset.card = 4) :
    ∃ p q r : Nat,
      p ∈ e ∧
      q ∈ a.face ∧ q ∉ e ∧
      r ∈ a.tet.verts.toFinset ∧
      r ∉ a.face := by
  have hecard : e.card = 2 := a.edge_card
  have hfcard : a.face.card = 3 := a.face_card
  obtain ⟨p, hp⟩ : e.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨q, hqface, hqedge⟩ :
      ∃ q : Nat, q ∈ a.face ∧ q ∉ e := by
    by_contra hn
    have hsub : a.face ⊆ e := by
      intro y hy
      by_contra hnot
      exact hn ⟨y, hy, hnot⟩
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨r, hrtet, hrface⟩ :
      ∃ r : Nat,
        r ∈ a.tet.verts.toFinset ∧ r ∉ a.face := by
    by_contra hn
    have hsub : a.tet.verts.toFinset ⊆ a.face := by
      intro y hy
      by_contra hnot
      exact hn ⟨y, hy, hnot⟩
    have hle := Finset.card_le_card hsub
    omega
  exact ⟨p, q, r, hp, hqface, hqedge, hrtet, hrface⟩

/-- The actual barycentric flag map uniquely
determines its affine coefficients without
separate vertex-witness hypotheses. -/
theorem actualFlag_affine_coefficients_unique_no_witnesses
    {K : Triangulation}
    {e : Finset Nat}
    (a : BarycentricDualFlag K e)
    (htcard : a.tet.verts.toFinset.card = 4)
    (α β γ α' β' γ' : ℝ)
    (heq :
      (fun n : Nat =>
        α * finiteBarycenter e n +
        β * finiteBarycenter a.face n +
        γ * finiteBarycenter a.tet.verts.toFinset n) =
      (fun n : Nat =>
        α' * finiteBarycenter e n +
        β' * finiteBarycenter a.face n +
        γ' * finiteBarycenter a.tet.verts.toFinset n)) :
    α = α' ∧ β = β' ∧ γ = γ' := by
  obtain ⟨p, q, r, hp, hqface, hqedge, hrtet, hrface⟩ :=
    actualFlag_support_witnesses a htcard
  exact actualFlag_affine_coefficients_unique
    a htcard p q r hp hqface hqedge hrtet hrface
    α β γ α' β' γ' heq

#print axioms actualFlag_support_witnesses
#print axioms actualFlag_affine_coefficients_unique_no_witnesses

end Poincare.PR199G2
