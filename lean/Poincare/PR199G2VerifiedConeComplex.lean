import Poincare.GlobalEdgeCyclicFan

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


end Poincare.PR199G2
