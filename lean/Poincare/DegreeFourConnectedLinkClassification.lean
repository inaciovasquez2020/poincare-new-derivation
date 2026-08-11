import Poincare.DegreeFourVertexLinkClassification

namespace Poincare

/-- In a closed core, two distinct represented tetrahedra containing the same
represented triangular face are the only represented tetrahedra containing
that face.  This is the exact incidence-two forcing principle used to close
the target-present five-tetrahedron cluster under face adjacency. -/
theorem ClosedTriangulationCore.eq_left_or_eq_right_of_common_face
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {a b c : Nat}
    (hface : [a, b, c].Nodup)
    {tau rho : Tet}
    (htauK : tau ∈ K.tets)
    (hrhoK : rho ∈ K.tets)
    (htauFace : a ∈ tau.verts ∧ b ∈ tau.verts ∧ c ∈ tau.verts)
    (hrhoFace : a ∈ rho.verts ∧ b ∈ rho.verts ∧ c ∈ rho.verts)
    (hne : tau ≠ rho)
    {sigma : Tet}
    (hsigmaK : sigma ∈ K.tets)
    (hsigmaFace : a ∈ sigma.verts ∧ b ∈ sigma.verts ∧ c ∈ sigma.verts) :
    sigma = tau ∨ sigma = rho := by
  classical
  let p : Tet → Bool := fun xi ↦
    decide (a ∈ xi.verts ∧ b ∈ xi.verts ∧ c ∈ xi.verts)
  have hrepresented : ∃ xi ∈ K.tets,
      a ∈ xi.verts ∧ b ∈ xi.verts ∧ c ∈ xi.verts :=
    ⟨tau, htauK, htauFace⟩
  have hlength : (K.tets.filter p).length = 2 := by
    simpa [p] using hcore.2.2 a b c hface hrepresented
  obtain ⟨u, w, huw⟩ := List.length_eq_two.mp hlength
  have htau : tau = u ∨ tau = w := by
    have : tau ∈ K.tets.filter p := by simp [p, htauK, htauFace]
    rw [huw] at this
    simpa using this
  have hrho : rho = u ∨ rho = w := by
    have : rho ∈ K.tets.filter p := by simp [p, hrhoK, hrhoFace]
    rw [huw] at this
    simpa using this
  have hsigma : sigma = u ∨ sigma = w := by
    have : sigma ∈ K.tets.filter p := by simp [p, hsigmaK, hsigmaFace]
    rw [huw] at this
    simpa using this
  rcases htau with rfl | rfl <;>
    rcases hrho with rfl | rfl <;>
    rcases hsigma with rfl | rfl <;>
    simp_all

/-- In a connected vertex link, a nonempty family of represented link
triangles that is closed under link adjacency contains every represented link
triangle.  This is the propagation principle that excludes an additional
four-simplex block meeting a degree-four boundary cluster only at a vertex. -/
theorem VertexLinkConnected.all_of_adjacent_closed
    {K : Triangulation}
    {v : Nat}
    (hconnected : VertexLinkConnected K v)
    (C : LinkTriangle → Prop)
    {σ₀ : LinkTriangle}
    (hσ₀ : σ₀ ∈ vertexLinkTriangles K v)
    (hC₀ : C σ₀)
    (hclosed : ∀ σ ρ,
      VertexLinkAdjacent K v σ ρ → C σ → C ρ) :
    ∀ ρ ∈ vertexLinkTriangles K v, C ρ := by
  intro ρ hρ
  have hpath := hconnected σ₀ hσ₀ ρ hρ
  exact Relation.ReflTransGen.trans_induction_on
    (motive := fun {σ ρ} _ => C σ → C ρ)
    hpath
    (fun _ hC => hC)
    (fun hadj hC => hclosed _ _ hadj hC)
    (fun _ _ ih₁ ih₂ hC => ih₂ (ih₁ hC))
    hC₀

/-- In the target-present branch at a degree-four center, the four source
tetrahedra fill the entire represented vertex link.  The target witness is
kept explicit, so this is precisely the local five-tetrahedron cluster
statement and makes no assertion about tetrahedra away from the center. -/
theorem Move41Site.targetPresent_fiveTetCluster_closes_vertexLink
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v : Nat}
    (hdegree : vertexDegree K v = 4)
    (hconnected : VertexLinkConnected K v)
    (s : Move41Site)
    (hse : s.e = v)
    (hsaturated : ∀ τ ∈ K.tets, s.e ∈ τ.verts →
      ∃ source ∈ s.sourceTets, SameTetVertices τ source)
    (htarget : ∃ τ ∈ K.tets, SameTetVertices τ s.targetTet) :
    (∃ τ ∈ K.tets, SameTetVertices τ s.targetTet) ∧
      ∀ σ ∈ vertexLinkTriangles K v,
        ∃ τ ∈ K.tets,
          τ.linkTriangleAt? v = some σ ∧
          ∃ source ∈ s.sourceTets, SameTetVertices τ source := by
  classical
  refine ⟨htarget, ?_⟩
  let C : LinkTriangle → Prop := fun σ ↦
    ∃ τ ∈ K.tets,
      τ.linkTriangleAt? v = some σ ∧
      ∃ source ∈ s.sourceTets, SameTetVertices τ source
  have hlength : (vertexLinkTriangles K v).length = 4 := by
    rw [vertexLinkTriangles_length_eq_vertexDegree K hcore v, hdegree]
  have hnonempty : (vertexLinkTriangles K v).length > 0 := by omega
  obtain ⟨σ₀, hσ₀⟩ := List.length_pos_iff_exists_mem.mp hnonempty
  have hC_of_mem : ∀ σ ∈ vertexLinkTriangles K v, C σ := by
    intro σ hσ
    obtain ⟨τ, hτK, hlink⟩ :=
      (mem_vertexLinkTriangles_iff K v σ).1 hσ
    have hvτ : v ∈ τ.verts :=
      (τ.linkTriangleAt?_isSome_iff v).1 (by rw [hlink]; rfl)
    obtain ⟨source, hsource, hsame⟩ :=
      hsaturated τ hτK (hse.symm ▸ hvτ)
    exact ⟨τ, hτK, hlink, source, hsource, hsame⟩
  have hC₀ : C σ₀ := hC_of_mem σ₀ hσ₀
  have hclosed : ∀ σ ρ,
      VertexLinkAdjacent K v σ ρ → C σ → C ρ := by
    intro σ ρ hadj _
    exact hC_of_mem ρ hadj.2.1
  exact hconnected.all_of_adjacent_closed C hσ₀ hC₀ hclosed

/-- At a degree-four vertex with connected link, either the constructed
`4 → 1` site is legal, or its represented opposite tetrahedron completes a
five-tetrahedron cluster whose four source tetrahedra fill the whole vertex
link. -/
theorem ClosedTriangulationCore.exists_move41Site_legalIn_or_targetPresent_closes_vertexLink
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hdegree : vertexDegree K v = 4)
    (hconnected : VertexLinkConnected K v) :
    ∃ s : Move41Site,
      s.e = v ∧
      (s.LegalIn K ∨
        ((∃ τ ∈ K.tets, SameTetVertices τ s.targetTet) ∧
          ∀ σ ∈ vertexLinkTriangles K v,
            ∃ τ ∈ K.tets,
              τ.linkTriangleAt? v = some σ ∧
              ∃ source ∈ s.sourceTets,
                SameTetVertices τ source)) := by
  classical
  obtain ⟨s, hse, hlabels⟩ :=
    hcore.exists_move41Site_labels_of_vertexDegree_eq_four v hdegree
  have hsources :=
    hcore.move41Site_sourcesExactlyOnce_of_vertexDegree_eq_four
      v hdegree s hse hlabels
  have hsaturated : ∀ τ ∈ K.tets, s.e ∈ τ.verts →
      ∃ source ∈ s.sourceTets, SameTetVertices τ source := by
    intro τ hτK he
    apply exists_move41_source_of_center_mem_of_outer_cover s τ
      (hcore.1 τ hτK) he
    intro x hxτ hxe
    obtain ⟨σ, hσ, hlink⟩ :=
      exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem K v τ hτK (hse ▸ he)
    have hxσ : x ∈ σ.verts :=
      (τ.mem_linkTriangleAt?_iff v x σ hlink
        (by simpa [hse] using hxe)).2 hxτ
    exact (hlabels x).1
      ((mem_vertexLinkVertices_iff K v x).2 ⟨σ, hσ, hxσ⟩)
  have hpairwise :
      s.sourceTets.Pairwise (fun τ σ => ¬ SameTetVertices τ σ) := by
    have hd := s.distinct
    simp [Move41Site.sourceTets, Move41Site.sourceTet₀, Move41Site.sourceTet₁,
      Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts] at hd ⊢
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · intro h
      have := (h s.c).1 (by simp [Move41Site.sourceTet₀, Tet.verts])
      simp [Move41Site.sourceTet₁, Tet.verts] at this
      aesop
    · intro h
      have := (h s.b).1 (by simp [Move41Site.sourceTet₀, Tet.verts])
      simp [Move41Site.sourceTet₂, Tet.verts] at this
      aesop
    · intro h
      have := (h s.a).1 (by simp [Move41Site.sourceTet₀, Tet.verts])
      simp [Move41Site.sourceTet₃, Tet.verts] at this
      aesop
    · intro h
      have := (h s.b).1 (by simp [Move41Site.sourceTet₁, Tet.verts])
      simp [Move41Site.sourceTet₂, Tet.verts] at this
      aesop
    · intro h
      have := (h s.a).1 (by simp [Move41Site.sourceTet₁, Tet.verts])
      simp [Move41Site.sourceTet₃, Tet.verts] at this
      aesop
    · intro h
      have := (h s.a).1 (by simp [Move41Site.sourceTet₂, Tet.verts])
      simp [Move41Site.sourceTet₃, Tet.verts] at this
      aesop
  refine ⟨s, hse, ?_⟩
  rcases s.legalIn_or_exists_target hcore hsources hpairwise hsaturated with
    hlegal | htarget
  · exact Or.inl hlegal
  · exact Or.inr
      (s.targetPresent_fiveTetCluster_closes_vertexLink
        hcore hdegree hconnected hse hsaturated htarget)

end Poincare
