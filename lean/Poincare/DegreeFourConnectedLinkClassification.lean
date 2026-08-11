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

/-- Exact occurrence of every source vertex set supplies concrete represented
source tetrahedra.  This is the witness bridge used to define the
target-present five-tetrahedron cluster as a family of represented
tetrahedra. -/
theorem Move41Site.sources_represented_of_exactlyOnce
    {K : Triangulation}
    (s : Move41Site)
    (hsources : ∀ source ∈ s.sourceTets,
      (K.tets.filter (fun tau => sameTetVerticesBool tau source)).length = 1) :
    ∀ source ∈ s.sourceTets,
      ∃ tau ∈ K.tets, SameTetVertices tau source := by
  intro source hsource
  have hlength := hsources source hsource
  obtain ⟨tau, htau⟩ := List.length_pos_iff_exists_mem.mp (by omega :
    0 < (K.tets.filter
      (fun rho => sameTetVerticesBool rho source)).length)
  have htau' : tau ∈ K.tets ∧ sameTetVerticesBool tau source = true := by
    simpa using htau
  exact ⟨tau, htau'.1,
    (sameTetVerticesBool_eq_true_iff tau source).1 htau'.2⟩

/-- Exact source occurrence together with a represented target supplies the
five concrete represented tetrahedra of the target-present cluster. -/
theorem Move41Site.exists_represented_fiveTetCluster_of_targetPresent
    {K : Triangulation}
    (s : Move41Site)
    (hsources : ∀ source ∈ s.sourceTets,
      (K.tets.filter (fun tau => sameTetVerticesBool tau source)).length = 1)
    (htarget : ∃ tau ∈ K.tets, SameTetVertices tau s.targetTet) :
    ∃ tau₀ tau₁ tau₂ tau₃ target,
      tau₀ ∈ K.tets ∧ SameTetVertices tau₀ s.sourceTet₀ ∧
      tau₁ ∈ K.tets ∧ SameTetVertices tau₁ s.sourceTet₁ ∧
      tau₂ ∈ K.tets ∧ SameTetVertices tau₂ s.sourceTet₂ ∧
      tau₃ ∈ K.tets ∧ SameTetVertices tau₃ s.sourceTet₃ ∧
      target ∈ K.tets ∧ SameTetVertices target s.targetTet := by
  have hrepresented := s.sources_represented_of_exactlyOnce hsources
  obtain ⟨tau₀, htau₀K, htau₀⟩ :=
    hrepresented s.sourceTet₀ (by simp [Move41Site.sourceTets])
  obtain ⟨tau₁, htau₁K, htau₁⟩ :=
    hrepresented s.sourceTet₁ (by simp [Move41Site.sourceTets])
  obtain ⟨tau₂, htau₂K, htau₂⟩ :=
    hrepresented s.sourceTet₂ (by simp [Move41Site.sourceTets])
  obtain ⟨tau₃, htau₃K, htau₃⟩ :=
    hrepresented s.sourceTet₃ (by simp [Move41Site.sourceTets])
  obtain ⟨target, htargetK, htargetSame⟩ := htarget
  exact ⟨tau₀, tau₁, tau₂, tau₃, target,
    htau₀K, htau₀, htau₁K, htau₁, htau₂K, htau₂,
    htau₃K, htau₃, htargetK, htargetSame⟩

/-- The concrete tetrahedra representing the four sources and the opposite
target of a `4 → 1` site are pairwise distinct.  This is the exact finite
cluster certificate needed before closed-core face incidence can be used at
the four outer vertices. -/
theorem Move41Site.exists_represented_fiveTetCluster_nodup_of_targetPresent
    {K : Triangulation}
    (s : Move41Site)
    (hsources : ∀ source ∈ s.sourceTets,
      (K.tets.filter (fun tau => sameTetVerticesBool tau source)).length = 1)
    (htarget : ∃ tau ∈ K.tets, SameTetVertices tau s.targetTet) :
    ∃ tau₀ tau₁ tau₂ tau₃ target,
      tau₀ ∈ K.tets ∧ SameTetVertices tau₀ s.sourceTet₀ ∧
      tau₁ ∈ K.tets ∧ SameTetVertices tau₁ s.sourceTet₁ ∧
      tau₂ ∈ K.tets ∧ SameTetVertices tau₂ s.sourceTet₂ ∧
      tau₃ ∈ K.tets ∧ SameTetVertices tau₃ s.sourceTet₃ ∧
      target ∈ K.tets ∧ SameTetVertices target s.targetTet ∧
      [tau₀, tau₁, tau₂, tau₃, target].Nodup := by
  classical
  obtain ⟨tau₀, tau₁, tau₂, tau₃, target,
    htau₀K, htau₀, htau₁K, htau₁, htau₂K, htau₂,
    htau₃K, htau₃, htargetK, htargetSame⟩ :=
      s.exists_represented_fiveTetCluster_of_targetPresent hsources htarget
  have concrete_ne {alpha beta A B : Tet}
      (halpha : SameTetVertices alpha A)
      (hbeta : SameTetVertices beta B)
      (hne : ¬ SameTetVertices A B) : alpha ≠ beta := by
    intro hab
    apply hne
    intro v
    exact (halpha v).symm.trans (hab ▸ hbeta v)
  have model_ne (A B : Tet) (v : Nat)
      (hvA : v ∈ A.verts) (hvB : v ∉ B.verts) :
      ¬ SameTetVertices A B := by
    intro h
    exact hvB ((h v).1 hvA)
  have hd := s.distinct
  simp at hd
  rcases hd with
    ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩
  have hba := Ne.symm hab
  have hca := Ne.symm hac
  have hda := Ne.symm had
  have hea := Ne.symm hae
  have hcb := Ne.symm hbc
  have hdb := Ne.symm hbd
  have heb := Ne.symm hbe
  have hdc := Ne.symm hcd
  have hec := Ne.symm hce
  have hed := Ne.symm hde
  have h01 : ¬ SameTetVertices s.sourceTet₀ s.sourceTet₁ :=
    model_ne _ _ s.c (by simp [Move41Site.sourceTet₀, Tet.verts])
      (by simp [Move41Site.sourceTet₁, Tet.verts, hca, hcb, hcd, hce])
  have h02 : ¬ SameTetVertices s.sourceTet₀ s.sourceTet₂ :=
    model_ne _ _ s.b (by simp [Move41Site.sourceTet₀, Tet.verts])
      (by simp [Move41Site.sourceTet₂, Tet.verts, hba, hbc, hbd, hbe])
  have h03 : ¬ SameTetVertices s.sourceTet₀ s.sourceTet₃ :=
    model_ne _ _ s.a (by simp [Move41Site.sourceTet₀, Tet.verts])
      (by simp [Move41Site.sourceTet₃, Tet.verts, hab, hac, had, hae])
  have h0t : ¬ SameTetVertices s.sourceTet₀ s.targetTet :=
    model_ne _ _ s.e (by simp [Move41Site.sourceTet₀, Tet.verts])
      (by simp [Move41Site.targetTet, Tet.verts, hea, heb, hec, hed])
  have h12 : ¬ SameTetVertices s.sourceTet₁ s.sourceTet₂ :=
    model_ne _ _ s.b (by simp [Move41Site.sourceTet₁, Tet.verts])
      (by simp [Move41Site.sourceTet₂, Tet.verts, hba, hbc, hbd, hbe])
  have h13 : ¬ SameTetVertices s.sourceTet₁ s.sourceTet₃ :=
    model_ne _ _ s.a (by simp [Move41Site.sourceTet₁, Tet.verts])
      (by simp [Move41Site.sourceTet₃, Tet.verts, hab, hac, had, hae])
  have h1t : ¬ SameTetVertices s.sourceTet₁ s.targetTet :=
    model_ne _ _ s.e (by simp [Move41Site.sourceTet₁, Tet.verts])
      (by simp [Move41Site.targetTet, Tet.verts, hea, heb, hec, hed])
  have h23 : ¬ SameTetVertices s.sourceTet₂ s.sourceTet₃ :=
    model_ne _ _ s.a (by simp [Move41Site.sourceTet₂, Tet.verts])
      (by simp [Move41Site.sourceTet₃, Tet.verts, hab, hac, had, hae])
  have h2t : ¬ SameTetVertices s.sourceTet₂ s.targetTet :=
    model_ne _ _ s.e (by simp [Move41Site.sourceTet₂, Tet.verts])
      (by simp [Move41Site.targetTet, Tet.verts, hea, heb, hec, hed])
  have h3t : ¬ SameTetVertices s.sourceTet₃ s.targetTet :=
    model_ne _ _ s.e (by simp [Move41Site.sourceTet₃, Tet.verts])
      (by simp [Move41Site.targetTet, Tet.verts, hea, heb, hec, hed])
  have htau01 := concrete_ne htau₀ htau₁ h01
  have htau02 := concrete_ne htau₀ htau₂ h02
  have htau03 := concrete_ne htau₀ htau₃ h03
  have htau0t := concrete_ne htau₀ htargetSame h0t
  have htau12 := concrete_ne htau₁ htau₂ h12
  have htau13 := concrete_ne htau₁ htau₃ h13
  have htau1t := concrete_ne htau₁ htargetSame h1t
  have htau23 := concrete_ne htau₂ htau₃ h23
  have htau2t := concrete_ne htau₂ htargetSame h2t
  have htau3t := concrete_ne htau₃ htargetSame h3t
  exact ⟨tau₀, tau₁, tau₂, tau₃, target,
    htau₀K, htau₀, htau₁K, htau₁, htau₂K, htau₂,
    htau₃K, htau₃, htargetK, htargetSame,
    by simp [htau01, htau02, htau03, htau0t, htau12, htau13,
      htau1t, htau23, htau2t, htau3t]⟩

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
