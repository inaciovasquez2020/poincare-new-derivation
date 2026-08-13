import Poincare.GlobalDegreeFourTargetPresentSaturation
import Poincare.DegreeFourVertexLinkClassification

namespace Poincare

/--
A degree-four vertex in a closed triangulation core, under connected
represented vertex links and tetrahedron vertex-overlap connectivity,
has exactly the global fork needed by the F0 descent program:

* either its canonical degree-four site is a genuine legal `4 → 1` move; or
* the target tetrahedron is represented and the resulting five-tetrahedron
  boundary cluster exhausts every represented tetrahedron of `K`.

This theorem makes no strict-Phi claim in the legal branch.
-/
theorem
    ClosedTriangulationCore.exists_move41Site_legalIn_or_globalFiveTetCluster_of_vertexDegree_eq_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (v : Nat)
    (hdegree : vertexDegree K v = 4) :
    ∃ s : Move41Site,
      s.e = v ∧
      (s.LegalIn K ∨
        ∃ tau₀ tau₁ tau₂ tau₃ target,
          tau₀ ∈ K.tets ∧
          SameTetVertices tau₀ s.sourceTet₀ ∧
          tau₁ ∈ K.tets ∧
          SameTetVertices tau₁ s.sourceTet₁ ∧
          tau₂ ∈ K.tets ∧
          SameTetVertices tau₂ s.sourceTet₂ ∧
          tau₃ ∈ K.tets ∧
          SameTetVertices tau₃ s.sourceTet₃ ∧
          target ∈ K.tets ∧
          SameTetVertices target s.targetTet ∧
          [tau₀, tau₁, tau₂, tau₃, target].Nodup ∧
          ∀ rho ∈ K.tets,
            rho = tau₀ ∨
            rho = tau₁ ∨
            rho = tau₂ ∨
            rho = tau₃ ∨
            rho = target) := by
  classical

  obtain ⟨s, hse, hlabels⟩ :=
    hcore.exists_move41Site_labels_of_vertexDegree_eq_four
      v hdegree

  have hsources :
      ∀ source ∈ s.sourceTets,
        (K.tets.filter
          (fun tau => sameTetVerticesBool tau source)).length = 1 :=
    hcore.move41Site_sourcesExactlyOnce_of_vertexDegree_eq_four
      v hdegree s hse hlabels

  have hsaturated :
      ∀ tau ∈ K.tets,
        s.e ∈ tau.verts →
          ∃ source ∈ s.sourceTets,
            SameTetVertices tau source := by
    intro tau htauK he
    apply exists_move41_source_of_center_mem_of_outer_cover
      s tau (hcore.1 tau htauK) he
    intro x hxtau hxe
    obtain ⟨sigma, hsigma, hlink⟩ :=
      exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
        K v tau htauK (hse ▸ he)
    have hxsigma : x ∈ sigma.verts :=
      (tau.mem_linkTriangleAt?_iff
        v x sigma hlink
        (by simpa [hse] using hxe)).2 hxtau
    exact (hlabels x).1
      ((mem_vertexLinkVertices_iff K v x).2
        ⟨sigma, hsigma, hxsigma⟩)

  have hpairwise :
      s.sourceTets.Pairwise
        (fun tau sigma => ¬ SameTetVertices tau sigma) := by
    have hd := s.distinct
    simp [Move41Site.sourceTets,
      Move41Site.sourceTet₀,
      Move41Site.sourceTet₁,
      Move41Site.sourceTet₂,
      Move41Site.sourceTet₃,
      Tet.verts] at hd ⊢
    refine
      ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · intro h
      have hx :=
        (h s.c).1
          (by simp [Move41Site.sourceTet₀, Tet.verts])
      simp [Move41Site.sourceTet₁, Tet.verts] at hx
      aesop
    · intro h
      have hx :=
        (h s.b).1
          (by simp [Move41Site.sourceTet₀, Tet.verts])
      simp [Move41Site.sourceTet₂, Tet.verts] at hx
      aesop
    · intro h
      have hx :=
        (h s.a).1
          (by simp [Move41Site.sourceTet₀, Tet.verts])
      simp [Move41Site.sourceTet₃, Tet.verts] at hx
      aesop
    · intro h
      have hx :=
        (h s.b).1
          (by simp [Move41Site.sourceTet₁, Tet.verts])
      simp [Move41Site.sourceTet₂, Tet.verts] at hx
      aesop
    · intro h
      have hx :=
        (h s.a).1
          (by simp [Move41Site.sourceTet₁, Tet.verts])
      simp [Move41Site.sourceTet₃, Tet.verts] at hx
      aesop
    · intro h
      have hx :=
        (h s.a).1
          (by simp [Move41Site.sourceTet₂, Tet.verts])
      simp [Move41Site.sourceTet₃, Tet.verts] at hx
      aesop

  refine ⟨s, hse, ?_⟩

  rcases
      Move41Site.legalIn_or_exists_target
        hcore s hsources hpairwise hsaturated with
    hlegal | htarget

  · exact Or.inl hlegal

  · right

    obtain
      ⟨tau₀, tau₁, tau₂, tau₃, target,
        htau₀K, htau₀,
        htau₁K, htau₁,
        htau₂K, htau₂,
        htau₃K, htau₃,
        htargetK, htargetMatch,
        hnodup⟩ :=
      Move41Site.exists_represented_fiveTetCluster_nodup_of_targetPresent
        s hsources htarget

    refine
      ⟨tau₀, tau₁, tau₂, tau₃, target,
        htau₀K, htau₀,
        htau₁K, htau₁,
        htau₂K, htau₂,
        htau₃K, htau₃,
        htargetK, htargetMatch,
        hnodup, ?_⟩

    let C : Tet → Prop :=
      fun rho =>
        rho = tau₀ ∨
        rho = tau₁ ∨
        rho = tau₂ ∨
        rho = tau₃ ∨
        rho = target

    have hseed :
        ∃ tau ∈ K.tets, C tau := by
      exact ⟨tau₀, htau₀K, Or.inl rfl⟩

    have hstar :
        ∀ x,
          ∀ alpha ∈ K.tets,
            C alpha →
            x ∈ alpha.verts →
            ∀ beta ∈ K.tets,
              x ∈ beta.verts →
              C beta := by
      intro x alpha halphaK halphaC hxalpha
        beta hbetaK hxbeta
      exact
        Move41Site.represented_fiveTetCluster_vertexStarClosed_of_connectedLinks
          hcore hlinks s
          htau₀K htau₀
          htau₁K htau₁
          htau₂K htau₂
          htau₃K htau₃
          htargetK htargetMatch
          hnodup
          alpha
          halphaK
          halphaC
          x
          hxalpha
          beta
          hbetaK
          hxbeta

    intro rho hrhoK
    exact
      Move41Site.targetPresent_fiveTetCluster_global_of_vertexStarClosed
        hconn s C hseed hstar rho hrhoK

end Poincare
