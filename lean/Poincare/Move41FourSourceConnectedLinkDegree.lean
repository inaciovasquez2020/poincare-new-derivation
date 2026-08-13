import Poincare.Move41FourSourceCenterDegree
import Poincare.Move41FourSourceCenterSaturation

namespace Poincare

theorem ClosedTriangulationCore.move41Site_center_vertexDegree_eq_four_of_represented_sources_connectedLink
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (m : Move41Site)
    {tau₀ tau₁ tau₂ tau₃ : Tet}
    (htau₀K : tau₀ ∈ K.tets)
    (htau₀ : SameTetVertices tau₀ m.sourceTet₀)
    (htau₁K : tau₁ ∈ K.tets)
    (htau₁ : SameTetVertices tau₁ m.sourceTet₁)
    (htau₂K : tau₂ ∈ K.tets)
    (htau₂ : SameTetVertices tau₂ m.sourceTet₂)
    (htau₃K : tau₃ ∈ K.tets)
    (htau₃ : SameTetVertices tau₃ m.sourceTet₃)
    (hconnected : VertexLinkConnected K m.e) :
    vertexDegree K m.e = 4 := by
  classical
  have hpairwise :
      m.sourceTets.Pairwise (fun tau sigma => ¬ SameTetVertices tau sigma) := by
    have hd := m.distinct
    simp [Move41Site.sourceTets, Move41Site.sourceTet₀, Move41Site.sourceTet₁,
      Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts] at hd ⊢
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · intro h
      have hx := (h m.c).1 (by simp [Move41Site.sourceTet₀, Tet.verts])
      simp [Move41Site.sourceTet₁, Tet.verts] at hx
      aesop
    · intro h
      have hx := (h m.b).1 (by simp [Move41Site.sourceTet₀, Tet.verts])
      simp [Move41Site.sourceTet₂, Tet.verts] at hx
      aesop
    · intro h
      have hx := (h m.a).1 (by simp [Move41Site.sourceTet₀, Tet.verts])
      simp [Move41Site.sourceTet₃, Tet.verts] at hx
      aesop
    · intro h
      have hx := (h m.b).1 (by simp [Move41Site.sourceTet₁, Tet.verts])
      simp [Move41Site.sourceTet₂, Tet.verts] at hx
      aesop
    · intro h
      have hx := (h m.a).1 (by simp [Move41Site.sourceTet₁, Tet.verts])
      simp [Move41Site.sourceTet₃, Tet.verts] at hx
      aesop
    · intro h
      have hx := (h m.a).1 (by simp [Move41Site.sourceTet₂, Tet.verts])
      simp [Move41Site.sourceTet₃, Tet.verts] at hx
      aesop

  have hsourcePair := hpairwise
  simp [Move41Site.sourceTets] at hsourcePair
  have hne {x y u v : Tet}
      (hxy : ¬ SameTetVertices x y)
      (hu : SameTetVertices u x) (hv : SameTetVertices v y) : u ≠ v := by
    intro huv
    subst v
    exact hxy (sameTetVertices_trans (sameTetVertices_symm hu) hv)
  have hnodup : [tau₀, tau₁, tau₂, tau₃].Nodup := by
    simp [hne hsourcePair.1.1 htau₀ htau₁,
      hne hsourcePair.1.2.1 htau₀ htau₂,
      hne hsourcePair.1.2.2 htau₀ htau₃,
      hne hsourcePair.2.1.1 htau₁ htau₂,
      hne hsourcePair.2.1.2 htau₁ htau₃,
      hne hsourcePair.2.2 htau₂ htau₃]

  have hsaturated :=
    m.represented_sourceCluster_saturates_center_of_connectedLink
      hcore htau₀K htau₀ htau₁K htau₁ htau₂K htau₂ htau₃K htau₃
      hnodup hconnected

  have exactOnce (source tau : Tet) (htauK : tau ∈ K.tets)
      (hsame : SameTetVertices tau source) :
      (K.tets.filter (fun rho => sameTetVerticesBool rho source)).length = 1 := by
      have hunique := hcore.existsUnique_sameTetVertices ⟨tau, htauK, hsame⟩
      let L := K.tets.filter (fun rho => sameTetVerticesBool rho source)
      have htauL : tau ∈ L := by
        simp [L, htauK, sameTetVerticesBool_eq_true_iff, hsame]
      have hmem : ∀ rho, rho ∈ L ↔ rho = tau := by
        intro rho
        constructor
        · intro hrho
          have hrho' := (by
            simpa [L, sameTetVerticesBool_eq_true_iff] using hrho :
              rho ∈ K.tets ∧ SameTetVertices rho source)
          exact hunique.unique hrho' ⟨htauK, hsame⟩
        · rintro rfl
          exact htauL
      have hfinset : L.toFinset = {tau} := by
        ext rho
        simp [hmem]
      have hnodupK : K.tets.Nodup := by
        rw [List.nodup_iff_pairwise_ne]
        exact hcore.2.1.imp (fun {x y} hxy heq => by
          subst y
          exact hxy (sameTetVertices_refl x))
      have hnodupL : L.Nodup := hnodupK.filter _
      change L.length = 1
      rw [← List.toFinset_card_of_nodup hnodupL, hfinset]
      simp

  have hsourcesExact :
      ∀ source ∈ m.sourceTets,
        (K.tets.filter (fun tau => sameTetVerticesBool tau source)).length = 1 := by
    intro source hsource
    simp [Move41Site.sourceTets] at hsource
    rcases hsource with rfl | rfl | rfl | rfl
    · exact exactOnce m.sourceTet₀ tau₀ htau₀K htau₀
    · exact exactOnce m.sourceTet₁ tau₁ htau₁K htau₁
    · exact exactOnce m.sourceTet₂ tau₂ htau₂K htau₂
    · exact exactOnce m.sourceTet₃ tau₃ htau₃K htau₃

  exact hcore.move41Site_center_vertexDegree_eq_four_of_local_star
    m hsourcesExact hpairwise hsaturated

end Poincare
