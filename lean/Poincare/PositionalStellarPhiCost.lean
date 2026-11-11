import Poincare.PermutationCertifiedStellar
import Poincare.HeadStellarSimpleCore
import Poincare.PhiSupportEulerCount
import Mathlib.Tactic

namespace Poincare

private theorem support_mem_iff_of_tets_perm
    {K L : Triangulation} (hperm : K.tets.Perm L.tets) (v : Nat) :
    v ∈ vertexSupport K ↔ v ∈ vertexSupport L := by
  rw [mem_vertexSupport_iff, mem_vertexSupport_iff]
  change v ∈ K.tets.flatMap Tet.verts ↔
    v ∈ L.tets.flatMap Tet.verts
  constructor
  · intro hv
    obtain ⟨τ, hτ, hverts⟩ := List.mem_flatMap.mp hv
    exact List.mem_flatMap.mpr ⟨τ, (hperm.mem_iff).mp hτ, hverts⟩
  · intro hv
    obtain ⟨τ, hτ, hverts⟩ := List.mem_flatMap.mp hv
    exact List.mem_flatMap.mpr ⟨τ, (hperm.mem_iff).mpr hτ, hverts⟩

/-- A fresh 1→4 at any ordered tetrahedron position adds precisely its center
to the supported vertex set; this uses literal position-preserving insertion. -/
theorem Move41Site.insertFreshAt_vertexSupport_iff
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hfresh : s.e ∉ vertexSupport K) (v : Nat) :
    v ∈ vertexSupport (s.insertFreshAt K before after hsource hfresh) ↔
      v = s.e ∨ v ∈ vertexSupport K := by
  have hsourcePerm : K.tets.Perm (s.targetTet :: (before ++ after)) := by
    rw [hsource]
    exact List.perm_middle
  have htargetPerm :
      (s.insertFreshAt K before after hsource hfresh).tets.Perm
        (s.headStellar (before ++ after)).tets := by
    change (before ++ s.sourceTets ++ after).Perm
      (s.sourceTets ++ (before ++ after))
    simpa [List.append_assoc] using
      (List.perm_append_comm_assoc before s.sourceTets after)
  rw [support_mem_iff_of_tets_perm htargetPerm v,
    s.headStellar_vertexSupport_iff (before ++ after) v]
  exact or_congr Iff.rfl
    (support_mem_iff_of_tets_perm hsourcePerm v).symm

/-- An arbitrary-position fresh 1→4 creates exactly one new supported vertex. -/
theorem Move41Site.insertFreshAt_vertexSupport_length
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hfresh : s.e ∉ vertexSupport K) :
    (vertexSupport (s.insertFreshAt K before after hsource hfresh)).length =
      (vertexSupport K).length + 1 := by
  let T := s.insertFreshAt K before after hsource hfresh
  have hfin : (vertexSupport T).toFinset =
      insert s.e (vertexSupport K).toFinset := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_insert]
    exact s.insertFreshAt_vertexSupport_iff K before after hsource hfresh v
  have hnot : s.e ∉ (vertexSupport K).toFinset := by
    simpa using hfresh
  have hnT : (vertexSupport T).Nodup := by
    unfold vertexSupport
    exact eraseDups_nodup_nat (allVerts T)
  have hnK : (vertexSupport K).Nodup := by
    unfold vertexSupport
    exact eraseDups_nodup_nat (allVerts K)
  have hcT : (vertexSupport T).toFinset.card =
      (vertexSupport T).length :=
    List.toFinset_card_of_nodup hnT
  have hcK : (vertexSupport K).toFinset.card =
      (vertexSupport K).length :=
    List.toFinset_card_of_nodup hnK
  rw [← hcT, hfin, Finset.card_insert_of_not_mem hnot, hcK]

/-- A fresh 1→4 increases the tetrahedron-list length by three. -/
theorem Move41Site.insertFreshAt_tets_length
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hfresh : s.e ∉ vertexSupport K) :
    (s.insertFreshAt K before after hsource hfresh).tets.length =
      K.tets.length + 3 := by
  change (before ++ s.sourceTets ++ after).length = K.tets.length + 3
  rw [hsource]
  simp [Move41Site.sourceTets, List.length_append]
  omega

/-- Exact stabilization cost for the repository's PhiSupport functional:
a legal fresh positional 1→4 increases the defect by eight. Hence insertion
alone never produces strict PhiSupport descent. -/
theorem Move41Site.insertFreshAt_PhiSupport_eq_add_eight
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hcore : ClosedTriangulationCore K)
    (hfresh : s.e ∉ vertexSupport K) :
    PhiSupport (s.insertFreshAt K before after hsource hfresh) =
      PhiSupport K + 8 := by
  have htets := s.insertFreshAt_tets_length K before after hsource hfresh
  have hverts := s.insertFreshAt_vertexSupport_length K before after hsource hfresh
  have hK := hcore.PhiSupport_eq_four_mul_tets_sub_vertices
  have hT := (s.insertFreshAt_closedCore K before after hsource hcore hfresh).
    PhiSupport_eq_four_mul_tets_sub_vertices
  omega

end Poincare
