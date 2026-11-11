import Poincare.TriangulationTopologicalGeometricCarrier
import Mathlib.Topology.Homeomorph

namespace Poincare

/-- Reordering the tetrahedron records does not alter the actual
Pi-space geometric realization, since its constituent faces are selected
by membership rather than by list position. -/
theorem triangulationTopologicalGeometricComplex_space_eq_of_perm
    {K L : Triangulation} (hperm : K.tets.Perm L.tets) :
    (triangulationTopologicalGeometricComplex K).space =
      (triangulationTopologicalGeometricComplex L).space := by
  ext x
  rw [mem_triangulationTopologicalGeometricCarrier_iff,
    mem_triangulationTopologicalGeometricCarrier_iff]
  constructor
  · rintro ⟨F, hF, ⟨τ, hτ, hsub⟩, hx⟩
    exact ⟨F, hF, ⟨τ, (hperm.mem_iff).mp hτ, hsub⟩, hx⟩
  · rintro ⟨F, hF, ⟨τ, hτ, hsub⟩, hx⟩
    exact ⟨F, hF, ⟨τ, (hperm.mem_iff).mpr hτ, hsub⟩, hx⟩

/-- Any permutation of the tetrahedron list induces a genuine
homeomorphism of the topology-bearing geometric carrier.
No closed-core assumptions or move-site legality are needed. -/
noncomputable def triangulationTopologicalGeometricCarrier_homeomorph_of_perm
    {K L : Triangulation} (hperm : K.tets.Perm L.tets) :
    triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier L := by
  have hspace := triangulationTopologicalGeometricComplex_space_eq_of_perm hperm
  simp only [triangulationTopologicalGeometricCarrier, hspace]
  exact Homeomorph.refl _

end Poincare
