/-!
Append after G2ClosedPrimalWalkCandidate.lean in the existing temporary
G2 piecewise-loop compilation, with the extra import
  import Poincare.TriangulationTopologicalManifoldVertexLinkSimplyConnectedness
in the initial import block.
Pinned PR #200 head: 0abea229aac60357bf49520b98ba8f244bd78fc4.
NOT_RUN. This is a candidate, not a kernel certificate.
The padded records encode triangle supports only. No closed-core,
nondegeneracy, manifold or Pachner claim is made for the auxiliary record list.
-/

namespace Poincare

private def g2LinkPaddedTet (s : LinkTriangle) : Tet :=
  ⟨s.v0, s.v1, s.v2, s.v2⟩

private def g2LinkSupportCarrier (K : Triangulation) (v : Nat) : Triangulation :=
  ⟨(vertexLinkTriangles K v).map g2LinkPaddedTet⟩

private theorem g2LinkPaddedTet_mem (s : LinkTriangle) (x : Nat) :
    x ∈ (g2LinkPaddedTet s).verts ↔ x ∈ s.verts := by
  simp [g2LinkPaddedTet, Tet.verts, LinkTriangle.verts]

private theorem g2LinkPaddedTet_support (s : LinkTriangle) :
    (g2LinkPaddedTet s).verts.toFinset = s.verts.toFinset := by
  ext x
  simpa only [List.mem_toFinset] using g2LinkPaddedTet_mem s x

/-- The auxiliary carrier is literally the original vertex-link subset of
Pi-space, not a thickening or a new geometric construction. -/
private theorem g2LinkSupportCarrier_space (K : Triangulation) (v : Nat) :
    (triangulationTopologicalGeometricComplex (g2LinkSupportCarrier K v)).space =
      triangulationTopologicalVertexLink K v := by
  classical
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  ext p
  simp only [Set.mem_iUnion]
  rw [mem_triangulationTopologicalVertexLink_iff]
  constructor
  · rintro ⟨tau, htau, hp⟩
    change tau ∈ (vertexLinkTriangles K v).map g2LinkPaddedTet at htau
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp htau
    refine ⟨s, hs, ?_⟩
    simpa only [triangulationTopologicalTetBody, g2LinkPaddedTet_support] using hp
  · rintro ⟨s, hs, hp⟩
    refine ⟨g2LinkPaddedTet s, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨s, hs, rfl⟩
    · simpa only [triangulationTopologicalTetBody, g2LinkPaddedTet_support] using hp

/-- Transport the already verified closed-primal-walk cancellation theorem
to the actual geometric vertex link, without a second grid proof. -/
theorem g2_vertex_link_closed_walk_pairing_zero_candidate
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v : Nat} (hv : v ∈ vertexSupport K)
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ a, w a a = 0)
    (hsym : ∀ a b, w a b = w b a)
    (htri : ∀ s : LinkTriangle, s ∈ vertexLinkTriangles K v →
      ∀ a b c : Nat, a ∈ s.verts → b ∈ s.verts → c ∈ s.verts →
      w a b + w b c + w c a = 0)
    (m : Nat) (hm : 0 < m) (vertex : Nat → Nat)
    (hclosed : vertex m = vertex 0)
    (hdistinct : ∀ k, k < m → vertex k ≠ vertex (k+1))
    (hstep : ∀ k, k < m → ∃ s : LinkTriangle,
      s ∈ vertexLinkTriangles K v ∧ vertex k ∈ s.verts ∧
      vertex (k+1) ∈ s.verts) :
    (∑ k ∈ Finset.range m, w (vertex k) (vertex (k+1))) = 0 := by
  have hSC : TriangulationRealizationSimplyConnected (g2LinkSupportCarrier K v) := by
    rw [triangulationRealizationSimplyConnected_iff_isSimplyConnected_space,
      g2LinkSupportCarrier_space]
    exact triangulationTopologicalVertexLink_simplyConnected_of_topologicalThreeManifold
      K hcore hM hv
  refine g2_closed_primal_walk_pairing_zero_candidate
    hSC w hzero hsym ?_ m hm vertex hclosed hdistinct ?_
  · intro tau htau a b c ha hb hc
    change tau ∈ (vertexLinkTriangles K v).map g2LinkPaddedTet at htau
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp htau
    exact htri s hs a b c ((g2LinkPaddedTet_mem s a).1 ha)
      ((g2LinkPaddedTet_mem s b).1 hb) ((g2LinkPaddedTet_mem s c).1 hc)
  · intro k hk
    obtain ⟨s, hs, ha, hb⟩ := hstep k hk
    exact ⟨g2LinkPaddedTet s, List.mem_map.mpr ⟨s, hs, rfl⟩,
      (g2LinkPaddedTet_mem s (vertex k)).2 ha,
      (g2LinkPaddedTet_mem s (vertex (k+1))).2 hb⟩

#print axioms g2LinkSupportCarrier_space
#print axioms g2_vertex_link_closed_walk_pairing_zero_candidate

end Poincare
