import Poincare.PermutationCertifiedStellar

namespace Poincare

/-- A path of genuine Pachner steps with changes of tetrahedron-list order
allowed only at the endpoints of each certified step.  It does not identify
permutations with literal equality of Triangulation records. -/
inductive PermutationCertifiedPachnerPath : Triangulation → Triangulation → Prop where
  | refl (K : Triangulation) : PermutationCertifiedPachnerPath K K
  | snoc {K L M : Triangulation}
      (hpath : PermutationCertifiedPachnerPath K L)
      (hstep : PermutationCertifiedPachnerStep L M) :
      PermutationCertifiedPachnerPath K M

/-- Every step of the permutation-aware path has an actual topological
homeomorphism.  This is not an additional geometric assumption. -/
theorem PermutationCertifiedPachnerPath.homeomorphic
    {K L : Triangulation} (h : PermutationCertifiedPachnerPath K L) :
    Nonempty (triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier L) := by
  induction h with
  | refl => exact ⟨Homeomorph.refl _⟩
  | snoc hpath hstep ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨f⟩ := hstep.homeomorphic
      exact ⟨e.trans f⟩

/-- Once the two *actual* move sites are proved legal, and the endpoint list
has been proved to be a permutation of the intended target, the two-move
certificate is assembled without any geometric or global-descent axiom.

The local first/second legality and endpoint-permutation lemmas are separate
open obligations; this conditional result must not be cited as their proof. -/
theorem permutationCertifiedTwoMovePath_of_legal23_legal32
    (K L : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (s23 : Move23Site) (h23 : s23.LegalIn K)
    (s32 : Move32Site) (h32 : s32.LegalIn (s23.replace K))
    (hperm : (s32.replace (s23.replace K)).tets.Perm L.tets) :
    PermutationCertifiedPachnerPath K L := by
  have hcoreMid : ClosedTriangulationCore (s23.replace K) :=
    hcore.move23Site_replace_closedCore s23 h23
  apply PermutationCertifiedPachnerPath.snoc
  · apply PermutationCertifiedPachnerPath.snoc
    · exact PermutationCertifiedPachnerPath.refl K
    · exact ⟨K, s23.replace K, List.Perm.refl _,
        CertifiedPachnerStep.move23 hcore s23 h23, List.Perm.refl _⟩
  · exact ⟨s23.replace K, s32.replace (s23.replace K), List.Perm.refl _,
      CertifiedPachnerStep.move32 hcoreMid s32 h32, hperm⟩

end Poincare
