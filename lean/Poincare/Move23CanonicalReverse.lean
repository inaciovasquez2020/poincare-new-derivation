import Poincare.Move23GeometricCarrierHomeomorph

open Set

namespace Poincare

set_option maxHeartbeats 800000

/-- The canonical two-tetrahedron predecessor associated to a `2-3` site. -/
def Move23Site.canonicalPredecessor
    (s : Move23Site) (K : Triangulation) : Triangulation :=
  { tets := s.leftTet :: s.rightTet :: s.unchangedTets K }

/-- Concrete canonical `3-2` reversal: erase the three target tetrahedra and
insert the two source tetrahedra. -/
def Move23Site.reverseReplace
    (s : Move23Site) (L : Triangulation) : Triangulation :=
  let after0 := eraseFirstSameTet s.newTet₀ L.tets
  let after1 := eraseFirstSameTet s.newTet₁ after0
  let after2 := eraseFirstSameTet s.newTet₂ after1
  { tets := s.leftTet :: s.rightTet :: after2 }

theorem Move23Site.reverseReplace_replace_eq_canonicalPredecessor
    (s : Move23Site) (K : Triangulation) :
    s.reverseReplace (s.replace K) = s.canonicalPredecessor K := by
  simp [Move23Site.reverseReplace, Move23Site.canonicalPredecessor,
    Move23Site.replace, Move23Site.unchangedTets, eraseFirstSameTet, sameTetVerticesBool,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts]

theorem Move23Site.canonicalPredecessor_geometricComplex_space_eq
    (s : Move23Site) (K : Triangulation) :
    (triangulationTopologicalGeometricComplex
      (s.canonicalPredecessor K)).space =
      move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ∪
        s.unchangedGeometricCarrier K := by
  rw [move23PiSourceLocalCarrier, ← s.leftTet_tetBody, ← s.rightTet_tetBody]
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  ext p
  simp [Move23Site.canonicalPredecessor, Move23Site.unchangedGeometricCarrier,
    triangulationTopologicalTetBody]
  aesop

theorem Move23Site.canonicalPredecessor_space_eq_original
    {K : Triangulation} (s : Move23Site) (hrealized : s.RealizedIn K) :
    (triangulationTopologicalGeometricComplex
      (s.canonicalPredecessor K)).space =
    (triangulationTopologicalGeometricComplex K).space := by
  rw [s.canonicalPredecessor_geometricComplex_space_eq K,
    s.geometricComplex_space_eq_source_union_unchanged hrealized]

noncomputable def Move23Site.canonicalPredecessorHomeomorphOriginal
    {K : Triangulation} (s : Move23Site) (hrealized : s.RealizedIn K) :
    triangulationTopologicalGeometricCarrier (s.canonicalPredecessor K) ≃ₜ
      triangulationTopologicalGeometricCarrier K :=
  Homeomorph.setCongr (s.canonicalPredecessor_space_eq_original hrealized)

@[simp] theorem Move23Site.canonicalPredecessorHomeomorphOriginal_apply
    {K : Triangulation} (s : Move23Site) (hrealized : s.RealizedIn K)
    (p : triangulationTopologicalGeometricCarrier (s.canonicalPredecessor K)) :
    (s.canonicalPredecessorHomeomorphOriginal hrealized p).1 = p.1 := by
  rfl

@[simp] theorem Move23Site.canonicalPredecessorHomeomorphOriginal_symm_apply
    {K : Triangulation} (s : Move23Site) (hrealized : s.RealizedIn K)
    (p : triangulationTopologicalGeometricCarrier K) :
    ((s.canonicalPredecessorHomeomorphOriginal hrealized).symm p).1 = p.1 := by
  rfl

theorem Move23Site.reverseReplace_replace_space_eq_original
    {K : Triangulation} (s : Move23Site) (hrealized : s.RealizedIn K) :
    (triangulationTopologicalGeometricComplex
      (s.reverseReplace (s.replace K))).space =
    (triangulationTopologicalGeometricComplex K).space := by
  rw [s.reverseReplace_replace_eq_canonicalPredecessor K]
  exact s.canonicalPredecessor_space_eq_original hrealized

noncomputable def
    ClosedTriangulationCore.move23ReverseGeometricCarrierHomeomorph
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    triangulationTopologicalGeometricCarrier (s.replace K) ≃ₜ
      triangulationTopologicalGeometricCarrier
        (s.reverseReplace (s.replace K)) := by
  exact (hcore.move23GeometricCarrierHomeomorph s hlegal).symm.trans
    (Homeomorph.setCongr
      (s.reverseReplace_replace_space_eq_original hlegal.1).symm)

theorem ClosedTriangulationCore.move23ReverseGeometricCarrierHomeomorph_apply
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K)
    (q : triangulationTopologicalGeometricCarrier (s.replace K)) :
    (hcore.move23ReverseGeometricCarrierHomeomorph s hlegal q).1 =
      ((hcore.move23GeometricCarrierHomeomorph s hlegal).symm q).1 := by
  rfl

theorem ClosedTriangulationCore.move23ReverseGeometricCarrierHomeomorph_apply_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K)
    (q : triangulationTopologicalGeometricCarrier (s.replace K))
    (hqU : q.1 ∈ s.unchangedGeometricCarrier K) :
    (hcore.move23ReverseGeometricCarrierHomeomorph s hlegal q).1 = q.1 := by
  rw [hcore.move23ReverseGeometricCarrierHomeomorph_apply s hlegal q]
  exact hcore.move23GeometricCarrierHomeomorph_symm_apply_eq_self_of_mem_unchanged
    s hlegal q hqU

end Poincare
