import Poincare.GlobalFanChordMove2332SecondStep

namespace Poincare

/-- A legal `2-3` followed by any legal `3-2` returns `PhiSupport` exactly to
its starting value.  This is the prefix balance needed to transfer any later
strict descent found while resolving the second source-face obstruction back
to the original triangulation. -/
theorem move2332Prefix_PhiSupport_eq
    {K0 : Triangulation}
    (hcore0 : ClosedTriangulationCore K0)
    (m23 : Move23Site)
    (h23 : m23.LegalIn K0)
    (m32 : Move32Site)
    (h32 : m32.LegalIn (m23.replace K0)) :
    PhiSupport (m32.replace (m23.replace K0)) = PhiSupport K0 := by
  have hcore1 : ClosedTriangulationCore (m23.replace K0) :=
    hcore0.move23Site_replace_closedCore m23 h23
  have hcore2 : ClosedTriangulationCore (m32.replace (m23.replace K0)) :=
    hcore1.move32Site_replace_closedCore m32 h32

  have h23realized : m23.RealizedIn K0 := h23.1
  rcases h23realized with
    ⟨⟨tauD, htauD, htauDMatch⟩, ⟨tauE, htauE, htauEMatch⟩⟩

  have hd0Support : m23.d ∈ vertexSupport K0 := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tauD, htauD, (htauDMatch m23.d).2 (by
      simp [Move23Site.leftTet, Tet.verts])⟩

  have he0Support : m23.e ∈ vertexSupport K0 := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tauE, htauE, (htauEMatch m23.e).2 (by
      simp [Move23Site.rightTet, Tet.verts])⟩

  have hd0 : 4 ≤ vertexDegree K0 m23.d :=
    hcore0.vertexDegree_ge_four_of_mem_vertexSupport hd0Support
  have he0 : 4 ≤ vertexDegree K0 m23.e :=
    hcore0.vertexDegree_ge_four_of_mem_vertexSupport he0Support

  rcases m23.replace_vertexDegree_site K0 h23 with
    ⟨_, _, _, hd23, he23⟩

  have hdDef23 :
      vertexDefect (m23.replace K0) m23.d =
        vertexDefect K0 m23.d + 2 :=
    (vertexDefect_of_degree_add_two
      K0 (m23.replace K0) m23.d hd23).2.2 hd0

  have heDef23 :
      vertexDefect (m23.replace K0) m23.e =
        vertexDefect K0 m23.e + 2 :=
    (vertexDefect_of_degree_add_two
      K0 (m23.replace K0) m23.e he23).2.2 he0

  have hb23 := m23.replace_PhiSupport_balance K0 h23

  have hPhi23 :
      PhiSupport (m23.replace K0) = PhiSupport K0 + 4 := by
    omega

  have h32realized : m32.RealizedIn (m23.replace K0) := h32.1
  rcases h32realized with ⟨⟨tau, htau, hmatch⟩, _, _⟩

  have hd1Support : m32.d ∈ vertexSupport (m23.replace K0) := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htau, (hmatch m32.d).2 (by
      simp [Move32Site.targetTet₀, Tet.verts])⟩

  have he1Support : m32.e ∈ vertexSupport (m23.replace K0) := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htau, (hmatch m32.e).2 (by
      simp [Move32Site.targetTet₀, Tet.verts])⟩

  have hd2Support : m32.d ∈ vertexSupport (m32.replace (m23.replace K0)) :=
    (hcore1.move32Site_replace_vertexSupport_mem_iff m32 h32 m32.d).2 hd1Support
  have he2Support : m32.e ∈ vertexSupport (m32.replace (m23.replace K0)) :=
    (hcore1.move32Site_replace_vertexSupport_mem_iff m32 h32 m32.e).2 he1Support

  have hd2 : 4 ≤ vertexDegree (m32.replace (m23.replace K0)) m32.d :=
    hcore2.vertexDegree_ge_four_of_mem_vertexSupport hd2Support
  have he2 : 4 ≤ vertexDegree (m32.replace (m23.replace K0)) m32.e :=
    hcore2.vertexDegree_ge_four_of_mem_vertexSupport he2Support

  rcases hcore1.move32Site_replace_vertexDegree_site m32 h32 with
    ⟨_, _, _, hd32, he32⟩

  have hdDef32 :
      vertexDefect (m23.replace K0) m32.d =
        vertexDefect (m32.replace (m23.replace K0)) m32.d + 2 :=
    (vertexDefect_of_degree_add_two
      (m32.replace (m23.replace K0)) (m23.replace K0) m32.d hd32).2.2 hd2

  have heDef32 :
      vertexDefect (m23.replace K0) m32.e =
        vertexDefect (m32.replace (m23.replace K0)) m32.e + 2 :=
    (vertexDefect_of_degree_add_two
      (m32.replace (m23.replace K0)) (m23.replace K0) m32.e he32).2.2 he2

  have hb32 := hcore1.move32Site_replace_PhiSupport_balance m32 h32

  have hPhi32 :
      PhiSupport (m32.replace (m23.replace K0)) + 4 =
        PhiSupport (m23.replace K0) := by
    omega

  omega

end Poincare
