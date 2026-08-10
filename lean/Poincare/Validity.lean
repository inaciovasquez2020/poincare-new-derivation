import Poincare.Moves

namespace Poincare

def ClosedTriangulationCore (K : Triangulation) : Prop :=
  (∀ τ ∈ K.tets, τ.verts.Nodup) ∧

  K.tets.Pairwise
    (fun τ σ => ¬ SameTetVertices τ σ) ∧

  ∀ a b c : Nat,
    [a, b, c].Nodup →
    (∃ τ ∈ K.tets,
      a ∈ τ.verts ∧
      b ∈ τ.verts ∧
      c ∈ τ.verts) →
    (K.tets.filter
      (fun τ =>
        a ∈ τ.verts ∧
        b ∈ τ.verts ∧
        c ∈ τ.verts)).length = 2

/-- A represented triangle in a closed triangulation has a second incident
tetrahedron with a different vertex set. -/
theorem ClosedTriangulationCore.exists_other_tet_across_triangle
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {a b c : Nat}
    (habc : [a, b, c].Nodup)
    {τ : Tet}
    (hτK : τ ∈ K.tets)
    (haτ : a ∈ τ.verts)
    (hbτ : b ∈ τ.verts)
    (hcτ : c ∈ τ.verts) :
    ∃ ρ ∈ K.tets,
      ¬ SameTetVertices τ ρ ∧
      a ∈ ρ.verts ∧
      b ∈ ρ.verts ∧
      c ∈ ρ.verts := by
  let incident :=
    K.tets.filter (fun σ =>
      a ∈ σ.verts ∧ b ∈ σ.verts ∧ c ∈ σ.verts)

  have hτIncident : τ ∈ incident := by
    simp [incident, hτK, haτ, hbτ, hcτ]

  have hlength : incident.length = 2 := by
    exact hcore.2.2 a b c habc ⟨τ, hτK, haτ, hbτ, hcτ⟩

  have hpairwise :
      incident.Pairwise (fun σ ρ => ¬ SameTetVertices σ ρ) := by
    exact hcore.2.1.filter _

  cases hincident : incident with
  | nil => simp [hincident] at hlength
  | cons σ tail =>
    cases htail : tail with
    | nil => simp [hincident, htail] at hlength
    | cons ρ rest =>
      have hrest : rest = [] := by
        simpa [hincident, htail] using hlength
      subst rest
      simp only [hincident, htail, List.pairwise_cons,
        List.mem_singleton, forall_eq] at hpairwise
      have hσρ : ¬ SameTetVertices σ ρ := hpairwise.1
      have hτCases : τ = σ ∨ τ = ρ := by
        simpa [hincident, htail] using hτIncident
      have hσData :
          σ ∈ K.tets ∧
            (a ∈ σ.verts ∧ b ∈ σ.verts ∧ c ∈ σ.verts) := by
        simpa [incident] using (show σ ∈ incident by simp [hincident, htail])
      have hρData :
          ρ ∈ K.tets ∧
            (a ∈ ρ.verts ∧ b ∈ ρ.verts ∧ c ∈ ρ.verts) := by
        simpa [incident] using (show ρ ∈ incident by simp [hincident, htail])
      rcases hτCases with rfl | rfl
      · exact ⟨ρ, hρData.1, hσρ, hρData.2⟩
      · refine ⟨σ, hσData.1, ?_, hσData.2⟩
        intro hρσ
        apply hσρ
        intro v
        exact (hρσ v).symm


theorem single_tet_not_ClosedTriangulationCore
    (τ : Tet)
    (hτ : τ.verts.Nodup) :
    ¬ ClosedTriangulationCore
      ({ tets := [τ] } : Triangulation) := by
  intro hcore

  have hface :
      [τ.v0, τ.v1, τ.v2].Nodup := by
    have h := hτ
    simp [Tet.verts] at h ⊢
    aesop

  have hrepresented :
      ∃ σ ∈ ([τ] : List Tet),
        τ.v0 ∈ σ.verts ∧
        τ.v1 ∈ σ.verts ∧
        τ.v2 ∈ σ.verts := by
    refine ⟨τ, by simp, ?_⟩
    simp [Tet.verts]

  have hincidence :=
    hcore.2.2
      τ.v0 τ.v1 τ.v2
      hface
      hrepresented

  norm_num [Tet.verts] at hincidence

end Poincare
