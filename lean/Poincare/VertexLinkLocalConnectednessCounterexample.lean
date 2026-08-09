import Poincare.VertexLinkConnectednessCounterexample

namespace Poincare

def edgePinchCandidate : Triangulation :=
  {
    tets :=
      [
        ⟨0, 1, 2, 3⟩,
        ⟨0, 1, 2, 4⟩,
        ⟨0, 1, 3, 4⟩,

        ⟨0, 1, 5, 6⟩,
        ⟨0, 1, 5, 7⟩,
        ⟨0, 1, 6, 7⟩,

        ⟨0, 2, 3, 5⟩,
        ⟨0, 2, 4, 6⟩,
        ⟨0, 2, 5, 6⟩,
        ⟨0, 3, 4, 6⟩,
        ⟨0, 3, 5, 7⟩,
        ⟨0, 3, 6, 7⟩,

        ⟨1, 2, 3, 5⟩,
        ⟨1, 2, 4, 6⟩,
        ⟨1, 2, 5, 6⟩,
        ⟨1, 3, 4, 6⟩,
        ⟨1, 3, 5, 7⟩,
        ⟨1, 3, 6, 7⟩
      ]
  }


theorem edgePinchCandidate_closedCore :
    ClosedTriangulationCore
      edgePinchCandidate := by

  constructor

  · intro τ hτ

    simp [edgePinchCandidate] at hτ

    rcases hτ with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      native_decide

  constructor

  · native_decide

  · intro a b c habc hrepresented

    rcases hrepresented with
      ⟨τ, hτ, ha, hb, hc⟩

    simp [edgePinchCandidate] at hτ

    rcases hτ with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [
        edgePinchCandidate,
        Tet.verts
      ] at ha hb hc <;>
      rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      norm_num at habc <;>
      native_decide


theorem edgePinchCandidate_link_zero :
    vertexLinkTriangles
        edgePinchCandidate 0 =
      [
        ⟨1, 2, 3⟩,
        ⟨1, 2, 4⟩,
        ⟨1, 3, 4⟩,

        ⟨1, 5, 6⟩,
        ⟨1, 5, 7⟩,
        ⟨1, 6, 7⟩,

        ⟨2, 3, 5⟩,
        ⟨2, 4, 6⟩,
        ⟨2, 5, 6⟩,
        ⟨3, 4, 6⟩,
        ⟨3, 5, 7⟩,
        ⟨3, 6, 7⟩
      ] := by
  native_decide


theorem edgePinchCandidate_star_zero_one :
    vertexLinkStarTriangles
        edgePinchCandidate 0 1 =
      [
        ⟨1, 2, 3⟩,
        ⟨1, 2, 4⟩,
        ⟨1, 3, 4⟩,
        ⟨1, 5, 6⟩,
        ⟨1, 5, 7⟩,
        ⟨1, 6, 7⟩
      ] := by
  native_decide


def edgePinchCandidateStarLeftBlock
    (σ : LinkTriangle) : Prop :=
  σ ∈
    [
      ⟨1, 2, 3⟩,
      ⟨1, 2, 4⟩,
      ⟨1, 3, 4⟩
    ]


theorem edgePinchCandidate_starAdjacent_preserves_left
    (σ ρ : LinkTriangle)
    (hadj :
      VertexLinkStarAdjacent
        edgePinchCandidate 0 1 σ ρ)
    (hleft :
      edgePinchCandidateStarLeftBlock σ) :
    edgePinchCandidateStarLeftBlock ρ := by

  rcases hadj with
    ⟨_, hρ, hshare⟩

  simp [
    edgePinchCandidateStarLeftBlock
  ] at hleft

  rw [
    edgePinchCandidate_star_zero_one
  ] at hρ

  simp at hρ

  rcases hleft with
      rfl | rfl | rfl <;>
    rcases hρ with
      rfl | rfl | rfl |
      rfl | rfl | rfl

  all_goals
    simp [
      edgePinchCandidateStarLeftBlock
    ]

  all_goals
    rcases hshare with
      ⟨y, hy1, hyσ, hyρ⟩
    simp [
      LinkTriangle.verts
    ] at hyσ hyρ
    omega


theorem edgePinchCandidate_starPath_preserves_left
    (σ ρ : LinkTriangle)
    (hpath :
      Relation.ReflTransGen
        (VertexLinkStarAdjacent
          edgePinchCandidate 0 1)
        σ ρ)
    (hleft :
      edgePinchCandidateStarLeftBlock σ) :
    edgePinchCandidateStarLeftBlock ρ := by

  exact
    Relation.ReflTransGen.trans_induction_on
      (motive :=
        fun {a b} _ =>
          edgePinchCandidateStarLeftBlock a →
            edgePinchCandidateStarLeftBlock b)
      hpath
      (fun _ ha => ha)
      (fun hstep ha =>
        edgePinchCandidate_starAdjacent_preserves_left
          _ _ hstep ha)
      (fun _ _ ih₁ ih₂ ha =>
        ih₂ (ih₁ ha))
      hleft


theorem edgePinchCandidate_star_zero_one_not_connected :
    ¬ VertexLinkStarConnected
        edgePinchCandidate 0 1 := by

  intro hconnected

  unfold VertexLinkStarConnected at hconnected

  let σL : LinkTriangle :=
    ⟨1, 2, 3⟩

  let σR : LinkTriangle :=
    ⟨1, 5, 6⟩

  have hσL :
      σL ∈
        vertexLinkStarTriangles
          edgePinchCandidate 0 1 := by
    rw [edgePinchCandidate_star_zero_one]
    simp [σL]

  have hσR :
      σR ∈
        vertexLinkStarTriangles
          edgePinchCandidate 0 1 := by
    rw [edgePinchCandidate_star_zero_one]
    simp [σR]

  have hpath :
      Relation.ReflTransGen
        (VertexLinkStarAdjacent
          edgePinchCandidate 0 1)
        σL σR :=
    hconnected
      σL hσL
      σR hσR

  have hleft :
      edgePinchCandidateStarLeftBlock σL := by
    simp [
      edgePinchCandidateStarLeftBlock,
      σL
    ]

  have hforced :
      edgePinchCandidateStarLeftBlock σR :=
    edgePinchCandidate_starPath_preserves_left
      σL σR hpath hleft

  have hnot :
      ¬ edgePinchCandidateStarLeftBlock σR := by
    simp [
      edgePinchCandidateStarLeftBlock,
      σR
    ]

  exact hnot hforced


theorem edgePinchCandidate_not_VertexLinksLocallyConnected_of_zero :
    VertexLinkVertexRepresented
        edgePinchCandidate 0 1 →
      ¬ VertexLinksLocallyConnected
        edgePinchCandidate := by

  intro hrep
  intro hall

  have hzero :
      0 ∈ vertexSupport
        edgePinchCandidate := by
    native_decide

  have hlocal :
      VertexLinkLocallyConnected
        edgePinchCandidate 0 :=
    hall 0 hzero

  have hstar :
      VertexLinkStarConnected
        edgePinchCandidate 0 1 :=
    hlocal 1 hrep

  exact
    edgePinchCandidate_star_zero_one_not_connected
      hstar


theorem edgePinchCandidate_not_VertexLinksLocallyConnected :
    ¬ VertexLinksLocallyConnected
        edgePinchCandidate := by

  apply
    edgePinchCandidate_not_VertexLinksLocallyConnected_of_zero

  refine
    ⟨⟨1, 2, 3⟩, ?_, ?_⟩

  · rw [edgePinchCandidate_link_zero]
    simp

  · simp [LinkTriangle.verts]

theorem edgePinchCandidate_vertexLinkConnected_zero :
    VertexLinkConnected edgePinchCandidate 0 := by
  intro σ hσ ρ hρ

  have edgePath
      (a b : LinkTriangle)
      (h : VertexLinkAdjacent edgePinchCandidate 0 a b) :
      Relation.ReflTransGen
        (VertexLinkAdjacent edgePinchCandidate 0)
        a b :=
    Relation.ReflTransGen.single h

  have toRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 0,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 0)
          τ ⟨1, 2, 3⟩ := by
    intro τ hτ

    by_cases h123 : τ = ⟨1, 2, 3⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h124 : τ = ⟨1, 2, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h134 : τ = ⟨1, 3, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h156 : τ = ⟨1, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 5, 6⟩
          ⟨2, 5, 6⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨2, 5, 6⟩
            ⟨2, 3, 5⟩
            (by native_decide))
          (edgePath
            ⟨2, 3, 5⟩
            ⟨1, 2, 3⟩
            (by native_decide)))

    by_cases h256 : τ = ⟨2, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨2, 5, 6⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (edgePath
          ⟨2, 3, 5⟩
          ⟨1, 2, 3⟩
          (by native_decide))

    by_cases h235 : τ = ⟨2, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h157 : τ = ⟨1, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 5, 7⟩
          ⟨3, 5, 7⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨3, 5, 7⟩
            ⟨2, 3, 5⟩
            (by native_decide))
          (edgePath
            ⟨2, 3, 5⟩
            ⟨1, 2, 3⟩
            (by native_decide)))

    by_cases h357 : τ = ⟨3, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨3, 5, 7⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (edgePath
          ⟨2, 3, 5⟩
          ⟨1, 2, 3⟩
          (by native_decide))

    by_cases h167 : τ = ⟨1, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 6, 7⟩
          ⟨3, 6, 7⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨3, 6, 7⟩
            ⟨3, 4, 6⟩
            (by native_decide))
          (Relation.ReflTransGen.trans
            (edgePath
              ⟨3, 4, 6⟩
              ⟨1, 3, 4⟩
              (by native_decide))
            (edgePath
              ⟨1, 3, 4⟩
              ⟨1, 2, 3⟩
              (by native_decide))))

    by_cases h367 : τ = ⟨3, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨3, 6, 7⟩
          ⟨3, 4, 6⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨3, 4, 6⟩
            ⟨1, 3, 4⟩
            (by native_decide))
          (edgePath
            ⟨1, 3, 4⟩
            ⟨1, 2, 3⟩
            (by native_decide)))

    by_cases h346 : τ = ⟨3, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨3, 4, 6⟩
          ⟨1, 3, 4⟩
          (by native_decide))
        (edgePath
          ⟨1, 3, 4⟩
          ⟨1, 2, 3⟩
          (by native_decide))

    by_cases h246 : τ = ⟨2, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨2, 4, 6⟩
          ⟨1, 2, 4⟩
          (by native_decide))
        (edgePath
          ⟨1, 2, 4⟩
          ⟨1, 2, 3⟩
          (by native_decide))

    simp [
      edgePinchCandidate_link_zero,
      h123, h124, h134,
      h156, h256, h235,
      h157, h357,
      h167, h367, h346, h246
    ] at hτ

  have fromRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 0,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 0)
          ⟨1, 2, 3⟩ τ := by
    intro τ hτ

    by_cases h123 : τ = ⟨1, 2, 3⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h124 : τ = ⟨1, 2, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h134 : τ = ⟨1, 3, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h156 : τ = ⟨1, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 2, 3⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨2, 3, 5⟩
            ⟨2, 5, 6⟩
            (by native_decide))
          (edgePath
            ⟨2, 5, 6⟩
            ⟨1, 5, 6⟩
            (by native_decide)))

    by_cases h256 : τ = ⟨2, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 2, 3⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (edgePath
          ⟨2, 3, 5⟩
          ⟨2, 5, 6⟩
          (by native_decide))

    by_cases h235 : τ = ⟨2, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h157 : τ = ⟨1, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 2, 3⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨2, 3, 5⟩
            ⟨3, 5, 7⟩
            (by native_decide))
          (edgePath
            ⟨3, 5, 7⟩
            ⟨1, 5, 7⟩
            (by native_decide)))

    by_cases h357 : τ = ⟨3, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 2, 3⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (edgePath
          ⟨2, 3, 5⟩
          ⟨3, 5, 7⟩
          (by native_decide))

    by_cases h167 : τ = ⟨1, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 2, 3⟩
          ⟨1, 3, 4⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨1, 3, 4⟩
            ⟨3, 4, 6⟩
            (by native_decide))
          (Relation.ReflTransGen.trans
            (edgePath
              ⟨3, 4, 6⟩
              ⟨3, 6, 7⟩
              (by native_decide))
            (edgePath
              ⟨3, 6, 7⟩
              ⟨1, 6, 7⟩
              (by native_decide))))

    by_cases h367 : τ = ⟨3, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 2, 3⟩
          ⟨1, 3, 4⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨1, 3, 4⟩
            ⟨3, 4, 6⟩
            (by native_decide))
          (edgePath
            ⟨3, 4, 6⟩
            ⟨3, 6, 7⟩
            (by native_decide)))

    by_cases h346 : τ = ⟨3, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 2, 3⟩
          ⟨1, 3, 4⟩
          (by native_decide))
        (edgePath
          ⟨1, 3, 4⟩
          ⟨3, 4, 6⟩
          (by native_decide))

    by_cases h246 : τ = ⟨2, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 2, 3⟩
          ⟨1, 2, 4⟩
          (by native_decide))
        (edgePath
          ⟨1, 2, 4⟩
          ⟨2, 4, 6⟩
          (by native_decide))

    simp [
      edgePinchCandidate_link_zero,
      h123, h124, h134,
      h156, h256, h235,
      h157, h357,
      h167, h367, h346, h246
    ] at hτ

  exact Relation.ReflTransGen.trans
    (toRoot σ hσ)
    (fromRoot ρ hρ)

end Poincare
