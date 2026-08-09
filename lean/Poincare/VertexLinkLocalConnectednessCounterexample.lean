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

theorem edgePinchCandidate_vertexLinkConnected_one :
    VertexLinkConnected edgePinchCandidate 1 := by
  have hlink :
    vertexLinkTriangles
            edgePinchCandidate 1 =
          [
            ⟨0, 2, 3⟩,
            ⟨0, 2, 4⟩,
            ⟨0, 3, 4⟩,

            ⟨0, 5, 6⟩,
            ⟨0, 5, 7⟩,
            ⟨0, 6, 7⟩,

            ⟨2, 3, 5⟩,
            ⟨2, 4, 6⟩,
            ⟨2, 5, 6⟩,
            ⟨3, 4, 6⟩,
            ⟨3, 5, 7⟩,
            ⟨3, 6, 7⟩
          ] := by
    native_decide
  intro σ hσ ρ hρ

  have edgePath
      (a b : LinkTriangle)
      (h : VertexLinkAdjacent edgePinchCandidate 1 a b) :
      Relation.ReflTransGen
        (VertexLinkAdjacent edgePinchCandidate 1)
        a b :=
    Relation.ReflTransGen.single h

  have toRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 1,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 1)
          τ ⟨0, 2, 3⟩ := by
    intro τ hτ

    by_cases h123 : τ = ⟨0, 2, 3⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h124 : τ = ⟨0, 2, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h134 : τ = ⟨0, 3, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h156 : τ = ⟨0, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 5, 6⟩
          ⟨2, 5, 6⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨2, 5, 6⟩
            ⟨2, 3, 5⟩
            (by native_decide))
          (edgePath
            ⟨2, 3, 5⟩
            ⟨0, 2, 3⟩
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
          ⟨0, 2, 3⟩
          (by native_decide))

    by_cases h235 : τ = ⟨2, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h157 : τ = ⟨0, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 5, 7⟩
          ⟨3, 5, 7⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨3, 5, 7⟩
            ⟨2, 3, 5⟩
            (by native_decide))
          (edgePath
            ⟨2, 3, 5⟩
            ⟨0, 2, 3⟩
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
          ⟨0, 2, 3⟩
          (by native_decide))

    by_cases h167 : τ = ⟨0, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 6, 7⟩
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
              ⟨0, 3, 4⟩
              (by native_decide))
            (edgePath
              ⟨0, 3, 4⟩
              ⟨0, 2, 3⟩
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
            ⟨0, 3, 4⟩
            (by native_decide))
          (edgePath
            ⟨0, 3, 4⟩
            ⟨0, 2, 3⟩
            (by native_decide)))

    by_cases h346 : τ = ⟨3, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨3, 4, 6⟩
          ⟨0, 3, 4⟩
          (by native_decide))
        (edgePath
          ⟨0, 3, 4⟩
          ⟨0, 2, 3⟩
          (by native_decide))

    by_cases h246 : τ = ⟨2, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨2, 4, 6⟩
          ⟨0, 2, 4⟩
          (by native_decide))
        (edgePath
          ⟨0, 2, 4⟩
          ⟨0, 2, 3⟩
          (by native_decide))

    simp [
      hlink,
      h123, h124, h134,
      h156, h256, h235,
      h157, h357,
      h167, h367, h346, h246
    ] at hτ

  have fromRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 1,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 1)
          ⟨0, 2, 3⟩ τ := by
    intro τ hτ

    by_cases h123 : τ = ⟨0, 2, 3⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h124 : τ = ⟨0, 2, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h134 : τ = ⟨0, 3, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h156 : τ = ⟨0, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 2, 3⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨2, 3, 5⟩
            ⟨2, 5, 6⟩
            (by native_decide))
          (edgePath
            ⟨2, 5, 6⟩
            ⟨0, 5, 6⟩
            (by native_decide)))

    by_cases h256 : τ = ⟨2, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 2, 3⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (edgePath
          ⟨2, 3, 5⟩
          ⟨2, 5, 6⟩
          (by native_decide))

    by_cases h235 : τ = ⟨2, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h157 : τ = ⟨0, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 2, 3⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨2, 3, 5⟩
            ⟨3, 5, 7⟩
            (by native_decide))
          (edgePath
            ⟨3, 5, 7⟩
            ⟨0, 5, 7⟩
            (by native_decide)))

    by_cases h357 : τ = ⟨3, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 2, 3⟩
          ⟨2, 3, 5⟩
          (by native_decide))
        (edgePath
          ⟨2, 3, 5⟩
          ⟨3, 5, 7⟩
          (by native_decide))

    by_cases h167 : τ = ⟨0, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 2, 3⟩
          ⟨0, 3, 4⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨0, 3, 4⟩
            ⟨3, 4, 6⟩
            (by native_decide))
          (Relation.ReflTransGen.trans
            (edgePath
              ⟨3, 4, 6⟩
              ⟨3, 6, 7⟩
              (by native_decide))
            (edgePath
              ⟨3, 6, 7⟩
              ⟨0, 6, 7⟩
              (by native_decide))))

    by_cases h367 : τ = ⟨3, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 2, 3⟩
          ⟨0, 3, 4⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨0, 3, 4⟩
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
          ⟨0, 2, 3⟩
          ⟨0, 3, 4⟩
          (by native_decide))
        (edgePath
          ⟨0, 3, 4⟩
          ⟨3, 4, 6⟩
          (by native_decide))

    by_cases h246 : τ = ⟨2, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 2, 3⟩
          ⟨0, 2, 4⟩
          (by native_decide))
        (edgePath
          ⟨0, 2, 4⟩
          ⟨2, 4, 6⟩
          (by native_decide))

    simp [
      hlink,
      h123, h124, h134,
      h156, h256, h235,
      h157, h357,
      h167, h367, h346, h246
    ] at hτ

  exact Relation.ReflTransGen.trans
    (toRoot σ hσ)
    (fromRoot ρ hρ)

theorem edgePinchCandidate_vertexLinkConnected_two :
    VertexLinkConnected edgePinchCandidate 2 := by

  have hlink :
      vertexLinkTriangles edgePinchCandidate 2 =
        [
          ⟨0, 1, 3⟩,
          ⟨0, 1, 4⟩,
          ⟨0, 3, 5⟩,
          ⟨0, 4, 6⟩,
          ⟨0, 5, 6⟩,
          ⟨1, 3, 5⟩,
          ⟨1, 4, 6⟩,
          ⟨1, 5, 6⟩
        ] := by
    native_decide

  intro σ hσ ρ hρ

  have edgePath
      (a b : LinkTriangle)
      (h : VertexLinkAdjacent edgePinchCandidate 2 a b) :
      Relation.ReflTransGen
        (VertexLinkAdjacent edgePinchCandidate 2)
        a b :=
    Relation.ReflTransGen.single h

  have toRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 2,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 2)
          τ ⟨0, 1, 3⟩ := by
    intro τ hτ

    by_cases h013 : τ = ⟨0, 1, 3⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h014 : τ = ⟨0, 1, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h035 : τ = ⟨0, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h046 : τ = ⟨0, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 4, 6⟩
          ⟨0, 1, 4⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 4⟩
          ⟨0, 1, 3⟩
          (by native_decide))

    by_cases h056 : τ = ⟨0, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 5, 6⟩
          ⟨0, 4, 6⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨0, 4, 6⟩
            ⟨0, 1, 4⟩
            (by native_decide))
          (edgePath
            ⟨0, 1, 4⟩
            ⟨0, 1, 3⟩
            (by native_decide)))

    by_cases h135 : τ = ⟨1, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h146 : τ = ⟨1, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 4, 6⟩
          ⟨0, 1, 4⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 4⟩
          ⟨0, 1, 3⟩
          (by native_decide))

    by_cases h156 : τ = ⟨1, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 5, 6⟩
          ⟨1, 3, 5⟩
          (by native_decide))
        (edgePath
          ⟨1, 3, 5⟩
          ⟨0, 1, 3⟩
          (by native_decide))

    rw [hlink] at hτ
    simp [
      h013, h014, h035, h046,
      h056, h135, h146, h156
    ] at hτ

  have fromRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 2,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 2)
          ⟨0, 1, 3⟩ τ := by
    intro τ hτ

    by_cases h013 : τ = ⟨0, 1, 3⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h014 : τ = ⟨0, 1, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h035 : τ = ⟨0, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h046 : τ = ⟨0, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 1, 3⟩
          ⟨0, 1, 4⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 4⟩
          ⟨0, 4, 6⟩
          (by native_decide))

    by_cases h056 : τ = ⟨0, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 1, 3⟩
          ⟨0, 1, 4⟩
          (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath
            ⟨0, 1, 4⟩
            ⟨0, 4, 6⟩
            (by native_decide))
          (edgePath
            ⟨0, 4, 6⟩
            ⟨0, 5, 6⟩
            (by native_decide)))

    by_cases h135 : τ = ⟨1, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h146 : τ = ⟨1, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 1, 3⟩
          ⟨0, 1, 4⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 4⟩
          ⟨1, 4, 6⟩
          (by native_decide))

    by_cases h156 : τ = ⟨1, 5, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 1, 3⟩
          ⟨1, 3, 5⟩
          (by native_decide))
        (edgePath
          ⟨1, 3, 5⟩
          ⟨1, 5, 6⟩
          (by native_decide))

    rw [hlink] at hτ
    simp [
      h013, h014, h035, h046,
      h056, h135, h146, h156
    ] at hτ

  exact Relation.ReflTransGen.trans
    (toRoot σ hσ)
    (fromRoot ρ hρ)

theorem edgePinchCandidate_vertexLinkConnected_three :
    VertexLinkConnected edgePinchCandidate 3 := by

  have hlink :
      vertexLinkTriangles edgePinchCandidate 3 =
        [
          ⟨0, 1, 2⟩,
          ⟨0, 1, 4⟩,
          ⟨0, 2, 5⟩,
          ⟨0, 4, 6⟩,
          ⟨0, 5, 7⟩,
          ⟨0, 6, 7⟩,
          ⟨1, 2, 5⟩,
          ⟨1, 4, 6⟩,
          ⟨1, 5, 7⟩,
          ⟨1, 6, 7⟩
        ] := by
    native_decide

  intro σ hσ ρ hρ

  have edgePath
      (a b : LinkTriangle)
      (h : VertexLinkAdjacent edgePinchCandidate 3 a b) :
      Relation.ReflTransGen
        (VertexLinkAdjacent edgePinchCandidate 3)
        a b :=
    Relation.ReflTransGen.single h

  have toRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 3,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 3)
          τ ⟨0, 1, 2⟩ := by
    intro τ hτ

    by_cases h012 : τ = ⟨0, 1, 2⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h014 : τ = ⟨0, 1, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h025 : τ = ⟨0, 2, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h046 : τ = ⟨0, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 4, 6⟩ ⟨0, 1, 4⟩ (by native_decide))
        (edgePath ⟨0, 1, 4⟩ ⟨0, 1, 2⟩ (by native_decide))

    by_cases h057 : τ = ⟨0, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 5, 7⟩ ⟨0, 2, 5⟩ (by native_decide))
        (edgePath ⟨0, 2, 5⟩ ⟨0, 1, 2⟩ (by native_decide))

    by_cases h067 : τ = ⟨0, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 6, 7⟩ ⟨0, 4, 6⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨0, 4, 6⟩ ⟨0, 1, 4⟩ (by native_decide))
          (edgePath ⟨0, 1, 4⟩ ⟨0, 1, 2⟩ (by native_decide)))

    by_cases h125 : τ = ⟨1, 2, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h146 : τ = ⟨1, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨1, 4, 6⟩ ⟨0, 1, 4⟩ (by native_decide))
        (edgePath ⟨0, 1, 4⟩ ⟨0, 1, 2⟩ (by native_decide))

    by_cases h157 : τ = ⟨1, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨1, 5, 7⟩ ⟨1, 2, 5⟩ (by native_decide))
        (edgePath ⟨1, 2, 5⟩ ⟨0, 1, 2⟩ (by native_decide))

    by_cases h167 : τ = ⟨1, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨1, 6, 7⟩ ⟨1, 4, 6⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨1, 4, 6⟩ ⟨0, 1, 4⟩ (by native_decide))
          (edgePath ⟨0, 1, 4⟩ ⟨0, 1, 2⟩ (by native_decide)))

    rw [hlink] at hτ
    simp [
      h012, h014, h025, h046, h057,
      h067, h125, h146, h157, h167
    ] at hτ

  have fromRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 3,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 3)
          ⟨0, 1, 2⟩ τ := by
    intro τ hτ

    by_cases h012 : τ = ⟨0, 1, 2⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h014 : τ = ⟨0, 1, 4⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h025 : τ = ⟨0, 2, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h046 : τ = ⟨0, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 2⟩ ⟨0, 1, 4⟩ (by native_decide))
        (edgePath ⟨0, 1, 4⟩ ⟨0, 4, 6⟩ (by native_decide))

    by_cases h057 : τ = ⟨0, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 2⟩ ⟨0, 2, 5⟩ (by native_decide))
        (edgePath ⟨0, 2, 5⟩ ⟨0, 5, 7⟩ (by native_decide))

    by_cases h067 : τ = ⟨0, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 2⟩ ⟨0, 1, 4⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨0, 1, 4⟩ ⟨0, 4, 6⟩ (by native_decide))
          (edgePath ⟨0, 4, 6⟩ ⟨0, 6, 7⟩ (by native_decide)))

    by_cases h125 : τ = ⟨1, 2, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h146 : τ = ⟨1, 4, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 2⟩ ⟨0, 1, 4⟩ (by native_decide))
        (edgePath ⟨0, 1, 4⟩ ⟨1, 4, 6⟩ (by native_decide))

    by_cases h157 : τ = ⟨1, 5, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 2⟩ ⟨1, 2, 5⟩ (by native_decide))
        (edgePath ⟨1, 2, 5⟩ ⟨1, 5, 7⟩ (by native_decide))

    by_cases h167 : τ = ⟨1, 6, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 2⟩ ⟨0, 1, 4⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨0, 1, 4⟩ ⟨1, 4, 6⟩ (by native_decide))
          (edgePath ⟨1, 4, 6⟩ ⟨1, 6, 7⟩ (by native_decide)))

    rw [hlink] at hτ
    simp [
      h012, h014, h025, h046, h057,
      h067, h125, h146, h157, h167
    ] at hτ

  exact Relation.ReflTransGen.trans
    (toRoot σ hσ)
    (fromRoot ρ hρ)

theorem edgePinchCandidate_vertexLinkConnected_four :
    VertexLinkConnected edgePinchCandidate 4 := by

  have hlink :
      vertexLinkTriangles edgePinchCandidate 4 =
        [
          ⟨0, 1, 2⟩,
          ⟨0, 1, 3⟩,
          ⟨0, 2, 6⟩,
          ⟨0, 3, 6⟩,
          ⟨1, 2, 6⟩,
          ⟨1, 3, 6⟩
        ] := by
    native_decide

  intro σ hσ ρ hρ

  have edgePath
      (a b : LinkTriangle)
      (h : VertexLinkAdjacent edgePinchCandidate 4 a b) :
      Relation.ReflTransGen
        (VertexLinkAdjacent edgePinchCandidate 4)
        a b :=
    Relation.ReflTransGen.single h

  have toRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 4,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 4)
          τ ⟨0, 1, 2⟩ := by
    intro τ hτ

    by_cases h012 : τ = ⟨0, 1, 2⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h013 : τ = ⟨0, 1, 3⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h026 : τ = ⟨0, 2, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h036 : τ = ⟨0, 3, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 3, 6⟩
          ⟨0, 1, 3⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 3⟩
          ⟨0, 1, 2⟩
          (by native_decide))

    by_cases h126 : τ = ⟨1, 2, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h136 : τ = ⟨1, 3, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 3, 6⟩
          ⟨0, 1, 3⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 3⟩
          ⟨0, 1, 2⟩
          (by native_decide))

    rw [hlink] at hτ
    simp [
      h012, h013, h026,
      h036, h126, h136
    ] at hτ

  have fromRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 4,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 4)
          ⟨0, 1, 2⟩ τ := by
    intro τ hτ

    by_cases h012 : τ = ⟨0, 1, 2⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h013 : τ = ⟨0, 1, 3⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h026 : τ = ⟨0, 2, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h036 : τ = ⟨0, 3, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 1, 2⟩
          ⟨0, 1, 3⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 3⟩
          ⟨0, 3, 6⟩
          (by native_decide))

    by_cases h126 : τ = ⟨1, 2, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h136 : τ = ⟨1, 3, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 1, 2⟩
          ⟨0, 1, 3⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 3⟩
          ⟨1, 3, 6⟩
          (by native_decide))

    rw [hlink] at hτ
    simp [
      h012, h013, h026,
      h036, h126, h136
    ] at hτ

  exact Relation.ReflTransGen.trans
    (toRoot σ hσ)
    (fromRoot ρ hρ)

theorem edgePinchCandidate_vertexLinkConnected_five :
    VertexLinkConnected edgePinchCandidate 5 := by

  have hlink :
      vertexLinkTriangles edgePinchCandidate 5 =
        [
          ⟨0, 1, 6⟩,
          ⟨0, 1, 7⟩,
          ⟨0, 2, 3⟩,
          ⟨0, 2, 6⟩,
          ⟨0, 3, 7⟩,
          ⟨1, 2, 3⟩,
          ⟨1, 2, 6⟩,
          ⟨1, 3, 7⟩
        ] := by
    native_decide

  intro σ hσ ρ hρ

  have edgePath
      (a b : LinkTriangle)
      (h : VertexLinkAdjacent edgePinchCandidate 5 a b) :
      Relation.ReflTransGen
        (VertexLinkAdjacent edgePinchCandidate 5)
        a b :=
    Relation.ReflTransGen.single h

  have toRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 5,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 5)
          τ ⟨0, 1, 6⟩ := by
    intro τ hτ

    by_cases h016 : τ = ⟨0, 1, 6⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h017 : τ = ⟨0, 1, 7⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h023 : τ = ⟨0, 2, 3⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 2, 3⟩ ⟨0, 2, 6⟩ (by native_decide))
        (edgePath ⟨0, 2, 6⟩ ⟨0, 1, 6⟩ (by native_decide))

    by_cases h026 : τ = ⟨0, 2, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h037 : τ = ⟨0, 3, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 3, 7⟩ ⟨0, 1, 7⟩ (by native_decide))
        (edgePath ⟨0, 1, 7⟩ ⟨0, 1, 6⟩ (by native_decide))

    by_cases h123 : τ = ⟨1, 2, 3⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨1, 2, 3⟩ ⟨1, 2, 6⟩ (by native_decide))
        (edgePath ⟨1, 2, 6⟩ ⟨0, 1, 6⟩ (by native_decide))

    by_cases h126 : τ = ⟨1, 2, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h137 : τ = ⟨1, 3, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨1, 3, 7⟩ ⟨0, 1, 7⟩ (by native_decide))
        (edgePath ⟨0, 1, 7⟩ ⟨0, 1, 6⟩ (by native_decide))

    rw [hlink] at hτ
    simp [
      h016, h017, h023, h026,
      h037, h123, h126, h137
    ] at hτ

  have fromRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 5,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 5)
          ⟨0, 1, 6⟩ τ := by
    intro τ hτ

    by_cases h016 : τ = ⟨0, 1, 6⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h017 : τ = ⟨0, 1, 7⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h023 : τ = ⟨0, 2, 3⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 6⟩ ⟨0, 2, 6⟩ (by native_decide))
        (edgePath ⟨0, 2, 6⟩ ⟨0, 2, 3⟩ (by native_decide))

    by_cases h026 : τ = ⟨0, 2, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h037 : τ = ⟨0, 3, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 6⟩ ⟨0, 1, 7⟩ (by native_decide))
        (edgePath ⟨0, 1, 7⟩ ⟨0, 3, 7⟩ (by native_decide))

    by_cases h123 : τ = ⟨1, 2, 3⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 6⟩ ⟨1, 2, 6⟩ (by native_decide))
        (edgePath ⟨1, 2, 6⟩ ⟨1, 2, 3⟩ (by native_decide))

    by_cases h126 : τ = ⟨1, 2, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h137 : τ = ⟨1, 3, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 6⟩ ⟨0, 1, 7⟩ (by native_decide))
        (edgePath ⟨0, 1, 7⟩ ⟨1, 3, 7⟩ (by native_decide))

    rw [hlink] at hτ
    simp [
      h016, h017, h023, h026,
      h037, h123, h126, h137
    ] at hτ

  exact Relation.ReflTransGen.trans
    (toRoot σ hσ)
    (fromRoot ρ hρ)

theorem edgePinchCandidate_vertexLinkConnected_six :
    VertexLinkConnected edgePinchCandidate 6 := by

  have hlink :
      vertexLinkTriangles edgePinchCandidate 6 =
        [
          ⟨0, 1, 5⟩,
          ⟨0, 1, 7⟩,
          ⟨0, 2, 4⟩,
          ⟨0, 2, 5⟩,
          ⟨0, 3, 4⟩,
          ⟨0, 3, 7⟩,
          ⟨1, 2, 4⟩,
          ⟨1, 2, 5⟩,
          ⟨1, 3, 4⟩,
          ⟨1, 3, 7⟩
        ] := by
    native_decide

  intro σ hσ ρ hρ

  have edgePath
      (a b : LinkTriangle)
      (h : VertexLinkAdjacent edgePinchCandidate 6 a b) :
      Relation.ReflTransGen
        (VertexLinkAdjacent edgePinchCandidate 6)
        a b :=
    Relation.ReflTransGen.single h

  have toRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 6,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 6)
          τ ⟨0, 1, 5⟩ := by
    intro τ hτ

    by_cases h015 : τ = ⟨0, 1, 5⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h017 : τ = ⟨0, 1, 7⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h024 : τ = ⟨0, 2, 4⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 2, 4⟩ ⟨0, 2, 5⟩ (by native_decide))
        (edgePath ⟨0, 2, 5⟩ ⟨0, 1, 5⟩ (by native_decide))

    by_cases h025 : τ = ⟨0, 2, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h034 : τ = ⟨0, 3, 4⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 3, 4⟩ ⟨0, 2, 4⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨0, 2, 4⟩ ⟨0, 2, 5⟩ (by native_decide))
          (edgePath ⟨0, 2, 5⟩ ⟨0, 1, 5⟩ (by native_decide)))

    by_cases h037 : τ = ⟨0, 3, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 3, 7⟩ ⟨0, 1, 7⟩ (by native_decide))
        (edgePath ⟨0, 1, 7⟩ ⟨0, 1, 5⟩ (by native_decide))

    by_cases h124 : τ = ⟨1, 2, 4⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨1, 2, 4⟩ ⟨0, 2, 4⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨0, 2, 4⟩ ⟨0, 2, 5⟩ (by native_decide))
          (edgePath ⟨0, 2, 5⟩ ⟨0, 1, 5⟩ (by native_decide)))

    by_cases h125 : τ = ⟨1, 2, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h134 : τ = ⟨1, 3, 4⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨1, 3, 4⟩ ⟨1, 2, 4⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨1, 2, 4⟩ ⟨0, 2, 4⟩ (by native_decide))
          (Relation.ReflTransGen.trans
            (edgePath ⟨0, 2, 4⟩ ⟨0, 2, 5⟩ (by native_decide))
            (edgePath ⟨0, 2, 5⟩ ⟨0, 1, 5⟩ (by native_decide))))

    by_cases h137 : τ = ⟨1, 3, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨1, 3, 7⟩ ⟨0, 1, 7⟩ (by native_decide))
        (edgePath ⟨0, 1, 7⟩ ⟨0, 1, 5⟩ (by native_decide))

    rw [hlink] at hτ
    simp [
      h015, h017, h024, h025, h034,
      h037, h124, h125, h134, h137
    ] at hτ

  have fromRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 6,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 6)
          ⟨0, 1, 5⟩ τ := by
    intro τ hτ

    by_cases h015 : τ = ⟨0, 1, 5⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h017 : τ = ⟨0, 1, 7⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h024 : τ = ⟨0, 2, 4⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 5⟩ ⟨0, 2, 5⟩ (by native_decide))
        (edgePath ⟨0, 2, 5⟩ ⟨0, 2, 4⟩ (by native_decide))

    by_cases h025 : τ = ⟨0, 2, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h034 : τ = ⟨0, 3, 4⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 5⟩ ⟨0, 2, 5⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨0, 2, 5⟩ ⟨0, 2, 4⟩ (by native_decide))
          (edgePath ⟨0, 2, 4⟩ ⟨0, 3, 4⟩ (by native_decide)))

    by_cases h037 : τ = ⟨0, 3, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 5⟩ ⟨0, 1, 7⟩ (by native_decide))
        (edgePath ⟨0, 1, 7⟩ ⟨0, 3, 7⟩ (by native_decide))

    by_cases h124 : τ = ⟨1, 2, 4⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 5⟩ ⟨0, 2, 5⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨0, 2, 5⟩ ⟨0, 2, 4⟩ (by native_decide))
          (edgePath ⟨0, 2, 4⟩ ⟨1, 2, 4⟩ (by native_decide)))

    by_cases h125 : τ = ⟨1, 2, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h134 : τ = ⟨1, 3, 4⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 5⟩ ⟨0, 2, 5⟩ (by native_decide))
        (Relation.ReflTransGen.trans
          (edgePath ⟨0, 2, 5⟩ ⟨0, 2, 4⟩ (by native_decide))
          (Relation.ReflTransGen.trans
            (edgePath ⟨0, 2, 4⟩ ⟨1, 2, 4⟩ (by native_decide))
            (edgePath ⟨1, 2, 4⟩ ⟨1, 3, 4⟩ (by native_decide))))

    by_cases h137 : τ = ⟨1, 3, 7⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath ⟨0, 1, 5⟩ ⟨0, 1, 7⟩ (by native_decide))
        (edgePath ⟨0, 1, 7⟩ ⟨1, 3, 7⟩ (by native_decide))

    rw [hlink] at hτ
    simp [
      h015, h017, h024, h025, h034,
      h037, h124, h125, h134, h137
    ] at hτ

  exact Relation.ReflTransGen.trans
    (toRoot σ hσ)
    (fromRoot ρ hρ)

theorem edgePinchCandidate_vertexLinkConnected_seven :
    VertexLinkConnected edgePinchCandidate 7 := by

  have hlink :
      vertexLinkTriangles edgePinchCandidate 7 =
        [
          ⟨0, 1, 5⟩,
          ⟨0, 1, 6⟩,
          ⟨0, 3, 5⟩,
          ⟨0, 3, 6⟩,
          ⟨1, 3, 5⟩,
          ⟨1, 3, 6⟩
        ] := by
    native_decide

  intro σ hσ ρ hρ

  have edgePath
      (a b : LinkTriangle)
      (h : VertexLinkAdjacent edgePinchCandidate 7 a b) :
      Relation.ReflTransGen
        (VertexLinkAdjacent edgePinchCandidate 7)
        a b :=
    Relation.ReflTransGen.single h

  have toRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 7,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 7)
          τ ⟨0, 1, 5⟩ := by
    intro τ hτ

    by_cases h015 : τ = ⟨0, 1, 5⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h016 : τ = ⟨0, 1, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h035 : τ = ⟨0, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h036 : τ = ⟨0, 3, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 3, 6⟩
          ⟨0, 1, 6⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 6⟩
          ⟨0, 1, 5⟩
          (by native_decide))

    by_cases h135 : τ = ⟨1, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h136 : τ = ⟨1, 3, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨1, 3, 6⟩
          ⟨0, 1, 6⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 6⟩
          ⟨0, 1, 5⟩
          (by native_decide))

    rw [hlink] at hτ
    simp [
      h015, h016, h035,
      h036, h135, h136
    ] at hτ

  have fromRoot :
      ∀ τ ∈ vertexLinkTriangles edgePinchCandidate 7,
        Relation.ReflTransGen
          (VertexLinkAdjacent edgePinchCandidate 7)
          ⟨0, 1, 5⟩ τ := by
    intro τ hτ

    by_cases h015 : τ = ⟨0, 1, 5⟩
    · subst τ
      exact Relation.ReflTransGen.refl

    by_cases h016 : τ = ⟨0, 1, 6⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h035 : τ = ⟨0, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h036 : τ = ⟨0, 3, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 1, 5⟩
          ⟨0, 1, 6⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 6⟩
          ⟨0, 3, 6⟩
          (by native_decide))

    by_cases h135 : τ = ⟨1, 3, 5⟩
    · subst τ
      exact edgePath _ _ (by native_decide)

    by_cases h136 : τ = ⟨1, 3, 6⟩
    · subst τ
      exact Relation.ReflTransGen.trans
        (edgePath
          ⟨0, 1, 5⟩
          ⟨0, 1, 6⟩
          (by native_decide))
        (edgePath
          ⟨0, 1, 6⟩
          ⟨1, 3, 6⟩
          (by native_decide))

    rw [hlink] at hτ
    simp [
      h015, h016, h035,
      h036, h135, h136
    ] at hτ

  exact Relation.ReflTransGen.trans
    (toRoot σ hσ)
    (fromRoot ρ hρ)

theorem edgePinchCandidate_connectedLinkClosedCore :
    ConnectedLinkClosedCore edgePinchCandidate := by
  refine ⟨edgePinchCandidate_closedCore, ?_⟩

  intro v hv

  have hsupport :
      vertexSupport edgePinchCandidate =
        [0, 1, 2, 3, 4, 5, 6, 7] := by
    native_decide

  by_cases h0 : v = 0
  · subst v
    exact edgePinchCandidate_vertexLinkConnected_zero

  by_cases h1 : v = 1
  · subst v
    exact edgePinchCandidate_vertexLinkConnected_one

  by_cases h2 : v = 2
  · subst v
    exact edgePinchCandidate_vertexLinkConnected_two

  by_cases h3 : v = 3
  · subst v
    exact edgePinchCandidate_vertexLinkConnected_three

  by_cases h4 : v = 4
  · subst v
    exact edgePinchCandidate_vertexLinkConnected_four

  by_cases h5 : v = 5
  · subst v
    exact edgePinchCandidate_vertexLinkConnected_five

  by_cases h6 : v = 6
  · subst v
    exact edgePinchCandidate_vertexLinkConnected_six

  by_cases h7 : v = 7
  · subst v
    exact edgePinchCandidate_vertexLinkConnected_seven

  rw [hsupport] at hv
  simp [h0, h1, h2, h3, h4, h5, h6, h7] at hv

end Poincare
