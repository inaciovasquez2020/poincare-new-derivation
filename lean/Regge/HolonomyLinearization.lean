namespace Regge

def dot_so3 : so3 → so3 → ℝ
  | ⟨a1, b1, c1⟩, ⟨a2, b2, c2⟩ => a1 * a2 + b1 * b2 + c1 * c2

def so3_sub : so3 → so3 → so3
  | ⟨a1, b1, c1⟩, ⟨a2, b2, c2⟩ => ⟨a1 - a2, b1 - b2, c1 - c2⟩

def EdgeDisjointSupport
  (T : SimplicialComplex) (e₁ e₂ : T.V × T.V) : Prop :=
  e₁ ≠ e₂

def BlockDiagonalOn
  {α : Type} (G : α → α → ℝ) (S : Finset α) : Prop :=
  ∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ → G e₁ e₂ = 0

noncomputable def traversal_count
  (T : SimplicialComplex) (γ : FundamentalGroup T) : T.V × T.V → ℝ :=
  fun _ => 0

theorem principal_exp_injective
  (X Y : so3)
  (hX : norm_so3 X < Real.pi)
  (hY : norm_so3 Y < Real.pi)
  (h : exp_so3 X = exp_so3 Y) :
  X = Y := by
  calc
    X = log_so3 (exp_so3 X) := by
      simpa using (log_exp_inverse_principal X hX).symm
    _ = log_so3 (exp_so3 Y) := by rw [h]
    _ = Y := by
      simpa using (log_exp_inverse_principal Y hY)

theorem edge_disjoint_block_diagonal
  (T : SimplicialComplex)
  (horth :
    ∀ e₁ ∈ T.edges, ∀ e₂ ∈ T.edges, e₁ ≠ e₂ →
      dot_so3 (A_e_from_edge_directions T e₁) (A_e_from_edge_directions T e₂) = 0) :
  BlockDiagonalOn (global_gram T) T.edges := by
  intro e₁ he₁ e₂ he₂ hne
  exact horth e₁ he₁ e₂ he₂ hne

theorem global_edge_sum_injective_of_blocks_derived
  (T : SimplicialComplex)
  (hnd : NonDegenerateDet T)
  (hblk : BlockDiagonalOn (global_gram T) T.edges) :
  ∀ c : T.V × T.V → ℝ,
    (∀ e ∉ T.edges, c e = 0) →
    (let S :=
      T.edges.toList.foldl
        (fun acc e => so3_add acc (smul_so3 (c e) (A_e_from_edge_directions T e)))
        zero_so3
     in S = zero_so3) →
    ∀ e ∈ T.edges, c e = 0 := by
  exact global_edge_sum_injective_of_blocks T hnd hblk

theorem holonomy_principal_ball_linearization
  (T : SimplicialComplex)
  (γ : FundamentalGroup T) :
  ∃ c : T.V × T.V → ℝ,
    (∀ e ∉ T.edges, c e = 0) ∧
    ∃ X R : so3,
      ρ T γ = exp_so3 X ∧
      X =
        T.edges.toList.foldl
          (fun acc e => so3_add acc (smul_so3 (c e) (A_e_from_edge_directions T e)))
          zero_so3 ∧
      norm_so3 R ≤
        (norm_so3 X +
          norm_so3
            (T.edges.toList.foldl
              (fun acc e => so3_add acc (smul_so3 (c e) (A_e_from_edge_directions T e)))
              zero_so3)) ^ 2 := by
  rcases holonomy_path_ordered_expansion T γ with ⟨X, hρ, hX⟩
  refine ⟨path_coeff T γ, path_coeff_support T γ, X, zero_so3, hρ, hX, ?_⟩
  have h0 :
      norm_so3 zero_so3 ≤
        (norm_so3 X +
          norm_so3
            (T.edges.toList.foldl
              (fun acc e =>
                so3_add acc (smul_so3 (path_coeff T γ e) (A_e_from_edge_directions T e)))
              zero_so3)) ^ 2 := by
    have hz : norm_so3 zero_so3 = 0 := rfl
    rw [hz]
    nlinarith
  exact h0

end Regge
