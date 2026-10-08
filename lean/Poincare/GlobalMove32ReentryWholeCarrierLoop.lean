    source_boundary := ?_
    target_boundary := ?_ }⟩
  · intro t
    exact H.apply_zero t
  · intro t
    exact H.apply_one t
  · intro s
    exact H.eq_fst s (.inl rfl)
  · intro s
    exact H.eq_fst s (.inr rfl)

theorem ClosedTriangulationCore.exists_wholeCarrierLoop_of_witnessedReentry_recurrent_crossing
    {K : Triangulation}