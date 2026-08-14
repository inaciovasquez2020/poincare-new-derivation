import Poincare.GlobalEdgeCyclicFan
import Mathlib.Tactic

namespace Poincare

theorem walk_support_subset_of_adjacency_closed
    {V : Type} {G : SimpleGraph V} {u w : V} (p : G.Walk u w)
    {S : V → Prop}
    (hclosed : ∀ {a b}, S a → G.Adj a b → S b)
    (hu : S u) :
    ∀ a ∈ p.support, S a := by
  induction p with
  | nil => simpa
  | cons h p ih =>
      intro a ha
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hu
      · exact ih (hclosed hu h) a ha

private theorem neighbors_eq_of_degreeTwo_triangle
    {K : Triangulation} {v x : Nat}
    (hdeg : VertexLinkStarDegreeTwo K v x)
    {a b c q : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x}}
    (hab : (vertexLinkStarGraph K v x).Adj a b)
    (hac : (vertexLinkStarGraph K v x).Adj a c)
    (hbc : b ≠ c)
    (haq : (vertexLinkStarGraph K v x).Adj a q) :
    q = b ∨ q = c := by
  obtain ⟨r₁, r₂, hr₁a, hr₂a, hr₁r₂, har₁, har₂, hall⟩ :=
    hdeg a.1 a.2
  have hbne : b.1 ≠ a.1 := fun h => hab.ne (Subtype.ext h.symm)
  have hcne : c.1 ≠ a.1 := fun h => hac.ne (Subtype.ext h.symm)
  have hqne : q.1 ≠ a.1 := fun h => haq.ne (Subtype.ext h.symm)
  have hb := hall b.1 hbne ((vertexLinkStarGraph_adj K v x a b).1 hab).2
  have hc := hall c.1 hcne ((vertexLinkStarGraph_adj K v x a c).1 hac).2
  have hq := hall q.1 hqne ((vertexLinkStarGraph_adj K v x a q).1 haq).2
  rcases hb with hb | hb <;> rcases hc with hc | hc <;> rcases hq with hq | hq
  · exact (hbc (Subtype.ext (hb.trans hc.symm))).elim
  · exact (hbc (Subtype.ext (hb.trans hc.symm))).elim
  · exact Or.inl (Subtype.ext (hq.trans hb.symm))
  · exact Or.inr (Subtype.ext (hq.trans hc.symm))
  · exact Or.inr (Subtype.ext (hq.trans hc.symm))
  · exact Or.inl (Subtype.ext (hq.trans hb.symm))
  · exact (hbc (Subtype.ext (hb.trans hc.symm))).elim
  · exact (hbc (Subtype.ext (hb.trans hc.symm))).elim

private theorem AmbientEdgeCyclicFan.star_length_eq_three_of_triangle
    {K : Triangulation} {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    (hcore : ClosedTriangulationCore K)
    (hdeg : VertexLinkStarDegreeTwo K v x)
    {a b c : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x}}
    (hab : (vertexLinkStarGraph K v x).Adj a b)
    (hac : (vertexLinkStarGraph K v x).Adj a c)
    (hbc : (vertexLinkStarGraph K v x).Adj b c) :
    (vertexLinkStarTriangles K v x).length = 3 := by
  have habne := hab.ne
  have hacne := hac.ne
  have hbcne := hbc.ne
  have hclosed : ∀ {p q}, (p = a ∨ p = b ∨ p = c) →
      (vertexLinkStarGraph K v x).Adj p q → (q = a ∨ q = b ∨ q = c) := by
    intro p q hp hpq
    rcases hp with rfl | rfl | rfl
    · rcases neighbors_eq_of_degreeTwo_triangle hdeg hab hac hbcne hpq with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rcases neighbors_eq_of_degreeTwo_triangle hdeg hab.symm hbc hacne hpq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · rcases neighbors_eq_of_degreeTwo_triangle hdeg hac.symm hbc.symm habne hpq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hall : ∀ q : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x},
      q = a ∨ q = b ∨ q = c := by
    intro q
    have hstartTail : F.start ∈ F.walk.support.tail := by
      have hlen := F.length_ge_three
      cases hw : F.walk with
      | nil => rw [hw] at hlen; simp at hlen
      | cons h p => simpa using p.end_mem_support
    have hqtail : q ∈ F.walk.support.tail := by
      have hcoverq := F.covers q
      rw [F.walk.mem_support_iff] at hcoverq
      rcases hcoverq with rfl | h
      · exact hstartTail
      · exact h
    have hqrotTail : q ∈ (F.walk.rotate a (F.covers a)).support.tail :=
      (F.walk.support_rotate a (F.covers a)).mem_iff.mpr hqtail
    have hqrot : q ∈ (F.walk.rotate a (F.covers a)).support := by
      exact (List.mem_of_mem_tail hqrotTail)
    let p := (F.walk.rotate a (F.covers a)).takeUntil q hqrot
    exact walk_support_subset_of_adjacency_closed p hclosed (Or.inl rfl) q p.end_mem_support
  have hmem : ∀ t, t ∈ vertexLinkStarTriangles K v x ↔
      t = a.1 ∨ t = b.1 ∨ t = c.1 := by
    intro t
    constructor
    · intro ht
      rcases hall ⟨t, ht⟩ with h | h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (Or.inl (congrArg Subtype.val h))
      · exact Or.inr (Or.inr (congrArg Subtype.val h))
    · rintro (rfl | rfl | rfl)
      · exact a.2
      · exact b.2
      · exact c.2
  have hperm : (vertexLinkStarTriangles K v x).Perm [a.1, b.1, c.1] :=
    List.perm_ext_iff_of_nodup
      (by unfold vertexLinkStarTriangles; exact (vertexLinkTriangles_nodup K hcore v).filter _)
      (by
        have habv : a.1 ≠ b.1 := fun h => habne (Subtype.ext h)
        have hacv : a.1 ≠ c.1 := fun h => hacne (Subtype.ext h)
        have hbcv : b.1 ≠ c.1 := fun h => hbcne (Subtype.ext h)
        simp [habv, hacv, hbcv]) |>.2
      (by intro t; simpa using hmem t)
  simpa using hperm.length_eq

/-- An adjacent fan pair either supports the legal `2-3` move, or its
represented chord is carried by exactly a three-tetrahedron central edge
star, or an explicit carrier misses at least one central endpoint. -/
theorem ClosedTriangulationCore.ambientEdgeCyclicFan_adjacent_chord_classification
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    {sigma rho} (hadj : (vertexLinkStarGraph K v x).Adj sigma rho) :
    ∃ y z0 z1, ∃ m : Move23Site,
      m.a = v ∧ m.b = x ∧ m.c = y ∧ m.d = z0 ∧ m.e = z1 ∧
      SameTetVertices (F.tetAt sigma) m.leftTet ∧
      SameTetVertices (F.tetAt rho) m.rightTet ∧
      (m.LegalIn K ∨
        (K.tets.filter (fun t => v ∈ t.verts ∧ x ∈ t.verts)).length = 3 ∨
        ∃ tau ∈ K.tets, z0 ∈ tau.verts ∧ z1 ∈ tau.verts ∧
          (v ∉ tau.verts ∨ x ∉ tau.verts)) := by
  classical
  obtain ⟨y, z0, z1, m, ha, hb, hc, hd, he, hleft, hright, hstatus⟩ :=
    hcore.ambientEdgeCyclicFan_adjacent_exists_legalMove23_or_representedChord F hadj
  refine ⟨y, z0, z1, m, ha, hb, hc, hd, he, hleft, hright, ?_⟩
  rcases hstatus with hlegal | ⟨tau, htau, hz0, hz1⟩
  · exact Or.inl hlegal
  · by_cases hcentral : v ∈ tau.verts ∧ x ∈ tau.verts
    · right; left
      obtain ⟨kappa, hkappa⟩ := F.covers_ambient tau htau hcentral.1 hcentral.2
      have hfive : [v, x, y, z0, z1].Nodup := by
        simpa [ha, hb, hc, hd, he] using m.distinct
      have hz0v : z0 ≠ v := by simp [List.nodup_cons] at hfive; aesop
      have hz1v : z1 ≠ v := by simp [List.nodup_cons] at hfive; aesop
      have hz0sigmaTet : z0 ∈ (F.tetAt sigma).verts :=
        (hleft z0).2 (by simp [Move23Site.leftTet, Tet.verts, ha, hb, hc, hd])
      have hz1rhoTet : z1 ∈ (F.tetAt rho).verts :=
        (hright z1).2 (by simp [Move23Site.rightTet, Tet.verts, ha, hb, hc, he])
      have hz1notSigmaTet : z1 ∉ (F.tetAt sigma).verts := by
        intro h
        have := (hleft z1).1 h
        simp [Move23Site.leftTet, Tet.verts, ha, hb, hc, hd] at this
        simp [List.nodup_cons] at hfive
        tauto
      have hz0notRhoTet : z0 ∉ (F.tetAt rho).verts := by
        intro h
        have := (hright z0).1 h
        simp [Move23Site.rightTet, Tet.verts, ha, hb, hc, he] at this
        simp [List.nodup_cons] at hfive
        tauto
      have hz0sigma : z0 ∈ sigma.1.verts :=
        ((F.tetAt sigma).mem_linkTriangleAt?_iff v z0 sigma.1
          (F.tetAt_link sigma) hz0v).2 hz0sigmaTet
      have hz1rho : z1 ∈ rho.1.verts :=
        ((F.tetAt rho).mem_linkTriangleAt?_iff v z1 rho.1
          (F.tetAt_link rho) hz1v).2 hz1rhoTet
      have hz0kappa : z0 ∈ kappa.1.verts :=
        ((F.tetAt kappa).mem_linkTriangleAt?_iff v z0 kappa.1
          (F.tetAt_link kappa) hz0v).2 (by simpa [hkappa] using hz0)
      have hz1kappa : z1 ∈ kappa.1.verts :=
        ((F.tetAt kappa).mem_linkTriangleAt?_iff v z1 kappa.1
          (F.tetAt_link kappa) hz1v).2 (by simpa [hkappa] using hz1)
      have hsigk : sigma ≠ kappa := by
        intro h
        apply hz1notSigmaTet
        rw [h, hkappa]
        exact hz1
      have hrhok : rho ≠ kappa := by
        intro h
        apply hz0notRhoTet
        rw [h, hkappa]
        exact hz0
      have hadjsk : (vertexLinkStarGraph K v x).Adj sigma kappa :=
        (vertexLinkStarGraph_adj K v x sigma kappa).2
          ⟨hsigk, sigma.2, kappa.2, z0, by
            simp [List.nodup_cons] at hfive; aesop, hz0sigma, hz0kappa⟩
      have hadjkr : (vertexLinkStarGraph K v x).Adj kappa rho :=
        (vertexLinkStarGraph_adj K v x kappa rho).2
          ⟨hrhok.symm, kappa.2, rho.2, z1, by
            simp [List.nodup_cons] at hfive; aesop, hz1kappa, hz1rho⟩
      have hrep : VertexLinkVertexRepresented K v x := by
        have hs := (mem_vertexLinkStarTriangles_iff K v x sigma.1).1 sigma.2
        exact ⟨sigma.1, hs⟩
      have hstar := F.star_length_eq_three_of_triangle hcore
        (hcore.vertexLinkStarDegreeTwo hrep) hadj hadjsk hadjkr.symm
      rw [hcore.vertexLinkStarTriangles_length_eq_edgeIncidence v x (by
        simp [List.nodup_cons] at hfive; aesop)] at hstar
      exact hstar
    · right; right
      refine ⟨tau, htau, hz0, hz1, ?_⟩
      exact not_and_or.mp hcentral

end Poincare
