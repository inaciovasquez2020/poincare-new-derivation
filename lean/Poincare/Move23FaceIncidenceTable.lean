import Poincare.TetrahedronFaceClassification
import Poincare.Move23SimpleBistellarData

namespace Poincare

def Tet.ContainsTriple (tau : Tet) (x y z : Nat) : Bool :=
  tau.verts.contains x && (tau.verts.contains y && tau.verts.contains z)

@[simp] theorem Tet.containsTriple_eq_true (tau : Tet) (x y z : Nat) :
    tau.ContainsTriple x y z = true ↔
      x ∈ tau.verts ∧ y ∈ tau.verts ∧ z ∈ tau.verts := by
  simp [Tet.ContainsTriple]

def SameTripleVertices (x y z a b c : Nat) : Prop :=
  ∀ v, v = x ∨ v = y ∨ v = z ↔ v = a ∨ v = b ∨ v = c

theorem filter_containsTriple_length_eq_of_sameTripleVertices
    (L : List Tet) {x y z a b c : Nat}
    (h : SameTripleVertices x y z a b c) :
    (L.filter fun tau => tau.ContainsTriple x y z).length =
      (L.filter fun tau => tau.ContainsTriple a b c).length := by
  congr 2
  funext tau
  apply (Bool.eq_iff_iff).2
  simp only [Tet.containsTriple_eq_true]
  constructor <;> intro ht
  · constructor
    · rcases (h a).2 (Or.inl rfl) with ha | ha | ha <;>
        rcases ha with rfl
      · exact ht.1
      · exact ht.2.1
      · exact ht.2.2
    · constructor
      · rcases (h b).2 (Or.inr (Or.inl rfl)) with hb | hb | hb <;>
          rcases hb with rfl
        · exact ht.1
        · exact ht.2.1
        · exact ht.2.2
      · rcases (h c).2 (Or.inr (Or.inr rfl)) with hc | hc | hc <;>
          rcases hc with rfl
        · exact ht.1
        · exact ht.2.1
        · exact ht.2.2
  · constructor
    · rcases (h x).1 (Or.inl rfl) with hx | hx | hx <;>
        rcases hx with rfl
      · exact ht.1
      · exact ht.2.1
      · exact ht.2.2
    · constructor
      · rcases (h y).1 (Or.inr (Or.inl rfl)) with hy | hy | hy <;>
          rcases hy with rfl
        · exact ht.1
        · exact ht.2.1
        · exact ht.2.2
      · rcases (h z).1 (Or.inr (Or.inr rfl)) with hz | hz | hz <;>
          rcases hz with rfl
        · exact ht.1
        · exact ht.2.1
        · exact ht.2.2

private theorem Move23Site.local_boundary_abd (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.a s.b s.d).length = 1 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.a s.b s.d).length = 1 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

private theorem Move23Site.local_boundary_abe (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.a s.b s.e).length = 1 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.a s.b s.e).length = 1 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

private theorem Move23Site.local_boundary_acd (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.a s.c s.d).length = 1 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.a s.c s.d).length = 1 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

private theorem Move23Site.local_boundary_ace (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.a s.c s.e).length = 1 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.a s.c s.e).length = 1 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

private theorem Move23Site.local_boundary_bcd (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.b s.c s.d).length = 1 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.b s.c s.d).length = 1 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

private theorem Move23Site.local_boundary_bce (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.b s.c s.e).length = 1 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.b s.c s.e).length = 1 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

theorem Move23Site.local_internal_abc (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.a s.b s.c).length = 2 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.a s.b s.c).length = 0 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

theorem Move23Site.local_internal_ade (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.a s.d s.e).length = 0 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.a s.d s.e).length = 2 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

theorem Move23Site.local_internal_bde (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.b s.d s.e).length = 0 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.b s.d s.e).length = 2 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

theorem Move23Site.local_internal_cde (s : Move23Site) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple s.c s.d s.e).length = 0 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple s.c s.d s.e).length = 2 := by
  have h := s.distinct
  simp [Tet.ContainsTriple, Move23Site.leftTet, Move23Site.rightTet,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts] at h ⊢
  simp_all [eq_comm]

/-- The source and target local clusters each contribute one tetrahedron to
every boundary face of the `2-3` bipyramid. -/
theorem Move23Site.boundaryFace_local_incidence_balance
    (s : Move23Site) (x y z : Nat)
    (hface :
      SameTripleVertices x y z s.a s.b s.d ∨
      SameTripleVertices x y z s.a s.b s.e ∨
      SameTripleVertices x y z s.a s.c s.d ∨
      SameTripleVertices x y z s.a s.c s.e ∨
      SameTripleVertices x y z s.b s.c s.d ∨
      SameTripleVertices x y z s.b s.c s.e) :
    ([s.leftTet, s.rightTet].filter fun tau =>
      tau.ContainsTriple x y z).length = 1 ∧
    ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun tau =>
      tau.ContainsTriple x y z).length = 1 := by
  rcases hface with h | h | h | h | h | h
  · simpa [filter_containsTriple_length_eq_of_sameTripleVertices _ h] using
      s.local_boundary_abd
  · simpa [filter_containsTriple_length_eq_of_sameTripleVertices _ h] using
      s.local_boundary_abe
  · simpa [filter_containsTriple_length_eq_of_sameTripleVertices _ h] using
      s.local_boundary_acd
  · simpa [filter_containsTriple_length_eq_of_sameTripleVertices _ h] using
      s.local_boundary_ace
  · simpa [filter_containsTriple_length_eq_of_sameTripleVertices _ h] using
      s.local_boundary_bcd
  · simpa [filter_containsTriple_length_eq_of_sameTripleVertices _ h] using
      s.local_boundary_bce

/-- Every nondegenerate face represented by one of the three target
tetrahedra of a `2-3` move is either a bipyramid boundary face or one of the
three new internal faces through the new edge. -/
theorem Move23Site.target_local_face_incidence_cases
    (s : Move23Site) (x y z : Nat)
    (hxyz : [x, y, z].Nodup)
    {tau : Tet}
    (htau : tau ∈ [s.newTet₀, s.newTet₁, s.newTet₂])
    (hcontains : tau.ContainsTriple x y z = true) :
    SameTripleVertices x y z s.a s.b s.d ∨
    SameTripleVertices x y z s.a s.b s.e ∨
    SameTripleVertices x y z s.a s.c s.d ∨
    SameTripleVertices x y z s.a s.c s.e ∨
    SameTripleVertices x y z s.b s.c s.d ∨
    SameTripleVertices x y z s.b s.c s.e ∨
    SameTripleVertices x y z s.a s.d s.e ∨
    SameTripleVertices x y z s.b s.d s.e ∨
    SameTripleVertices x y z s.c s.d s.e := by
  have hc := (Tet.containsTriple_eq_true tau x y z).1 hcontains
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htau
  rcases htau with htau | htau | htau
  · subst tau
    rcases Tet.distinct_triple_face_cases s.newTet₀ x y z hxyz hc.1 hc.2.1 hc.2.2 with
      h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (by simpa [Move23Site.newTet₀] using h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by simpa [Move23Site.newTet₀] using h)))))))
    · exact Or.inr (Or.inl (by simpa [Move23Site.newTet₀] using h))
    · exact Or.inl (by simpa [Move23Site.newTet₀] using h)
  · subst tau
    rcases Tet.distinct_triple_face_cases s.newTet₁ x y z hxyz hc.1 hc.2.1 hc.2.2 with
      h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (by simpa [Move23Site.newTet₁] using h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by simpa [Move23Site.newTet₁] using h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (by simpa [Move23Site.newTet₁] using h))))
    · exact Or.inr (Or.inr (Or.inl
        (by simpa [Move23Site.newTet₁] using h)))
  · subst tau
    rcases Tet.distinct_triple_face_cases s.newTet₂ x y z hxyz hc.1 hc.2.1 hc.2.2 with
      h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (by simpa [Move23Site.newTet₂] using h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (by simpa [Move23Site.newTet₂] using h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by simpa [Move23Site.newTet₂] using h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by simpa [Move23Site.newTet₂] using h)))))

/-- Every nondegenerate face represented by a source tetrahedron is either a
bipyramid boundary face or the old internal shared face. -/
theorem Move23Site.source_local_face_incidence_cases
    (s : Move23Site) (x y z : Nat)
    (hxyz : [x, y, z].Nodup)
    {tau : Tet}
    (htau : tau ∈ [s.leftTet, s.rightTet])
    (hcontains : tau.ContainsTriple x y z = true) :
    SameTripleVertices x y z s.a s.b s.d ∨
    SameTripleVertices x y z s.a s.b s.e ∨
    SameTripleVertices x y z s.a s.c s.d ∨
    SameTripleVertices x y z s.a s.c s.e ∨
    SameTripleVertices x y z s.b s.c s.d ∨
    SameTripleVertices x y z s.b s.c s.e ∨
    SameTripleVertices x y z s.a s.b s.c := by
  have hc := (Tet.containsTriple_eq_true tau x y z).1 hcontains
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htau
  rcases htau with rfl | rfl
  · rcases Tet.distinct_triple_face_cases s.leftTet x y z hxyz hc.1 hc.2.1 hc.2.2 with
      h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by simpa [Move23Site.leftTet] using h)))))
    · exact Or.inr (Or.inr (Or.inl (by simpa [Move23Site.leftTet] using h)))
    · exact Or.inl (by simpa [Move23Site.leftTet] using h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by simpa [Move23Site.leftTet] using h))))))
  · rcases Tet.distinct_triple_face_cases s.rightTet x y z hxyz hc.1 hc.2.1 hc.2.2 with
      h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by simpa [Move23Site.rightTet] using h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (by simpa [Move23Site.rightTet] using h))))
    · exact Or.inr (Or.inl (by simpa [Move23Site.rightTet] using h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by simpa [Move23Site.rightTet] using h))))))

end Poincare
