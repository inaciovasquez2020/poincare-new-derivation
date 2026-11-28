import Mathlib

/-!
Standalone algebraic gluing of vertex-star potentials over ZMod 2.
No Poincare imports. Geometry and incidence transport are explicit inputs.
Status: candidate, not kernel-checked in the current session.
-/
namespace G2LocalPotentialGluing

variable {V T F : Type*}

/-- Two tetrahedra are consecutive in the star of the edge uv when they
are the two cofaces of a face containing both u and v. -/
def EdgeStep (onFace : V → F → Prop) (left right : F → T)
    (u v : V) (s t : T) : Prop :=
  ∃ f : F, onFace u f ∧ onFace v f ∧
    ((s = left f ∧ t = right f) ∨ (s = right f ∧ t = left f))

private theorem twice_zero (a : ZMod 2) : a + a = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  calc
    a + a = (2 : ZMod 2) * a := by ring
    _ = 0 := by rw [h, zero_mul]

private theorem eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  calc
    a = a + (b + b) := by rw [twice_zero, add_zero]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

/-- The difference of local potentials is constant across a common face. -/
theorem edgeStep_invariant
    (onFace : V → F → Prop) (left right : F → T)
    (S : F → ZMod 2) (b : V → T → ZMod 2)
    (hlocal : ∀ v f, onFace v f → b v (left f) + b v (right f) = S f)
    {u v : V} {s t : T}
    (h : EdgeStep onFace left right u v s t) :
    b u s + b v s = b u t + b v t := by
  obtain ⟨f, hu, hv, hst⟩ := h
  have he : b u (left f) + b v (left f) =
      b u (right f) + b v (right f) := by
    apply eq_of_add_eq_zero
    calc
      (b u (left f) + b v (left f)) + (b u (right f) + b v (right f)) =
          (b u (left f) + b u (right f)) + (b v (left f) + b v (right f)) := by abel
      _ = 0 := by rw [hlocal u f hu, hlocal v f hv, twice_zero]
  rcases hst with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs, ht]; exact he
  · rw [hs, ht]; exact he.symm

/-- Extend the preceding identity along a finite chain in an edge star. -/
theorem edgePath_invariant
    (onFace : V → F → Prop) (left right : F → T)
    (S : F → ZMod 2) (b : V → T → ZMod 2)
    (hlocal : ∀ v f, onFace v f → b v (left f) + b v (right f) = S f)
    {u v : V} {s t : T}
    (h : Relation.ReflTransGen (EdgeStep onFace left right u v) s t) :
    b u s + b v s = b u t + b v t := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      exact ih.trans (edgeStep_invariant onFace left right S b hlocal hstep)

/-- A represented edge is any pair lying together in a tetrahedron;
repeated endpoints are allowed in this auxiliary relation. -/
def CommonTet (inTet : V → T → Prop) (u v : V) : Prop :=
  ∃ t, inTet u t ∧ inTet v t

noncomputable def transitionWeight (inTet : V → T → Prop)
    (b : V → T → ZMod 2) (u v : V) : ZMod 2 := by
  classical
  exact if h : CommonTet inTet u v then
    b u (Classical.choose h) + b v (Classical.choose h) else 0

/-- The transition weight has the same value for every tetrahedron
containing its two vertices. -/
theorem transitionWeight_eq
    (inTet : V → T → Prop) (onFace : V → F → Prop) (left right : F → T)
    (S : F → ZMod 2) (b : V → T → ZMod 2)
    (hlocal : ∀ v f, onFace v f → b v (left f) + b v (right f) = S f)
    (hconn : ∀ u v s t, u ≠ v → inTet u s → inTet v s →
      inTet u t → inTet v t →
      Relation.ReflTransGen (EdgeStep onFace left right u v) s t)
    (u v : V) (t : T) (hu : inTet u t) (hv : inTet v t) :
    transitionWeight inTet b u v = b u t + b v t := by
  classical
  have h : CommonTet inTet u v := ⟨t, hu, hv⟩
  unfold transitionWeight
  rw [dif_pos h]
  by_cases huv : u = v
  · subst v
    rw [twice_zero, twice_zero]
  · exact edgePath_invariant onFace left right S b hlocal
      (hconn u v (Classical.choose h) t huv
        (Classical.choose_spec h).1 (Classical.choose_spec h).2 hu hv)

/-- Abstract local-to-global gluing. The hypotheses deliberately expose
actual incidence, edge-star connectivity, local boundary solving, and
primal cocycle exactness. No homology or topology is assumed implicitly. -/
theorem global_boundary_of_local_potentials
    (inTet : V → T → Prop) (onFace : V → F → Prop) (left right : F → T)
    (S : F → ZMod 2) (b : V → T → ZMod 2)
    (hTet : ∀ t, ∃ v, inTet v t)
    (hFace : ∀ f, ∃ v, onFace v f)
    (hinc : ∀ v f, onFace v f → inTet v (left f) ∧ inTet v (right f))
    (hlocal : ∀ v f, onFace v f → b v (left f) + b v (right f) = S f)
    (hconn : ∀ u v s t, u ≠ v → inTet u s → inTet v s →
      inTet u t → inTet v t →
      Relation.ReflTransGen (EdgeStep onFace left right u v) s t)
    (hexact : ∀ w : V → V → ZMod 2,
      (∀ u, w u u = 0) →
      (∀ u v, w u v = w v u) →
      (∀ t u v x, inTet u t → inTet v t → inTet x t →
        w u v + w v x + w x u = 0) →
      ∃ A : V → ZMod 2, ∀ u v, CommonTet inTet u v →
        w u v = A u + A v) :
    ∃ B : T → ZMod 2, ∀ f, B (left f) + B (right f) = S f := by
  classical
  let w := transitionWeight inTet b
  have hw (u v : V) (t : T) (hu : inTet u t) (hv : inTet v t) :
      w u v = b u t + b v t :=
    transitionWeight_eq inTet onFace left right S b hlocal hconn u v t hu hv
  have hzero : ∀ u, w u u = 0 := by
    intro u
    by_cases h : CommonTet inTet u u
    · obtain ⟨t, hu, _⟩ := h
      rw [hw u u t hu hu, twice_zero]
    · change transitionWeight inTet b u u = 0
      simp only [transitionWeight, dif_neg h]
  have hsym : ∀ u v, w u v = w v u := by
    intro u v
    by_cases h : CommonTet inTet u v
    · obtain ⟨t, hu, hv⟩ := h
      rw [hw u v t hu hv, hw v u t hv hu, add_comm]
    · have h' : ¬ CommonTet inTet v u := by
        rintro ⟨t, hv, hu⟩
        exact h ⟨t, hu, hv⟩
      change transitionWeight inTet b u v = transitionWeight inTet b v u
      simp only [transitionWeight, dif_neg h, dif_neg h']
  have htri : ∀ t u v x, inTet u t → inTet v t → inTet x t →
      w u v + w v x + w x u = 0 := by
    intro t u v x hu hv hx
    rw [hw u v t hu hv, hw v x t hv hx, hw x u t hx hu]
    calc
      (b u t + b v t) + (b v t + b x t) + (b x t + b u t) =
          (b u t + b u t) + (b v t + b v t) + (b x t + b x t) := by abel
      _ = 0 := by simp only [twice_zero, add_zero]
  obtain ⟨A, hA⟩ := hexact w hzero hsym htri
  let B : T → ZMod 2 := fun t =>
    b (Classical.choose (hTet t)) t + A (Classical.choose (hTet t))
  have hB : ∀ t v, inTet v t → B t = b v t + A v := by
    intro t v hv
    let u := Classical.choose (hTet t)
    have hu : inTet u t := Classical.choose_spec (hTet t)
    have he : b u t + b v t = A u + A v :=
      (hw u v t hu hv).symm.trans (hA u v ⟨t, hu, hv⟩)
    change b u t + A u = b v t + A v
    apply eq_of_add_eq_zero
    calc
      (b u t + A u) + (b v t + A v) =
          (b u t + b v t) + (A u + A v) := by abel
      _ = 0 := by rw [he, twice_zero]
  refine ⟨B, ?_⟩
  intro f
  obtain ⟨v, hv⟩ := hFace f
  obtain ⟨hl, hr⟩ := hinc v f hv
  rw [hB (left f) v hl, hB (right f) v hr]
  calc
    (b v (left f) + A v) + (b v (right f) + A v) =
        (b v (left f) + b v (right f)) + (A v + A v) := by abel
    _ = S f := by rw [hlocal v f hv, twice_zero, add_zero]

#print axioms edgeStep_invariant
#print axioms edgePath_invariant
#print axioms transitionWeight_eq
#print axioms global_boundary_of_local_potentials

end G2LocalPotentialGluing
