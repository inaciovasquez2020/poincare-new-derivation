import Init

namespace FanTriangle

inductive Reachable {V : Type}
    (Adj : V → V → Prop) (root : V) : V → Prop where
  | base : Reachable Adj root root
  | step {u v : V} :
      Reachable Adj root u → Adj u v → Reachable Adj root v

def DegreeTwo {V : Type} (Adj : V → V → Prop) : Prop :=
  ∀ u v w q : V,
    Adj u v → Adj u w → v ≠ w →
    Adj u q → q = v ∨ q = w

theorem triangle_component_closed
    {V : Type} (Adj : V → V → Prop)
    (a b c : V)
    (hsym : ∀ u v : V, Adj u v → Adj v u)
    (hdeg : DegreeTwo Adj)
    (hab : Adj a b)
    (hac : Adj a c)
    (hbc : Adj b c)
    (habne : a ≠ b)
    (hacne : a ≠ c)
    (hbcne : b ≠ c) :
    ∀ q : V,
      Reachable Adj a q →
      q = a ∨ q = b ∨ q = c := by
  have hclosed :
      ∀ u v : V,
        (u = a ∨ u = b ∨ u = c) →
        Adj u v →
        (v = a ∨ v = b ∨ v = c) := by
    intro u v hu huv
    rcases hu with hua | hub | huc
    · have hav : Adj a v := hua ▸ huv
      rcases hdeg a b c v hab hac hbcne hav with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · have hbv : Adj b v := hub ▸ huv
      rcases hdeg b a c v (hsym a b hab) hbc hacne hbv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · have hcv : Adj c v := huc ▸ huv
      rcases hdeg c a b v
          (hsym a c hac) (hsym b c hbc) habne hcv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  intro q hq
  induction hq with
  | base => exact Or.inl rfl
  | step hp hedge ih => exact hclosed _ _ ih hedge

theorem no_fourth_vertex_in_triangle_fan
    {V : Type} (Adj : V → V → Prop)
    (a b c extra : V)
    (hsym : ∀ u v : V, Adj u v → Adj v u)
    (hdeg : DegreeTwo Adj)
    (hab : Adj a b)
    (hac : Adj a c)
    (hbc : Adj b c)
    (habne : a ≠ b)
    (hacne : a ≠ c)
    (hbcne : b ≠ c)
    (hreach : Reachable Adj a extra)
    (hxa : extra ≠ a)
    (hxb : extra ≠ b)
    (hxc : extra ≠ c) : False := by
  rcases triangle_component_closed Adj a b c
      hsym hdeg hab hac hbc habne hacne hbcne
      extra hreach with h | h | h
  · exact hxa h
  · exact hxb h
  · exact hxc h

end FanTriangle

#check FanTriangle.triangle_component_closed
#check FanTriangle.no_fourth_vertex_in_triangle_fan
#print axioms FanTriangle.triangle_component_closed
#print axioms FanTriangle.no_fourth_vertex_in_triangle_fan