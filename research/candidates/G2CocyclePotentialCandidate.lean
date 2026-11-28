/-!
Append after the verified G2VertexLinkWalkCandidate.lean in its temporary
compilation, with `import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
in the initial import block. Target revision df7af692a9f70a8f1c68cbca559a119ed7e65366.
NOT_RUN: candidate proof. No changes to existing hypotheses or dependencies.
-/
namespace Poincare

private def g2WalkWeight {G : SimpleGraph Nat} (w : Nat → Nat → ZMod 2)
    {a b : Nat} (p : G.Walk a b) : ZMod 2 :=
  (p.darts.map (fun d => w d.fst d.snd)).sum

private theorem g2WalkWeight_cons {G : SimpleGraph Nat}
    (w : Nat → Nat → ZMod 2) {a b c : Nat}
    (h : G.Adj a b) (p : G.Walk b c) :
    g2WalkWeight w (.cons h p) = w a b + g2WalkWeight w p := rfl

private theorem g2WalkWeight_append {G : SimpleGraph Nat}
    (w : Nat → Nat → ZMod 2) {a b c : Nat}
    (p : G.Walk a b) (q : G.Walk b c) :
    g2WalkWeight w (p.append q) = g2WalkWeight w p + g2WalkWeight w q := by
  simp [g2WalkWeight, SimpleGraph.Walk.darts_append]

private theorem g2WalkWeight_reverse {G : SimpleGraph Nat}
    (w : Nat → Nat → ZMod 2) (hsym : ∀ a b, w a b = w b a)
    {a b : Nat} (p : G.Walk a b) :
    g2WalkWeight w p.reverse = g2WalkWeight w p := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
      rw [SimpleGraph.Walk.reverse_cons, g2WalkWeight_append, ih,
        g2WalkWeight_cons, g2WalkWeight_cons, hsym b a]
      change g2WalkWeight w p + (w a b + 0) = w a b + g2WalkWeight w p
      abel

private theorem g2WalkWeight_eq_sum {G : SimpleGraph Nat}
    (w : Nat → Nat → ZMod 2) {a b : Nat} (p : G.Walk a b) :
    g2WalkWeight w p = ∑ k ∈ Finset.range p.length,
      w (p.getVert k) (p.getVert (k+1)) := by
  induction p with
  | nil => simp [g2WalkWeight]
  | @cons a b c h p ih =>
      rw [g2WalkWeight_cons, ih, SimpleGraph.Walk.length_cons,
        Finset.sum_range_succ']
      simp only [SimpleGraph.Walk.getVert_zero,
        SimpleGraph.Walk.getVert_cons_succ]
      exact add_comm _ _

/-- Closed-walk cancellation gives a potential on every graph component,
including isolated vertices. There is no assumed graph connectivity. -/
theorem g2_graph_potential_of_closed_walks_candidate
    (G : SimpleGraph Nat) (w : Nat → Nat → ZMod 2)
    (hsym : ∀ a b, w a b = w b a)
    (hclosed : ∀ a (p : G.Walk a a), g2WalkWeight w p = 0) :
    ∃ A : Nat → ZMod 2, ∀ a b, G.Adj a b → w a b = A a + A b := by
  classical
  have hex (a : Nat) : ∃ r, G.Reachable r a := ⟨a, .rfl⟩
  let root (a : Nat) : Nat := Nat.find (hex a)
  have hr (a : Nat) : G.Reachable (root a) a := Nat.find_spec (hex a)
  have hroot (a b : Nat) (h : G.Adj a b) : root a = root b := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (hex a) ((hr b).trans h.symm.reachable)
    · exact Nat.find_min' (hex b) ((hr a).trans h.reachable)
  let path (a : Nat) : G.Walk (root a) a := Classical.choice (hr a)
  let A (a : Nat) : ZMod 2 := g2WalkWeight w (path a)
  refine ⟨A, ?_⟩
  intro a b h
  have he := hroot a b h
  let q : G.Walk (root a) b := (path b).copy he.symm rfl
  have hq : g2WalkWeight w q = A b := by
    simp [q, A, g2WalkWeight]
  let loop : G.Walk (root a) (root a) :=
    (path a).append ((SimpleGraph.Walk.cons h SimpleGraph.Walk.nil).append q.reverse)
  have hz := hclosed (root a) loop
  change g2WalkWeight w ((path a).append
    ((SimpleGraph.Walk.cons h SimpleGraph.Walk.nil).append q.reverse)) = 0 at hz
  rw [g2WalkWeight_append, g2WalkWeight_append, g2WalkWeight_reverse w hsym,
    g2WalkWeight_cons, hq] at hz
  change A a + (w a b + 0 + A b) = 0 at hz
  calc
    w a b = (A a + (w a b + 0 + A b)) + (A a + A b) := by
      symm
      calc
        _ = w a b + ((A a + A a) + (A b + A b)) := by abel
        _ = w a b := by simp only [CharTwo.add_self_eq_zero, add_zero]
    _ = A a + A b := by rw [hz, zero_add]

/-- Actual link cocycles are vertex coboundaries on represented link edges. -/
theorem g2_vertex_link_cocycle_exact_candidate
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v : Nat} (hv : v ∈ vertexSupport K)
    (w : Nat → Nat → ZMod 2)
    (hzero : ∀ a, w a a = 0)
    (hsym : ∀ a b, w a b = w b a)
    (htri : ∀ s : LinkTriangle, s ∈ vertexLinkTriangles K v →
      ∀ a b c : Nat, a ∈ s.verts → b ∈ s.verts → c ∈ s.verts →
      w a b + w b c + w c a = 0) :
    ∃ A : Nat → ZMod 2, ∀ s ∈ vertexLinkTriangles K v,
      ∀ a b, a ∈ s.verts → b ∈ s.verts → w a b = A a + A b := by
  let G : SimpleGraph Nat := {
    Adj := fun a b => a ≠ b ∧ ∃ s ∈ vertexLinkTriangles K v,
      a ∈ s.verts ∧ b ∈ s.verts
    symm := by
      intro a b h
      obtain ⟨hne, s, hs, ha, hb⟩ := h
      exact ⟨hne.symm, s, hs, hb, ha⟩
    loopless := ⟨fun a h => h.1 rfl⟩ }
  have hc (a : Nat) (p : G.Walk a a) : g2WalkWeight w p = 0 := by
    rw [g2WalkWeight_eq_sum]
    by_cases hlen : p.length = 0
    · simp [hlen]
    refine g2_vertex_link_closed_walk_pairing_zero_candidate hcore hM hv
      w hzero hsym htri p.length (Nat.pos_of_ne_zero hlen) p.getVert ?_ ?_ ?_
    · rw [p.getVert_length, p.getVert_zero]
    · intro k hk
      exact (p.adj_getVert_succ hk).ne
    · intro k hk
      exact (p.adj_getVert_succ hk).2
  obtain ⟨A, hA⟩ := g2_graph_potential_of_closed_walks_candidate G w hsym hc
  refine ⟨A, ?_⟩
  intro s hs a b ha hb
  by_cases hab : a = b
  · subst b
    rw [hzero, CharTwo.add_self_eq_zero]
  · exact hA a b ⟨hab, s, hs, ha, hb⟩

#print axioms g2_graph_potential_of_closed_walks_candidate
#print axioms g2_vertex_link_cocycle_exact_candidate

end Poincare
