import Poincare.Move23ClosedCorePreservation
import Poincare.Move32ClosedCorePreservation
import Poincare.Move41CombinatorialFoundation
import Mathlib.Tactic

namespace Poincare.DelayedInsertionAudit

universe u
variable {α : Type u}

def replace (K R A : α → Prop) : α → Prop :=
  fun t => (K t ∧ ¬ R t) ∨ A t

def StarLegal (K S C R : α → Prop) : Prop :=
  (∀ t, R t ↔ K t ∧ S t) ∧
  (∀ t, ¬ (K t ∧ C t))

theorem delayedInsertionCore
    (K N S C R A : α → Prop) (T : α)
    (hT : K T)
    (hFresh : ∀ t, N t → ¬ K t)
    (hAvoid : ∀ t, N t → ¬ R t ∧ ¬ A t)
    (hCover : S T → ∃ t, N t ∧ S t)
    (hComp : ¬ C T)
    (hAdd : ∀ t, A t → C t)
    (hLegal :
      StarLegal (replace K (fun t => t = T) N) S C R) :
    StarLegal K S C R ∧
      replace K R A T ∧
      (∀ t, N t → ¬ replace K R A t) ∧
      replace (replace K (fun t => t = T) N) R A =
        replace (replace K R A) (fun t => t = T) N := by
  have hsT : ¬ S T := by
    intro hs
    obtain ⟨t, hn, hst⟩ := hCover hs
    have hr : R t :=
      (hLegal.1 t).2 ⟨Or.inr hn, hst⟩
    exact (hAvoid t hn).1 hr
  have hRT : ¬ R T := by
    intro hr
    exact hsT ((hLegal.1 T).1 hr).2
  have hAT : ¬ A T :=
    fun ha => hComp (hAdd T ha)
  have hStar : StarLegal K S C R := by
    constructor
    · intro t
      have heq :
          R t ↔ ((K t ∧ ¬ t = T) ∨ N t) ∧ S t :=
        hLegal.1 t
      have hf : N t → ¬ K t := hFresh t
      have hr : N t → ¬ R t :=
        fun hn => (hAvoid t hn).1
      have hs : t = T → ¬ S t := by
        intro h
        subst t
        exact hsT
      tauto
    · intro t h
      apply hLegal.2 t
      refine ⟨?_, h.2⟩
      apply Or.inl
      refine ⟨h.1, ?_⟩
      intro ht
      subst t
      exact hComp h.2
  refine ⟨hStar, Or.inl ⟨hT, hRT⟩, ?_, ?_⟩
  · intro t hn
    have hf := hFresh t hn
    have ha := (hAvoid t hn).2
    change ¬ ((K t ∧ ¬ R t) ∨ A t)
    tauto
  · funext t
    apply propext
    have hnR : N t → ¬ R t :=
      fun hn => (hAvoid t hn).1
    have htA : t = T → ¬ A t := by
      intro ht
      subst t
      exact hAT
    change
      ((((K t ∧ ¬ t = T) ∨ N t) ∧ ¬ R t) ∨ A t) ↔
        ((((K t ∧ ¬ R t) ∨ A t) ∧ ¬ t = T) ∨ N t)
    tauto

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.delayedInsertionCore

namespace Poincare.DelayedInsertionAudit

def stellarFacets
    (T : Finset Nat) (v : Nat)
    (t : Finset Nat) : Prop :=
  ∃ a ∈ T, t = insert v (T.erase a)

theorem stellar_cover
    (T P : Finset Nat) (v : Nat)
    (hT : T.card = 4)
    (hP : P.card < 4)
    (hsub : P ⊆ T) :
    ∃ t, stellarFacets T v t ∧ P ⊆ t := by
  classical
  have hex : ∃ a, a ∈ T ∧ a ∉ P := by
    by_contra h
    have hTP : T ⊆ P := by
      intro a ha
      by_contra hn
      exact h ⟨a, ha, hn⟩
    have hc := Finset.card_le_card hTP
    omega
  obtain ⟨a, haT, haP⟩ := hex
  refine ⟨insert v (T.erase a), ⟨a, haT, rfl⟩, ?_⟩
  intro x hx
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_erase.mpr
  refine ⟨?_, hsub hx⟩
  intro he
  subst x
  exact haP hx

theorem stellar_commutation_small_simplices
    (K R A : Finset Nat → Prop)
    (T S C : Finset Nat)
    (v : Nat)
    (hT : K T)
    (hCard : T.card = 4)
    (hSCard : S.card < 4)
    (hCCard : C.card < 4)
    (hKFresh : ∀ t, K t → v ∉ t)
    (hSv : v ∉ S)
    (hCv : v ∉ C)
    (hR : ∀ t, R t → t ⊆ S ∪ C)
    (hA : ∀ t, A t → t ⊆ S ∪ C)
    (hAdd : ∀ t, A t → C ⊆ t)
    (hLegal :
      StarLegal
        (replace K (fun t => t = T)
          (stellarFacets T v))
        (fun t => S ⊆ t)
        (fun t => C ⊆ t)
        R) :
    StarLegal K
        (fun t => S ⊆ t)
        (fun t => C ⊆ t)
        R ∧
      replace K R A T ∧
      (∀ t, stellarFacets T v t →
        ¬ replace K R A t) ∧
      replace
        (replace K (fun t => t = T)
          (stellarFacets T v)) R A =
      replace
        (replace K R A)
        (fun t => t = T)
        (stellarFacets T v) := by
  classical

  have hvUnion : v ∉ S ∪ C := by
    intro hv
    rcases Finset.mem_union.mp hv with hs | hc
    · exact hSv hs
    · exact hCv hc

  have hvNew :
      ∀ t, stellarFacets T v t → v ∈ t := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := ht
    simp

  have hFresh :
      ∀ t, stellarFacets T v t → ¬ K t := by
    intro t hn hk
    exact hKFresh t hk (hvNew t hn)

  have hAvoid :
      ∀ t, stellarFacets T v t →
        ¬ R t ∧ ¬ A t := by
    intro t hn
    have hv := hvNew t hn
    constructor
    · intro hr
      exact hvUnion (hR t hr hv)
    · intro ha
      exact hvUnion (hA t ha hv)

  have hComp : ¬ C ⊆ T := by
    intro hc
    obtain ⟨t, hn, hct⟩ :=
      stellar_cover T C v hCard hCCard hc
    exact hLegal.2 t ⟨Or.inr hn, hct⟩

  exact delayedInsertionCore
    K
    (stellarFacets T v)
    (fun t => S ⊆ t)
    (fun t => C ⊆ t)
    R A T hT hFresh hAvoid
    (stellar_cover T S v hCard hSCard)
    hComp hAdd hLegal

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.stellar_cover
#print axioms Poincare.DelayedInsertionAudit.stellar_commutation_small_simplices

namespace Poincare.DelayedInsertionAudit

def FaceConnected (K : Finset Nat → Prop) : Prop :=
  ∀ Q : Finset Nat → Prop,
    (∃ t, K t ∧ Q t) →
    (∀ t u f : Finset Nat,
      K t → K u → Q t →
      f.card = 3 → f ⊆ t → f ⊆ u → Q u) →
    ∀ t, K t → Q t

def FaceAtMostTwo (K : Finset Nat → Prop) : Prop :=
  ∀ f t u r : Finset Nat,
    f.card = 3 →
    K t → K u → K r →
    f ⊆ t → f ⊆ u → f ⊆ r →
    t ≠ u → r = t ∨ r = u

def NoFiveBoundary (K : Finset Nat → Prop) : Prop :=
  ∀ U : Finset Nat, U.card = 5 →
    ¬ (∀ a ∈ U, K (U.erase a))

theorem noFiveBoundary_of_connected
    (K : Finset Nat → Prop)
    (hConn : FaceConnected K)
    (hTwo : FaceAtMostTwo K)
    (hLarge : ∀ U : Finset Nat, U.card = 5 →
      ∃ t, K t ∧ ¬ t ⊆ U) :
    NoFiveBoundary K := by
  classical
  intro U hU hBoundary

  let Q : Finset Nat → Prop :=
    fun t => ∃ a ∈ U, t = U.erase a

  have hstart : ∃ t, K t ∧ Q t := by
    have hp : 0 < U.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
    exact ⟨U.erase a, hBoundary a ha, a, ha, rfl⟩

  have hclosed :
      ∀ t u f : Finset Nat,
        K t → K u → Q t →
        f.card = 3 → f ⊆ t → f ⊆ u → Q u := by
    intro t u f ht hu hQt hf hft hfu
    obtain ⟨a, ha, rfl⟩ := hQt

    have hc : (U.erase a).card = 4 := by
      rw [Finset.card_erase_of_mem ha, hU]

    have hex : ∃ b, b ∈ U.erase a ∧ b ∉ f := by
      by_contra h
      have hsub : U.erase a ⊆ f := by
        intro b hb
        by_contra hbf
        exact h ⟨b, hb, hbf⟩
      have hle := Finset.card_le_card hsub
      omega

    obtain ⟨b, hb, hbf⟩ := hex
    have hbU := (Finset.mem_erase.mp hb).2

    have hfb : f ⊆ U.erase b := by
      intro x hx
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        subst x
        exact hbf hx
      · exact (Finset.mem_erase.mp (hft hx)).2

    have hne : U.erase a ≠ U.erase b := by
      intro he
      rw [he] at hb
      exact (Finset.mem_erase.mp hb).1 rfl

    rcases hTwo f (U.erase a) (U.erase b) u
        hf ht (hBoundary b hbU) hu
        hft hfb hfu hne with he | he
    · exact ⟨a, ha, he⟩
    · exact ⟨b, hbU, he⟩

  obtain ⟨t, ht, hout⟩ := hLarge U hU
  obtain ⟨a, ha, he⟩ :=
    hConn Q hstart hclosed t ht
  apply hout
  intro x hx
  rw [he] at hx
  exact (Finset.mem_erase.mp hx).2

theorem stellar_commutation_41
    (K : Finset Nat → Prop)
    (T C : Finset Nat)
    (v w : Nat)
    (hT : K T)
    (hTCard : T.card = 4)
    (hCCard : C.card = 4)
    (hFresh : ∀ t, K t → v ∉ t)
    (hvC : v ∉ C)
    (hvw : v ≠ w)
    (hwC : w ∉ C)
    (hNoBoundary : NoFiveBoundary K)
    (hLegal :
      StarLegal
        (replace K (fun t => t = T)
          (stellarFacets T v))
        (fun t => w ∈ t)
        (fun t => C ⊆ t)
        (stellarFacets C w)) :
    StarLegal K
        (fun t => w ∈ t)
        (fun t => C ⊆ t)
        (stellarFacets C w) ∧
      replace K (stellarFacets C w)
        (fun t => t = C) T ∧
      (∀ t, stellarFacets T v t →
        ¬ replace K (stellarFacets C w)
          (fun t => t = C) t) ∧
      replace
        (replace K (fun t => t = T)
          (stellarFacets T v))
        (stellarFacets C w)
        (fun t => t = C) =
      replace
        (replace K (stellarFacets C w)
          (fun t => t = C))
        (fun t => t = T)
        (stellarFacets T v) := by
  classical

  have hvNew :
      ∀ t, stellarFacets T v t → v ∈ t := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := ht
    simp

  have hAvoid :
      ∀ t, stellarFacets T v t →
        ¬ stellarFacets C w t ∧ ¬ t = C := by
    intro t ht
    have hv := hvNew t ht
    constructor
    · intro hr
      obtain ⟨a, ha, rfl⟩ := hr
      have hn : v ∉ insert w (C.erase a) := by
        simp [hvw, hvC]
      exact hn hv
    · intro he
      exact hvC (he ▸ hv)

  have hComp : ¬ C ⊆ T := by
    intro hsub
    have heq : C = T :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    subst C

    let U := insert w T
    have hU : U.card = 5 := by
      simp [U, hwC, hTCard]

    apply hNoBoundary U hU
    intro a ha
    by_cases haw : a = w
    · subst a
      simpa [U, hwC] using hT
    · have haT : a ∈ T := by
        simpa [U, haw] using ha
      let r := insert w (T.erase a)
      have hr : stellarFacets T w r :=
        ⟨a, haT, rfl⟩

      have hk := ((hLegal.1 r).1 hr).1

      have hvnot : v ∉ r := by
        simp [r, hvw, hvC]

      have hrK : K r := by
        change (K r ∧ ¬ r = T) ∨
          stellarFacets T v r at hk
        rcases hk with h | h
        · exact h.1
        · exact False.elim (hvnot (hvNew r h))

      have herase : U.erase a = r := by
        ext x
        simp only [U, r, Finset.mem_erase,
          Finset.mem_insert]
        have hx : x = w → x ≠ a := by
          intro h
          subst x
          exact Ne.symm haw
        tauto

      rw [herase]
      exact hrK

  have hCover :
      w ∈ T → ∃ t, stellarFacets T v t ∧ w ∈ t := by
    intro hw
    have hs : ({w} : Finset Nat) ⊆ T := by
      intro x hx
      have he : x = w := by simpa using hx
      simpa [he] using hw
    obtain ⟨t, ht, hst⟩ :=
      stellar_cover T {w} v hTCard (by simp) hs
    exact ⟨t, ht, hst (by simp)⟩

  exact delayedInsertionCore
    K
    (stellarFacets T v)
    (fun t => w ∈ t)
    (fun t => C ⊆ t)
    (stellarFacets C w)
    (fun t => t = C)
    T hT
    (fun t ht hk => hFresh t hk (hvNew t ht))
    hAvoid hCover hComp
    (by
      intro t ht
      subst t
      exact fun _ h => h)
    hLegal

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.noFiveBoundary_of_connected
#print axioms Poincare.DelayedInsertionAudit.stellar_commutation_41

namespace Poincare.DelayedInsertionAudit

theorem stellar_center_mem
    (T t : Finset Nat) (v : Nat)
    (h : stellarFacets T v t) :
    v ∈ t := by
  obtain ⟨a, ha, rfl⟩ := h
  simp

theorem independent_insertions_commute
    (K : Finset Nat → Prop)
    (T U : Finset Nat)
    (v w : Nat)
    (hT : K T)
    (hTCard : T.card = 4)
    (hVFresh : ∀ t, K t → v ∉ t)
    (hU :
      replace K (fun t => t = T)
        (stellarFacets T v) U)
    (hUv : v ∉ U)
    (hWFresh :
      ∀ t,
        replace K (fun t => t = T)
          (stellarFacets T v) t →
        w ∉ t) :
    K U ∧
    U ≠ T ∧
    v ≠ w ∧
    (∀ t, K t → w ∉ t) ∧
    replace K (fun t => t = U)
      (stellarFacets U w) T ∧
    (∀ t,
      replace K (fun t => t = U)
        (stellarFacets U w) t →
      v ∉ t) ∧
    replace
      (replace K (fun t => t = T)
        (stellarFacets T v))
      (fun t => t = U)
      (stellarFacets U w) =
    replace
      (replace K (fun t => t = U)
        (stellarFacets U w))
      (fun t => t = T)
      (stellarFacets T v) := by
  classical

  have hUold : K U ∧ U ≠ T := by
    rcases hU with h | h
    · exact h
    · exact False.elim
        (hUv (stellar_center_mem T U v h))

  have hTneU : T ≠ U :=
    Ne.symm hUold.2

  have hvw : v ≠ w := by
    intro he
    have hp : 0 < T.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hp

    let t := insert v (T.erase a)

    have hn : stellarFacets T v t :=
      ⟨a, ha, rfl⟩

    have hv : v ∈ t :=
      stellar_center_mem T t v hn

    have hw : w ∈ t := by
      rw [← he]
      exact hv

    exact hWFresh t (Or.inr hn) hw

  have hwOld : ∀ t, K t → w ∉ t := by
    intro t ht hw
    by_cases he : t = T
    · subst t
      have hsub : ({w} : Finset Nat) ⊆ T := by
        intro x hx
        have hxw : x = w := by simpa using hx
        simpa [hxw] using hw

      obtain ⟨r, hr, hwr⟩ :=
        stellar_cover T {w} v hTCard
          (by simp) hsub

      exact hWFresh r (Or.inr hr)
        (hwr (by simp))

    · exact hWFresh t (Or.inl ⟨ht, he⟩) hw

  have hTsurvives :
      replace K (fun t => t = U)
        (stellarFacets U w) T :=
    Or.inl ⟨hT, hTneU⟩

  have hvAfter :
      ∀ t,
        replace K (fun t => t = U)
          (stellarFacets U w) t →
        v ∉ t := by
    intro t ht
    rcases ht with h | h
    · exact hVFresh t h.1
    · obtain ⟨a, ha, rfl⟩ := h
      simp [hvw, hUv]

  refine ⟨hUold.1, hUold.2, hvw,
    hwOld, hTsurvives, hvAfter, ?_⟩

  funext t
  apply propext

  have hnU :
      stellarFacets T v t → t ≠ U := by
    intro hn he
    subst t
    exact hUv (stellar_center_mem T U v hn)

  have hmT :
      stellarFacets U w t → t ≠ T := by
    intro hm he
    subst t
    exact hwOld T hT
      (stellar_center_mem U T w hm)

  change
    ((((K t ∧ ¬ t = T) ∨
      stellarFacets T v t) ∧ ¬ t = U) ∨
      stellarFacets U w t) ↔
    ((((K t ∧ ¬ t = U) ∨
      stellarFacets U w t) ∧ ¬ t = T) ∨
      stellarFacets T v t)

  tauto

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.stellar_center_mem
#print axioms Poincare.DelayedInsertionAudit.independent_insertions_commute

namespace Poincare.DelayedInsertionAudit

def facetFamily (L : List Tet)
    (q : Finset Nat) : Prop :=
  ∃ t ∈ L, t.verts.toFinset = q

theorem sameTetVertices_iff_finset
    (a b : Tet) :
    SameTetVertices a b ↔
      a.verts.toFinset = b.verts.toFinset := by
  constructor
  · intro h
    ext x
    simpa using h x
  · intro h x
    have hx := Finset.ext_iff.mp h x
    simpa using hx

theorem facetFamily_nil (q : Finset Nat) :
    ¬ facetFamily [] q := by
  simp [facetFamily]

theorem facetFamily_cons
    (a : Tet) (L : List Tet) (q : Finset Nat) :
    facetFamily (a :: L) q ↔
      q = a.verts.toFinset ∨ facetFamily L q := by
  constructor
  · rintro ⟨t, ht, he⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Or.inl he.symm
    · exact Or.inr ⟨t, ht, he⟩
  · rintro (rfl | ⟨t, ht, he⟩)
    · exact ⟨a, by simp, rfl⟩
    · exact ⟨t, by simp [ht], he⟩

theorem facetFamily_erase
    (target : Tet) (L : List Tet)
    (h : L.Pairwise
      (fun a b => ¬ SameTetVertices a b))
    (q : Finset Nat) :
    facetFamily (eraseFirstSameTet target L) q ↔
      facetFamily L q ∧
        q ≠ target.verts.toFinset := by
  induction L with
  | nil =>
      simp [eraseFirstSameTet, facetFamily]
  | cons a L ih =>
      have hp := List.pairwise_cons.mp h

      by_cases he : SameTetVertices a target

      · have hb :
            sameTetVerticesBool a target = true :=
          (sameTetVerticesBool_eq_true_iff a target).2 he

        have hEq :=
          (sameTetVertices_iff_finset a target).1 he

        have hnot :
            ¬ facetFamily L target.verts.toFinset := by
          rintro ⟨t, ht, hq⟩
          apply hp.1 t ht
          apply (sameTetVertices_iff_finset a t).2
          exact hEq.trans hq.symm

        have hErase :
            eraseFirstSameTet target (a :: L) = L := by
          simp [eraseFirstSameTet, hb]

        rw [hErase, facetFamily_cons]

        constructor
        · intro hq
          refine ⟨Or.inr hq, ?_⟩
          intro hh
          exact hnot (hh ▸ hq)
        · rintro ⟨hq, hne⟩
          rcases hq with ha | hq
          · exact (hne (ha.trans hEq)).elim
          · exact hq

      · have hb :
            sameTetVerticesBool a target = false := by
          cases hh : sameTetVerticesBool a target with
          | false => rfl
          | true =>
              exact
                (he ((sameTetVerticesBool_eq_true_iff
                  a target).1 hh)).elim

        have hne :
            a.verts.toFinset ≠ target.verts.toFinset :=
          fun heq =>
            he ((sameTetVertices_iff_finset a target).2 heq)

        have hErase :
            eraseFirstSameTet target (a :: L) =
              a :: eraseFirstSameTet target L := by
          simp [eraseFirstSameTet, hb]

        rw [hErase]
        simp only [facetFamily_cons, ih hp.2]

        have hqne :
            q = a.verts.toFinset →
              q ≠ target.verts.toFinset := by
          intro hqa hqt
          exact hne (hqa.symm.trans hqt)

        tauto

theorem move23_family_replace
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (s : Move23Site) :
    facetFamily (s.replace K).tets =
      replace
        (facetFamily K.tets)
        (facetFamily [s.leftTet, s.rightTet])
        (facetFamily
          [s.newTet₀, s.newTet₁, s.newTet₂]) := by
  have h0 := hcore.2.1
  have h1 := h0.sublist
    (eraseFirstSameTet_sublist s.leftTet K.tets)

  funext q
  apply propext

  simp only [
    Move23Site.replace_tets_eq,
    Move23Site.unchangedTets,
    replace,
    facetFamily_cons,
    facetFamily_nil,
    facetFamily_erase _ _ h1,
    facetFamily_erase _ _ h0
  ]

  tauto

theorem move32_family_replace
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site) :
    facetFamily (s.replace K).tets =
      replace
        (facetFamily K.tets)
        (facetFamily
          [s.targetTet₀, s.targetTet₁, s.targetTet₂])
        (facetFamily [s.sourceTet₀, s.sourceTet₁]) := by
  have h0 := hcore.2.1
  have h1 := h0.sublist
    (eraseFirstSameTet_sublist s.targetTet₀ K.tets)
  have h2 := h1.sublist
    (eraseFirstSameTet_sublist s.targetTet₁
      (eraseFirstSameTet s.targetTet₀ K.tets))

  funext q
  apply propext

  simp only [
    Move32Site.replace_tets_eq,
    Move32Site.unchangedTets,
    replace,
    facetFamily_cons,
    facetFamily_nil,
    facetFamily_erase _ _ h2,
    facetFamily_erase _ _ h1,
    facetFamily_erase _ _ h0
  ]

  tauto

theorem move41_family_replace
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (s : Move41Site) :
    facetFamily (s.replace K).tets =
      replace
        (facetFamily K.tets)
        (facetFamily s.sourceTets)
        (facetFamily [s.targetTet]) := by
  have h0 := hcore.2.1
  have h1 := h0.sublist
    (eraseFirstSameTet_sublist s.sourceTet₀ K.tets)
  have h2 := h1.sublist
    (eraseFirstSameTet_sublist s.sourceTet₁
      (eraseFirstSameTet s.sourceTet₀ K.tets))
  have h3 := h2.sublist
    (eraseFirstSameTet_sublist s.sourceTet₂
      (eraseFirstSameTet s.sourceTet₁
        (eraseFirstSameTet s.sourceTet₀ K.tets)))

  funext q
  apply propext

  simp only [
    Move41Site.replace,
    Move41Site.unchangedTets,
    Move41Site.sourceTets,
    replace,
    facetFamily_cons,
    facetFamily_nil,
    facetFamily_erase _ _ h3,
    facetFamily_erase _ _ h2,
    facetFamily_erase _ _ h1,
    facetFamily_erase _ _ h0
  ]

  tauto

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.sameTetVertices_iff_finset
#print axioms Poincare.DelayedInsertionAudit.facetFamily_nil
#print axioms Poincare.DelayedInsertionAudit.facetFamily_cons
#print axioms Poincare.DelayedInsertionAudit.facetFamily_erase
#print axioms Poincare.DelayedInsertionAudit.move23_family_replace
#print axioms Poincare.DelayedInsertionAudit.move32_family_replace
#print axioms Poincare.DelayedInsertionAudit.move41_family_replace

namespace Poincare.DelayedInsertionAudit

theorem family_witness
    {L M : List Tet}
    (h : facetFamily L = facetFamily M)
    {t : Tet} (ht : t ∈ L) :
    ∃ u ∈ M, SameTetVertices t u := by
  have hf : facetFamily L t.verts.toFinset :=
    ⟨t, ht, rfl⟩
  rw [h] at hf
  obtain ⟨u, hu, he⟩ := hf
  exact ⟨u, hu,
    (sameTetVertices_iff_finset t u).2 he.symm⟩

theorem family_exists_iff
    {L M : List Tet}
    (h : facetFamily L = facetFamily M)
    (p : Tet → Prop)
    (hinv : ∀ a b, SameTetVertices a b →
      (p a ↔ p b)) :
    (∃ t ∈ L, p t) ↔ (∃ t ∈ M, p t) := by
  constructor
  · rintro ⟨t, ht, hp⟩
    obtain ⟨u, hu, hs⟩ := family_witness h ht
    exact ⟨u, hu, (hinv t u hs).1 hp⟩
  · rintro ⟨t, ht, hp⟩
    obtain ⟨u, hu, hs⟩ :=
      family_witness h.symm ht
    exact ⟨u, hu, (hinv t u hs).1 hp⟩

theorem family_forall_iff
    {L M : List Tet}
    (h : facetFamily L = facetFamily M)
    (p : Tet → Prop)
    (hinv : ∀ a b, SameTetVertices a b →
      (p a ↔ p b)) :
    (∀ t ∈ L, p t) ↔ (∀ t ∈ M, p t) := by
  constructor
  · intro hp t ht
    obtain ⟨u, hu, hs⟩ :=
      family_witness h.symm ht
    exact (hinv t u hs).2 (hp u hu)
  · intro hp t ht
    obtain ⟨u, hu, hs⟩ :=
      family_witness h ht
    exact (hinv t u hs).2 (hp u hu)

theorem same_match_congr
    {a b : Tet}
    (h : SameTetVertices a b)
    (target : Tet) :
    SameTetVertices a target ↔
      SameTetVertices b target := by
  constructor
  · intro ha
    exact sameTetVertices_trans
      (sameTetVertices_symm h) ha
  · intro hb
    exact sameTetVertices_trans h hb

theorem facetMap_nodup
    (L : List Tet)
    (h : L.Pairwise
      (fun a b => ¬ SameTetVertices a b)) :
    (L.map (fun t => t.verts.toFinset)).Nodup := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have hp := List.pairwise_cons.mp h
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hp.2⟩
      intro hm
      obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
      exact hp.1 t ht
        ((sameTetVertices_iff_finset a t).2 he.symm)

theorem family_length_eq
    {L M : List Tet}
    (h : facetFamily L = facetFamily M)
    (hL : L.Pairwise
      (fun a b => ¬ SameTetVertices a b))
    (hM : M.Pairwise
      (fun a b => ¬ SameTetVertices a b)) :
    L.length = M.length := by
  classical
  have hs :
      (L.map (fun t => t.verts.toFinset)).toFinset =
      (M.map (fun t => t.verts.toFinset)).toFinset := by
    ext q
    simp only [List.mem_toFinset, List.mem_map]
    change facetFamily L q ↔ facetFamily M q
    rw [h]

  have hc := congrArg Finset.card hs
  rw [
    List.toFinset_card_of_nodup
      (facetMap_nodup L hL),
    List.toFinset_card_of_nodup
      (facetMap_nodup M hM)
  ] at hc

  simpa using hc

theorem family_filter_eq
    {L M : List Tet}
    (h : facetFamily L = facetFamily M)
    (p : Tet → Bool)
    (hinv : ∀ a b, SameTetVertices a b →
      p a = p b) :
    facetFamily (L.filter p) =
      facetFamily (M.filter p) := by
  funext q
  apply propext
  constructor
  · rintro ⟨t, ht, hq⟩
    have ht' := List.mem_filter.mp ht
    obtain ⟨u, hu, hs⟩ :=
      family_witness h ht'.1
    have hp : p u = true := by
      rw [← hinv t u hs]
      exact ht'.2
    exact ⟨u, List.mem_filter.mpr ⟨hu, hp⟩,
      ((sameTetVertices_iff_finset t u).1 hs).symm.trans hq⟩
  · rintro ⟨t, ht, hq⟩
    have ht' := List.mem_filter.mp ht
    obtain ⟨u, hu, hs⟩ :=
      family_witness h.symm ht'.1
    have hp : p u = true := by
      rw [← hinv t u hs]
      exact ht'.2
    exact ⟨u, List.mem_filter.mpr ⟨hu, hp⟩,
      ((sameTetVertices_iff_finset t u).1 hs).symm.trans hq⟩

theorem family_filter_length_eq
    {L M : List Tet}
    (h : facetFamily L = facetFamily M)
    (hL : L.Pairwise
      (fun a b => ¬ SameTetVertices a b))
    (hM : M.Pairwise
      (fun a b => ¬ SameTetVertices a b))
    (p : Tet → Bool)
    (hinv : ∀ a b, SameTetVertices a b →
      p a = p b) :
    (L.filter p).length = (M.filter p).length := by
  apply family_length_eq (family_filter_eq h p hinv)
  · exact hL.sublist (by apply List.filter_sublist)
  · exact hM.sublist (by apply List.filter_sublist)

theorem sameTetVerticesBool_congr
    {a b : Tet}
    (h : SameTetVertices a b)
    (target : Tet) :
    sameTetVerticesBool a target =
      sameTetVerticesBool b target := by
  have he :
      sameTetVerticesBool a target = true ↔
        sameTetVerticesBool b target = true := by
    simp only [sameTetVerticesBool_eq_true_iff]
    exact same_match_congr h target
  cases ha : sameTetVerticesBool a target <;>
    cases hb : sameTetVerticesBool b target <;>
    simp_all

theorem move23_legal_family_iff
    {K L : Triangulation}
    (hK : ClosedTriangulationCore K)
    (hL : ClosedTriangulationCore L)
    (h : facetFamily K.tets = facetFamily L.tets)
    (s : Move23Site) :
    s.LegalIn K ↔ s.LegalIn L := by
  have hr (target : Tet) :=
    family_exists_iff h
      (fun t => SameTetVertices t target)
      (fun _ _ hs => same_match_congr hs target)

  have hc :=
    family_filter_length_eq h hK.2.1 hL.2.1
      (fun t => decide
        (s.a ∈ t.verts ∧
         s.b ∈ t.verts ∧
         s.c ∈ t.verts))
      (by
        intro a b hs
        simp [hs s.a, hs s.b, hs s.c])

  have ha :=
    family_forall_iff h
      (fun t => ¬
        (s.d ∈ t.verts ∧ s.e ∈ t.verts))
      (by
        intro a b hs
        simp [hs s.d, hs s.e])

  unfold Move23Site.LegalIn
    Move23Site.RealizedIn
    Move23Site.SharedFaceExactlyTwo
    Move23Site.NewEdgeAbsent

  rw [hr s.leftTet, hr s.rightTet, hc, ha]

theorem move32_legal_family_iff
    {K L : Triangulation}
    (hK : ClosedTriangulationCore K)
    (hL : ClosedTriangulationCore L)
    (h : facetFamily K.tets = facetFamily L.tets)
    (s : Move32Site) :
    s.LegalIn K ↔ s.LegalIn L := by
  have hr (target : Tet) :=
    family_exists_iff h
      (fun t => SameTetVertices t target)
      (fun _ _ hs => same_match_congr hs target)

  have hc :=
    family_filter_length_eq h hK.2.1 hL.2.1
      (fun t => decide
        (s.d ∈ t.verts ∧ s.e ∈ t.verts))
      (by
        intro a b hs
        simp [hs s.d, hs s.e])

  have ha :=
    family_forall_iff h
      (fun t => ¬
        (s.a ∈ t.verts ∧
         s.b ∈ t.verts ∧
         s.c ∈ t.verts))
      (by
        intro a b hs
        simp [hs s.a, hs s.b, hs s.c])

  unfold Move32Site.LegalIn
    Move32Site.RealizedIn
    Move32Site.SharedEdgeExactlyThree
    Move32Site.SourceFaceAbsent

  rw [hr s.targetTet₀, hr s.targetTet₁,
      hr s.targetTet₂, hc, ha]

theorem move41_legal_family_transfer
    {K L : Triangulation}
    {s : Move41Site}
    (hL : ClosedTriangulationCore L)
    (h : facetFamily K.tets = facetFamily L.tets)
    (hlegal : s.LegalIn K) :
    s.LegalIn L := by
  refine ⟨hL, ?_,
    hlegal.sourcePairwiseDistinct, ?_, ?_⟩

  · intro source hs
    have hc :=
      family_filter_length_eq h
        hlegal.closedCore.2.1 hL.2.1
        (fun t => sameTetVerticesBool t source)
        (fun _ _ he =>
          sameTetVerticesBool_congr he source)
    rw [← hc]
    exact hlegal.sourceOccursExactlyOnce source hs

  · intro t ht he
    obtain ⟨u, hu, hs⟩ :=
      family_witness h.symm ht
    obtain ⟨source, hsource, hm⟩ :=
      hlegal.centerSaturated u hu ((hs s.e).1 he)
    exact ⟨source, hsource,
      sameTetVertices_trans hs hm⟩

  · intro t ht hm
    obtain ⟨u, hu, hs⟩ :=
      family_witness h.symm ht
    exact hlegal.targetAbsent u hu
      (sameTetVertices_trans
        (sameTetVertices_symm hs) hm)

theorem move41_legal_family_iff
    {K L : Triangulation}
    (hK : ClosedTriangulationCore K)
    (hL : ClosedTriangulationCore L)
    (h : facetFamily K.tets = facetFamily L.tets)
    (s : Move41Site) :
    s.LegalIn K ↔ s.LegalIn L := by
  constructor
  · exact move41_legal_family_transfer hL h
  · exact move41_legal_family_transfer hK h.symm

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.family_witness
#print axioms Poincare.DelayedInsertionAudit.family_exists_iff
#print axioms Poincare.DelayedInsertionAudit.family_forall_iff
#print axioms Poincare.DelayedInsertionAudit.same_match_congr
#print axioms Poincare.DelayedInsertionAudit.facetMap_nodup
#print axioms Poincare.DelayedInsertionAudit.family_length_eq
#print axioms Poincare.DelayedInsertionAudit.family_filter_eq
#print axioms Poincare.DelayedInsertionAudit.family_filter_length_eq
#print axioms Poincare.DelayedInsertionAudit.sameTetVerticesBool_congr
#print axioms Poincare.DelayedInsertionAudit.move23_legal_family_iff
#print axioms Poincare.DelayedInsertionAudit.move32_legal_family_iff
#print axioms Poincare.DelayedInsertionAudit.move41_legal_family_transfer
#print axioms Poincare.DelayedInsertionAudit.move41_legal_family_iff

namespace Poincare.DelayedInsertionAudit

theorem move41_source_family_stellar
    (s : Move41Site) :
    facetFamily s.sourceTets =
      stellarFacets s.targetTet.verts.toFinset s.e := by
  classical

  let T := s.targetTet.verts.toFinset

  have hd := s.distinct
  simp at hd

  have h0 :
      s.sourceTet₀.verts.toFinset =
        insert s.e (T.erase s.d) := by
    ext x
    simp [T, Move41Site.targetTet,
      Move41Site.sourceTet₀, Tet.verts] ; aesop

  have h1 :
      s.sourceTet₁.verts.toFinset =
        insert s.e (T.erase s.c) := by
    ext x
    simp [T, Move41Site.targetTet,
      Move41Site.sourceTet₁, Tet.verts] ; aesop

  have h2 :
      s.sourceTet₂.verts.toFinset =
        insert s.e (T.erase s.b) := by
    ext x
    simp [T, Move41Site.targetTet,
      Move41Site.sourceTet₂, Tet.verts] ; aesop

  have h3 :
      s.sourceTet₃.verts.toFinset =
        insert s.e (T.erase s.a) := by
    ext x
    simp [T, Move41Site.targetTet,
      Move41Site.sourceTet₃, Tet.verts] ; aesop

  funext q
  apply propext

  change facetFamily s.sourceTets q ↔
    stellarFacets T s.e q

  simp only [
    Move41Site.sourceTets,
    facetFamily_cons,
    facetFamily_nil,
    or_false,
    h0, h1, h2, h3
  ]

  constructor
  · intro h
    rcases h with h | h | h | h
    · exact ⟨s.d,
        by simp [T, Move41Site.targetTet, Tet.verts], h⟩
    · exact ⟨s.c,
        by simp [T, Move41Site.targetTet, Tet.verts], h⟩
    · exact ⟨s.b,
        by simp [T, Move41Site.targetTet, Tet.verts], h⟩
    · exact ⟨s.a,
        by simp [T, Move41Site.targetTet, Tet.verts], h⟩

  · rintro ⟨a, ha, he⟩
    have ha' :
        a = s.a ∨ a = s.b ∨
        a = s.c ∨ a = s.d := by
      simpa [T, Move41Site.targetTet, Tet.verts] using ha

    rcases ha' with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inl he)
    · exact Or.inl he

theorem replace_singleton_inverse
    {α : Type*}
    (K R : α → Prop)
    (T : α)
    (hAbsent : ¬ K T)
    (hSource : ∀ t, R t → K t) :
    replace
      (replace K R (fun t => t = T))
      (fun t => t = T) R = K := by
  funext t
  apply propext

  have hs := hSource t

  have ht : t = T → ¬ K t := by
    intro h
    subst t
    exact hAbsent

  change
    ((((K t ∧ ¬ R t) ∨ t = T) ∧
      ¬ t = T) ∨ R t) ↔ K t

  tauto

theorem move41_source_family_subset
    {K : Triangulation}
    {s : Move41Site}
    (hlegal : s.LegalIn K) :
    ∀ q, facetFamily s.sourceTets q →
      facetFamily K.tets q := by
  intro q hq

  obtain ⟨source, hs, he⟩ := hq

  have hlen :=
    hlegal.sourceOccursExactlyOnce source hs

  have hn :
      K.tets.filter
        (fun t => sameTetVerticesBool t source) ≠ [] := by
    intro hempty
    simp [hempty] at hlen

  obtain ⟨t, ht⟩ :=
    List.exists_mem_of_ne_nil _ hn

  have ht' :
      t ∈ K.tets ∧ SameTetVertices t source := by
    simpa [sameTetVerticesBool_eq_true_iff] using ht

  exact ⟨t, ht'.1,
    ((sameTetVertices_iff_finset t source).1
      ht'.2).trans he⟩

theorem move41_inverse_stellar_family
    {K : Triangulation}
    {s : Move41Site}
    (hlegal : s.LegalIn K) :
    facetFamily (s.replace K).tets
      s.targetTet.verts.toFinset ∧
    (∀ q, facetFamily (s.replace K).tets q →
      s.e ∉ q) ∧
    facetFamily K.tets =
      replace
        (facetFamily (s.replace K).tets)
        (fun q => q = s.targetTet.verts.toFinset)
        (stellarFacets s.targetTet.verts.toFinset s.e) := by

  let T := s.targetTet.verts.toFinset

  have hAbsent : ¬ facetFamily K.tets T := by
    rintro ⟨t, ht, he⟩
    exact hlegal.targetAbsent t ht
      ((sameTetVertices_iff_finset t s.targetTet).2 he)

  have hSource :
      ∀ q, facetFamily s.sourceTets q →
        facetFamily K.tets q :=
    move41_source_family_subset hlegal

  have hTarget :
      facetFamily [s.targetTet] =
        (fun q => q = T) := by
    funext q
    apply propext
    simp only [
      facetFamily_cons,
      facetFamily_nil,
      or_false,
      T
    ]

  have hr :=
    move41_family_replace K hlegal.closedCore s

  rw [hTarget] at hr

  refine ⟨?_, ?_, ?_⟩

  · exact ⟨s.targetTet,
      by simp [Move41Site.replace], rfl⟩

  · intro q hq he
    obtain ⟨t, ht, htq⟩ := hq

    have he' : s.e ∈ t.verts := by
      apply List.mem_toFinset.mp
      rw [htq]
      exact he

    apply Move41Site.center_not_mem_vertexSupport_replace
      hlegal

    rw [mem_vertexSupport_iff]

    exact List.mem_flatMap.mpr ⟨t, ht, he'⟩

  · change facetFamily K.tets =
      replace
        (facetFamily (s.replace K).tets)
        (fun q => q = T)
        (stellarFacets T s.e)

    have hstellar :
        facetFamily s.sourceTets =
          stellarFacets T s.e :=
      move41_source_family_stellar s

    rw [hr, ← hstellar]

    exact
      (replace_singleton_inverse
        (facetFamily K.tets)
        (facetFamily s.sourceTets)
        T hAbsent hSource).symm

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.move41_source_family_stellar
#print axioms Poincare.DelayedInsertionAudit.replace_singleton_inverse
#print axioms Poincare.DelayedInsertionAudit.move41_source_family_subset
#print axioms Poincare.DelayedInsertionAudit.move41_inverse_stellar_family


namespace Poincare

/-!
# Canonical head-tetrahedron stellar subdivision

This module constructs the four actual `Tet` records of a 1→4 stellar
subdivision in the repository's list representation. The canonical 4→1
replacement recovers the original list *exactly*, not merely as an unordered
set. Freshness of the new center in the unchanged exterior certifies that
its complete tetrahedron star lies in the four inserted tetrahedra.

The subdivision preserves the closed core and certifies a `1 → 4` step
when the center is fresh in the unchanged tetrahedra.
-/

/-- Four distinct source tetrahedra in the order that the repository's
`Move41Site.unchangedTets` algorithm erases them. -/
def Move41Site.headStellar (s : Move41Site) (rest : List Tet) : Triangulation :=
  { tets := s.sourceTet₀ :: s.sourceTet₁ :: s.sourceTet₂ :: s.sourceTet₃ :: rest }

/-- The canonical 4→1 replacement of the explicit head subdivision recovers
the original tetrahedron list, with its ordering unchanged. -/
theorem Move41Site.replace_headStellar_exact
    (s : Move41Site) (rest : List Tet) :
    s.replace (s.headStellar rest) =
      { tets := s.targetTet :: rest } := by
  have hself (τ : Tet) : sameTetVerticesBool τ τ = true :=
    (sameTetVerticesBool_eq_true_iff τ τ).2 (fun _ => Iff.rfl)
  simp [Move41Site.replace, Move41Site.unchangedTets,
    Move41Site.headStellar, eraseFirstSameTet, hself]

/-- If the center vertex is absent from the unchanged exterior, every
tetrahedron containing it in the constructed subdivision belongs to
the four-tetrahedron stellar star. No closed-core claim is used. -/
theorem Move41Site.headStellar_center_saturated
    (s : Move41Site) (rest : List Tet)
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    ∀ τ ∈ (s.headStellar rest).tets,
      s.e ∈ τ.verts →
      ∃ ρ ∈ s.sourceTets, SameTetVertices τ ρ := by
  intro τ hmem hcenter
  simp only [Move41Site.headStellar, List.mem_cons] at hmem
  rcases hmem with h0 | h1 | h2 | h3 | hrest
  · subst τ
    exact ⟨s.sourceTet₀, by simp [Move41Site.sourceTets], fun _ => Iff.rfl⟩
  · subst τ
    exact ⟨s.sourceTet₁, by simp [Move41Site.sourceTets], fun _ => Iff.rfl⟩
  · subst τ
    exact ⟨s.sourceTet₂, by simp [Move41Site.sourceTets], fun _ => Iff.rfl⟩
  · subst τ
    exact ⟨s.sourceTet₃, by simp [Move41Site.sourceTets], fun _ => Iff.rfl⟩
  · exact False.elim ((hfresh τ hrest) hcenter)

/-- The actual `Move41Site` for a subdivision of a specific tetrahedron
with an explicitly distinct new vertex. -/
def Tet.freshStellarSite
    (τ : Tet) (x : Nat)
    (hdist : [τ.v0, τ.v1, τ.v2, τ.v3, x].Nodup) : Move41Site :=
  { a := τ.v0, b := τ.v1, c := τ.v2, d := τ.v3, e := x,
    distinct := hdist }

@[simp] theorem Tet.freshStellarSite_target
    (τ : Tet) (x : Nat)
    (hdist : [τ.v0, τ.v1, τ.v2, τ.v3, x].Nodup) :
    (τ.freshStellarSite x hdist).targetTet = τ := by
  cases τ
  rfl

/-- An explicitly fresh subdivision of the first tetrahedron is an exact
predecessor of the original *list-valued* triangulation. -/
theorem Tet.freshHeadStellar_replace_exact
    (τ : Tet) (x : Nat)
    (hdist : [τ.v0, τ.v1, τ.v2, τ.v3, x].Nodup)
    (rest : List Tet) :
    (τ.freshStellarSite x hdist).replace
      ((τ.freshStellarSite x hdist).headStellar rest) =
      ({ tets := τ :: rest } : Triangulation) := by
  rw [Move41Site.replace_headStellar_exact]
  simp

private theorem Move41Site.sourceVertsNodup (s : Move41Site) :
    ∀ τ ∈ s.sourceTets, τ.verts.Nodup := by
  intro τ hτ
  have hd := s.distinct
  simp [Move41Site.sourceTets] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;>
    simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
      Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]

private theorem Move41Site.sourceCenter (s : Move41Site) :
    ∀ τ ∈ s.sourceTets, s.e ∈ τ.verts := by
  intro τ hτ
  simp [Move41Site.sourceTets] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;>
    simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
      Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]

theorem Move41Site.sourceDistinct (s : Move41Site) :
    s.sourceTets.Pairwise (fun τ σ => ¬ SameTetVertices τ σ) := by
  simp [Move41Site.sourceTets]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  all_goals intro h
  · have hc := h s.c
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₁, Tet.verts, eq_comm]
  · have hb := h s.b
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₂, Tet.verts, eq_comm]
  · have ha := h s.a
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₃, Tet.verts]
  · have hb := h s.b
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₁, Move41Site.sourceTet₂, Tet.verts, eq_comm]
  · have ha := h s.a
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₁, Move41Site.sourceTet₃, Tet.verts]
  · have ha := h s.a
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]

set_option maxHeartbeats 10000000 in
private theorem Move41Site.stellarLocalIncidence (s : Move41Site)
    (x y z : Nat) (hxyz : [x, y, z].Nodup)
    (hx : x ∈ [s.a, s.b, s.c, s.d, s.e])
    (hy : y ∈ [s.a, s.b, s.c, s.d, s.e])
    (hz : z ∈ [s.a, s.b, s.c, s.d, s.e]) :
    let p := fun τ : Tet => decide (x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts)
    if s.e ∈ [x, y, z] then (s.sourceTets.filter p).length = 2
    else (s.sourceTets.filter p).length = ([s.targetTet].filter p).length := by
  have hd := s.distinct
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Move41Site.sourceTets, Move41Site.sourceTet₀, Move41Site.sourceTet₁,
      Move41Site.sourceTet₂, Move41Site.sourceTet₃, Move41Site.targetTet, Tet.verts, eq_comm]

/-- Subdividing the head tetrahedron at a center fresh in the exterior
preserves nondegeneracy, distinct tetrahedra, and two-fold face incidence. -/
theorem Move41Site.headStellar_closedCore (s : Move41Site) (rest : List Tet)
    (hcore : ClosedTriangulationCore { tets := s.targetTet :: rest })
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    ClosedTriangulationCore (s.headStellar rest) := by
  change ClosedTriangulationCore { tets := s.sourceTets ++ rest }
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    rcases List.mem_append.mp hτ with hs | hr
    · exact s.sourceVertsNodup τ hs
    · exact hcore.1 τ (List.mem_cons_of_mem _ hr)
  · apply List.pairwise_append.mpr
    refine ⟨s.sourceDistinct, (List.pairwise_cons.mp hcore.2.1).2, ?_⟩
    intro τ hs σ hr hsame
    exact hfresh σ hr ((hsame s.e).mp (s.sourceCenter τ hs))
  · intro x y z hxyz hrepresented
    let p := fun τ : Tet => decide (x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts)
    change ((s.sourceTets ++ rest).filter p).length = 2
    have labels (τ : Tet) (hτ : τ ∈ s.targetTet :: s.sourceTets)
        (v : Nat) (hv : v ∈ τ.verts) : v ∈ [s.a, s.b, s.c, s.d, s.e] := by
      simp [Move41Site.sourceTets] at hτ
      rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
        simp [Move41Site.targetTet, Move41Site.sourceTet₀, Move41Site.sourceTet₁,
          Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts] at hv ⊢ <;> tauto
    have localTable (τ : Tet) (hτ : τ ∈ s.targetTet :: s.sourceTets)
        (hp : x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts) :
        if s.e ∈ [x, y, z] then (s.sourceTets.filter p).length = 2
        else (s.sourceTets.filter p).length = ([s.targetTet].filter p).length :=
      s.stellarLocalIncidence x y z hxyz
        (labels τ hτ x hp.1) (labels τ hτ y hp.2.1) (labels τ hτ z hp.2.2)
    rw [List.filter_append, List.length_append]
    by_cases he : s.e ∈ [x, y, z]
    · have noRest (τ : Tet) (hτ : τ ∈ rest) :
          ¬ (x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts) := by
        intro hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with h | h | h
        · exact hfresh τ hτ (h ▸ hp.1)
        · exact hfresh τ hτ (h ▸ hp.2.1)
        · exact hfresh τ hτ (h ▸ hp.2.2)
      have hrest : rest.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro τ hτ
        simp [p, noRest τ hτ]
      obtain ⟨τ, hτ, hp⟩ := hrepresented
      rcases List.mem_append.mp hτ with hs | hr
      · simpa [he, hrest] using localTable τ (List.mem_cons_of_mem _ hs) hp
      · exact (noRest τ hr hp).elim
    · have hcounts :
          (s.sourceTets.filter p).length = ([s.targetTet].filter p).length := by
        by_cases hlocal : ∃ τ ∈ s.targetTet :: s.sourceTets, p τ = true
        · obtain ⟨τ, hτ, hp⟩ := hlocal
          simpa [he] using localTable τ hτ (of_decide_eq_true hp)
        · have emptyFilter (L : List Tet) (hsub : ∀ τ ∈ L,
              τ ∈ s.targetTet :: s.sourceTets) : L.filter p = [] := by
            rw [List.filter_eq_nil_iff]
            intro τ hτ
            exact fun hp => hlocal ⟨τ, hsub τ hτ, hp⟩
          rw [emptyFilter s.sourceTets (fun τ hτ => List.mem_cons_of_mem _ hτ),
            emptyFilter [s.targetTet] (by simp)]
      have hold : ∃ τ ∈ s.targetTet :: rest,
          x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts := by
        obtain ⟨τ, hτ, hp⟩ := hrepresented
        rcases List.mem_append.mp hτ with hs | hr
        · have hmem : τ ∈ s.sourceTets.filter p :=
            List.mem_filter.mpr ⟨hs, decide_eq_true hp⟩
          have hpos := List.length_pos_iff_exists_mem.mpr ⟨τ, hmem⟩
          rw [hcounts] at hpos
          obtain ⟨σ, hσ⟩ := List.length_pos_iff_exists_mem.mp hpos
          obtain ⟨hσhead, hσp⟩ := List.mem_filter.mp hσ
          have hEq : σ = s.targetTet := by simpa using hσhead
          subst σ
          exact ⟨s.targetTet, by simp, of_decide_eq_true hσp⟩
        · exact ⟨τ, List.mem_cons_of_mem _ hr, hp⟩
      have htwo := hcore.2.2 x y z hxyz hold
      change (([s.targetTet] ++ rest).filter p).length = 2 at htwo
      rw [List.filter_append, List.length_append] at htwo
      rwa [hcounts]

private theorem filter_length_one_of_pairwise {α : Type} (p : α → Bool) (L : List α)
    (hpair : L.Pairwise (fun x y => ¬ (p x = true ∧ p y = true)))
    (hex : ∃ x ∈ L, p x = true) : (L.filter p).length = 1 := by
  induction L with
  | nil => simp at hex
  | cons x L ih =>
    obtain ⟨hx, hL⟩ := List.pairwise_cons.mp hpair
    cases hp : p x with
    | false =>
      apply (show (L.filter p).length = 1 → _ by simp [hp])
      apply ih hL
      simpa [hp] using hex
    | true =>
      have hnil : L.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        exact fun hpy => hx y hy ⟨hp, hpy⟩
      simp [hp, hnil]

/-- The canonical inverse is legal in the freshly subdivided core. -/
theorem Move41Site.headStellar_legal (s : Move41Site) (rest : List Tet)
    (hcore : ClosedTriangulationCore { tets := s.targetTet :: rest })
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    s.LegalIn (s.headStellar rest) := by
  have hnew := s.headStellar_closedCore rest hcore hfresh
  refine ⟨hnew, ?_, s.sourceDistinct, s.headStellar_center_saturated rest hfresh, ?_⟩
  · intro source hs
    apply filter_length_one_of_pairwise
    · apply hnew.2.1.imp
      intro τ σ hne hmatch
      have hτ := (sameTetVerticesBool_eq_true_iff τ source).mp hmatch.1
      have hσ := (sameTetVerticesBool_eq_true_iff σ source).mp hmatch.2
      exact hne (fun v => (hτ v).trans (hσ v).symm)
    · exact ⟨source, List.mem_append_left _ hs,
        (sameTetVerticesBool_eq_true_iff source source).mpr (fun _ => Iff.rfl)⟩
  · intro τ hτ hsame
    have hd := s.distinct
    have hnot : s.e ∉ s.targetTet.verts := by
      simp_all [Move41Site.targetTet, Tet.verts, eq_comm]
    change τ ∈ s.sourceTets ++ rest at hτ
    rcases List.mem_append.mp hτ with hs | hr
    · exact hnot ((hsame s.e).mp (s.sourceCenter τ hs))
    · exact (List.pairwise_cons.mp hcore.2.1).1 τ hr (sameTetVertices_symm hsame)


end Poincare

#print axioms Poincare.Move41Site.replace_headStellar_exact
#print axioms Poincare.Move41Site.headStellar_closedCore
#print axioms Poincare.Move41Site.headStellar_legal

namespace Poincare.DelayedInsertionAudit

theorem split_list_at_member
    {α : Type*}
    (L : List α) (a : α)
    (ha : a ∈ L) :
    ∃ before after, L = before ++ a :: after := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
      rcases List.mem_cons.mp ha with he | ht
      · subst b
        exact ⟨[], L, rfl⟩
      · obtain ⟨before, after, h⟩ := ih ht
        exact ⟨b :: before, after,
          by simp [h]⟩

theorem family_eq_of_perm
    {L M : List Tet}
    (h : L.Perm M) :
    facetFamily L = facetFamily M := by
  funext q
  apply propext
  constructor
  · rintro ⟨t, ht, he⟩
    exact ⟨t, h.mem_iff.mp ht, he⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨t, h.mem_iff.mpr ht, he⟩

theorem core_of_list_perm
    {K L : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hperm : K.tets.Perm L.tets) :
    ClosedTriangulationCore L := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact hcore.1 t (hperm.mem_iff.mpr ht)
  · exact hcore.2.1.perm hperm (by
      intro t u hnot hsame
      exact hnot (sameTetVertices_symm hsame))
  · intro a b c habc hrep
    obtain ⟨t, ht, hp⟩ := hrep
    have hrepK :
        ∃ t ∈ K.tets,
          a ∈ t.verts ∧
          b ∈ t.verts ∧
          c ∈ t.verts :=
      ⟨t, hperm.mem_iff.mpr ht, hp⟩
    have hcounts :=
      (hperm.filter (fun t : Tet =>
        decide (a ∈ t.verts ∧
          b ∈ t.verts ∧
          c ∈ t.verts))).length_eq
    exact hcounts.symm.trans
      (hcore.2.2 a b c habc hrepK)

theorem arbitrary_stellar_insertion_exists
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (T : Finset Nat) (v : Nat)
    (hT : facetFamily K.tets T)
    (hfresh :
      ∀ q, facetFamily K.tets q → v ∉ q) :
    ∃ (J : Triangulation) (s : Move41Site),
      s.LegalIn J ∧
      facetFamily (s.replace J).tets =
        facetFamily K.tets ∧
      s.targetTet.verts.toFinset = T ∧
      s.e = v ∧
      facetFamily J.tets =
        replace
          (facetFamily K.tets)
          (fun q => q = T)
          (stellarFacets T v) := by
  classical

  obtain ⟨t, ht, htT⟩ := hT

  have hn := hcore.1 t ht

  have hv : v ∉ t.verts := by
    intro hv
    exact hfresh t.verts.toFinset
      ⟨t, ht, rfl⟩
      (List.mem_toFinset.mpr hv)

  have hd :
      [t.v0, t.v1, t.v2, t.v3, v].Nodup := by
    simp [Tet.verts] at hn hv ⊢
    aesop

  obtain ⟨before, after, hsplit⟩ :=
    split_list_at_member K.tets t ht

  let rest := before ++ after
  let s := t.freshStellarSite v hd

  have htarget : s.targetTet = t := by
    simp [s]

  have hcenter : s.e = v := rfl

  let H : Triangulation :=
    { tets := s.targetTet :: rest }

  have hperm : K.tets.Perm H.tets := by
    change K.tets.Perm
      (s.targetTet :: (before ++ after))
    rw [hsplit, htarget]
    exact List.perm_middle

  have hheadCore : ClosedTriangulationCore H :=
    core_of_list_perm hcore hperm

  have hfreshRest :
      ∀ u ∈ rest, s.e ∉ u.verts := by
    intro u hu he

    have huH : u ∈ H.tets :=
      List.mem_cons_of_mem _ hu

    have huK := hperm.mem_iff.mpr huH

    apply hfresh u.verts.toFinset
      ⟨u, huK, rfl⟩

    apply List.mem_toFinset.mpr

    simpa [hcenter] using he

  let J := s.headStellar rest

  have hlegal : s.LegalIn J :=
    s.headStellar_legal rest hheadCore hfreshRest

  have hrecovery : s.replace J = H :=
    s.replace_headStellar_exact rest

  have hfamily :
      facetFamily (s.replace J).tets =
        facetFamily K.tets := by
    rw [hrecovery]
    exact (family_eq_of_perm hperm).symm

  have htargetFamily :
      s.targetTet.verts.toFinset = T :=
    (congrArg
      (fun u : Tet => u.verts.toFinset)
      htarget).trans htT

  refine ⟨J, s, hlegal, hfamily,
    htargetFamily, hcenter, ?_⟩

  have hinv :=
    (move41_inverse_stellar_family hlegal).2.2

  rw [hfamily, htargetFamily, hcenter] at hinv
  exact hinv

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.split_list_at_member
#print axioms Poincare.DelayedInsertionAudit.family_eq_of_perm
#print axioms Poincare.DelayedInsertionAudit.core_of_list_perm
#print axioms Poincare.DelayedInsertionAudit.arbitrary_stellar_insertion_exists

namespace Poincare.DelayedInsertionAudit

theorem starLegal_of_exact_sources
    (K : Triangulation)
    (S C : Finset Nat)
    (R : List Tet)
    (hReal : ∀ r ∈ R,
      ∃ t ∈ K.tets, SameTetVertices t r)
    (hContains : ∀ r ∈ R,
      S ⊆ r.verts.toFinset)
    (hSat : ∀ t ∈ K.tets,
      S ⊆ t.verts.toFinset →
      ∃ r ∈ R, SameTetVertices t r)
    (hAbsent : ∀ t ∈ K.tets,
      ¬ C ⊆ t.verts.toFinset) :
    StarLegal
      (facetFamily K.tets)
      (fun q => S ⊆ q)
      (fun q => C ⊆ q)
      (facetFamily R) := by
  constructor
  · intro q
    constructor
    · rintro ⟨r, hr, he⟩
      obtain ⟨t, ht, hs⟩ := hReal r hr
      refine ⟨⟨t, ht, ?_⟩, ?_⟩
      · exact
          ((sameTetVertices_iff_finset t r).1 hs).trans he
      · rw [← he]
        exact hContains r hr
    · rintro ⟨⟨t, ht, he⟩, hq⟩
      have hs : S ⊆ t.verts.toFinset := by
        rw [he]
        exact hq
      obtain ⟨r, hr, hm⟩ := hSat t ht hs
      exact ⟨r, hr,
        ((sameTetVertices_iff_finset t r).1 hm).symm.trans he⟩
  · rintro q ⟨⟨t, ht, he⟩, hc⟩
    apply hAbsent t ht
    rw [he]
    exact hc

theorem starLegal_source_realized
    {K : Triangulation}
    {S C : Finset Nat}
    {R : List Tet}
    (h : StarLegal
      (facetFamily K.tets)
      (fun q => S ⊆ q)
      (fun q => C ⊆ q)
      (facetFamily R))
    {r : Tet}
    (hr : r ∈ R) :
    ∃ t ∈ K.tets, SameTetVertices t r := by
  have hmem : facetFamily R r.verts.toFinset :=
    ⟨r, hr, rfl⟩
  obtain ⟨t, ht, he⟩ :=
    ((h.1 r.verts.toFinset).1 hmem).1
  exact ⟨t, ht,
    (sameTetVertices_iff_finset t r).2 he⟩

theorem starLegal_filtered_family
    (K : Triangulation)
    (S C : Finset Nat)
    (R : List Tet)
    (p : Tet → Bool)
    (hp : ∀ t, p t = true ↔ S ⊆ t.verts.toFinset)
    (h : StarLegal
      (facetFamily K.tets)
      (fun q => S ⊆ q)
      (fun q => C ⊆ q)
      (facetFamily R)) :
    facetFamily (K.tets.filter p) = facetFamily R := by
  funext q
  apply propext
  rw [h.1 q]
  constructor
  · rintro ⟨t, ht, he⟩
    obtain ⟨htK, hpt⟩ := List.mem_filter.mp ht
    refine ⟨⟨t, htK, he⟩, ?_⟩
    rw [← he]
    exact (hp t).1 hpt
  · rintro ⟨⟨t, ht, he⟩, hs⟩
    have hpt : p t = true := by
      apply (hp t).2
      rw [he]
      exact hs
    exact ⟨t, List.mem_filter.mpr ⟨ht, hpt⟩, he⟩

theorem starLegal_count_eq
    {K J : Triangulation}
    (hK : ClosedTriangulationCore K)
    (hJ : ClosedTriangulationCore J)
    (S C : Finset Nat)
    (R : List Tet)
    (p : Tet → Bool)
    (hp : ∀ t, p t = true ↔ S ⊆ t.verts.toFinset)
    (hk : StarLegal
      (facetFamily K.tets)
      (fun q => S ⊆ q)
      (fun q => C ⊆ q)
      (facetFamily R))
    (hj : StarLegal
      (facetFamily J.tets)
      (fun q => S ⊆ q)
      (fun q => C ⊆ q)
      (facetFamily R)) :
    (K.tets.filter p).length =
      (J.tets.filter p).length := by
  apply family_length_eq
    ((starLegal_filtered_family K S C R p hp hk).trans
      (starLegal_filtered_family J S C R p hp hj).symm)
  · exact hK.2.1.filter _
  · exact hJ.2.1.filter _

theorem small_forward_legal_diamond
    (K J : Triangulation)
    (hK : ClosedTriangulationCore K)
    (hJ : ClosedTriangulationCore J)
    (T S C : Finset Nat)
    (v : Nat)
    (R A : List Tet)
    (F : Triangulation → Triangulation)
    (legal : Triangulation → Prop)
    (hT : facetFamily K.tets T)
    (hCard : T.card = 4)
    (hSCard : S.card < 4)
    (hCCard : C.card < 4)
    (hFresh : ∀ q, facetFamily K.tets q → v ∉ q)
    (hvS : v ∉ S)
    (hvC : v ∉ C)
    (hInsert : facetFamily J.tets =
      replace (facetFamily K.tets)
        (fun q => q = T) (stellarFacets T v))
    (hR : ∀ q, facetFamily R q → q ⊆ S ∪ C)
    (hA : ∀ q, facetFamily A q → q ⊆ S ∪ C)
    (hAdd : ∀ q, facetFamily A q → C ⊆ q)
    (hStar : StarLegal
      (facetFamily J.tets)
      (fun q => S ⊆ q)
      (fun q => C ⊆ q)
      (facetFamily R))
    (hRecover : StarLegal
      (facetFamily K.tets)
      (fun q => S ⊆ q)
      (fun q => C ⊆ q)
      (facetFamily R) → legal K)
    (hPreserve : legal K →
      ClosedTriangulationCore (F K))
    (hReplace : ∀ X,
      ClosedTriangulationCore X →
      facetFamily (F X).tets =
        replace (facetFamily X.tets)
          (facetFamily R) (facetFamily A)) :
    legal K ∧
      ∃ (L : Triangulation) (w : Move41Site),
        w.LegalIn L ∧
        facetFamily (w.replace L).tets =
          facetFamily (F K).tets ∧
        w.targetTet.verts.toFinset = T ∧
        w.e = v ∧
        facetFamily L.tets = facetFamily (F J).tets := by

  have hStarInserted : StarLegal
      (replace (facetFamily K.tets)
        (fun q => q = T) (stellarFacets T v))
      (fun q => S ⊆ q)
      (fun q => C ⊆ q)
      (facetFamily R) := by
    rw [← hInsert]
    exact hStar

  have hc := stellar_commutation_small_simplices
    (facetFamily K.tets)
    (facetFamily R)
    (facetFamily A)
    T S C v hT hCard hSCard hCCard
    hFresh hvS hvC hR hA hAdd hStarInserted

  have hlegal := hRecover hc.1
  have hcore := hPreserve hlegal
  have hkReplace := hReplace K hK
  have hjReplace := hReplace J hJ

  have hTAfter : facetFamily (F K).tets T := by
    rw [hkReplace]
    exact hc.2.1

  have hfreshAfter :
      ∀ q, facetFamily (F K).tets q → v ∉ q := by
    intro q hq hv
    rw [hkReplace] at hq
    rcases hq with h | h
    · exact hFresh q h.1 hv
    · rcases Finset.mem_union.mp (hA q h hv) with hs | ht
      · exact hvS hs
      · exact hvC ht

  obtain ⟨L, w, hw, hback, ht, hv, hfamily⟩ :=
    arbitrary_stellar_insertion_exists
      (F K) hcore T v hTAfter hfreshAfter

  refine ⟨hlegal, L, w, hw, hback, ht, hv, ?_⟩

  rw [hfamily, hjReplace, hInsert, hc.2.2.2, hkReplace]

theorem move23_exact_star
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move23Site)
    (hlegal : s.LegalIn K) :
    StarLegal
      (facetFamily K.tets)
      (fun q => ({s.a, s.b, s.c} : Finset Nat) ⊆ q)
      (fun q => ({s.d, s.e} : Finset Nat) ⊆ q)
      (facetFamily [s.leftTet, s.rightTet]) := by

  apply starLegal_of_exact_sources

  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl
    · exact hlegal.1.1
    · exact hlegal.1.2

  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl
    · simp [Move23Site.leftTet, Tet.verts,
        Finset.insert_subset_iff]
    · simp [Move23Site.rightTet, Tet.verts,
        Finset.insert_subset_iff]

  · intro t ht hs
    have hp :
        s.a ∈ t.verts ∧
        s.b ∈ t.verts ∧
        s.c ∈ t.verts := by
      simpa only [Finset.insert_subset_iff,
        Finset.singleton_subset_iff,
        List.mem_toFinset] using hs

    rcases hcore.move23Site_same_source_of_contains_sharedFace
        s hlegal ht hp.1 hp.2.1 hp.2.2 with hl | hr

    · exact ⟨s.leftTet, by simp, hl⟩
    · exact ⟨s.rightTet, by simp, hr⟩

  · intro t ht hc
    apply hlegal.2.2 t ht
    simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff,
      List.mem_toFinset] using hc

theorem move23_legal_of_exact_star
    {K J : Triangulation}
    (hK : ClosedTriangulationCore K)
    (hJ : ClosedTriangulationCore J)
    (s : Move23Site)
    (hlegal : s.LegalIn J)
    (hStar : StarLegal
      (facetFamily K.tets)
      (fun q => ({s.a, s.b, s.c} : Finset Nat) ⊆ q)
      (fun q => ({s.d, s.e} : Finset Nat) ⊆ q)
      (facetFamily [s.leftTet, s.rightTet])) :
    s.LegalIn K := by

  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩

  · exact starLegal_source_realized hStar
      (by simp : s.leftTet ∈ [s.leftTet, s.rightTet])

  · exact starLegal_source_realized hStar
      (by simp : s.rightTet ∈ [s.leftTet, s.rightTet])

  · have hc := starLegal_count_eq hK hJ
      {s.a, s.b, s.c} {s.d, s.e}
      [s.leftTet, s.rightTet]
      (fun t => decide
        (s.a ∈ t.verts ∧
         s.b ∈ t.verts ∧
         s.c ∈ t.verts))
      (by
        intro t
        simp only [decide_eq_true_eq,
          Finset.insert_subset_iff,
          Finset.singleton_subset_iff,
          List.mem_toFinset])
      hStar (move23_exact_star hJ s hlegal)

    exact hc.trans hlegal.2.1

  · intro t ht hp
    apply hStar.2 t.verts.toFinset
    refine ⟨⟨t, ht, rfl⟩, ?_⟩
    simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff,
      List.mem_toFinset] using hp

theorem move23_delayed_insertion_diamond
    (K J : Triangulation)
    (hK : ClosedTriangulationCore K)
    (hJ : ClosedTriangulationCore J)
    (s : Move23Site)
    (hlegal : s.LegalIn J)
    (T : Finset Nat)
    (v : Nat)
    (hT : facetFamily K.tets T)
    (hCard : T.card = 4)
    (hfresh : ∀ q, facetFamily K.tets q → v ∉ q)
    (hvS : v ∉ ({s.a, s.b, s.c} : Finset Nat))
    (hvC : v ∉ ({s.d, s.e} : Finset Nat))
    (hInsert : facetFamily J.tets =
      replace (facetFamily K.tets)
        (fun q => q = T) (stellarFacets T v)) :
    s.LegalIn K ∧
      ∃ (L : Triangulation) (w : Move41Site),
        w.LegalIn L ∧
        facetFamily (w.replace L).tets =
          facetFamily (s.replace K).tets ∧
        w.targetTet.verts.toFinset = T ∧
        w.e = v ∧
        facetFamily L.tets =
          facetFamily (s.replace J).tets := by
  classical

  let S : Finset Nat := {s.a, s.b, s.c}
  let C : Finset Nat := {s.d, s.e}

  have hSCard : S.card < 4 := by
    have h1 := Finset.card_insert_le
      s.a ({s.b, s.c} : Finset Nat)
    have h2 := Finset.card_insert_le
      s.b ({s.c} : Finset Nat)
    simp only [Finset.card_singleton] at h2
    change ({s.a, s.b, s.c} : Finset Nat).card < 4
    omega

  have hCCard : C.card < 4 := by
    have h1 := Finset.card_insert_le
      s.d ({s.e} : Finset Nat)
    simp only [Finset.card_singleton] at h1
    change ({s.d, s.e} : Finset Nat).card < 4
    omega

  apply small_forward_legal_diamond
    K J hK hJ T S C v
    [s.leftTet, s.rightTet]
    [s.newTet₀, s.newTet₁, s.newTet₂]
    s.replace s.LegalIn
    hT hCard hSCard hCCard
    hfresh hvS hvC hInsert

  · rintro q ⟨t, ht, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl
    · intro x hx
      simp [Move23Site.leftTet, Tet.verts] at hx
      simp [S, C]
      tauto
    · intro x hx
      simp [Move23Site.rightTet, Tet.verts] at hx
      simp [S, C]
      tauto

  · rintro q ⟨t, ht, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl
    · intro x hx
      simp [Move23Site.newTet₀, Tet.verts] at hx
      simp [S, C]
      tauto
    · intro x hx
      simp [Move23Site.newTet₁, Tet.verts] at hx
      simp [S, C]
      tauto
    · intro x hx
      simp [Move23Site.newTet₂, Tet.verts] at hx
      simp [S, C]
      tauto

  · rintro q ⟨t, ht, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl
    · simp [C, Move23Site.newTet₀, Tet.verts,
        Finset.insert_subset_iff]
    · simp [C, Move23Site.newTet₁, Tet.verts,
        Finset.insert_subset_iff]
    · simp [C, Move23Site.newTet₂, Tet.verts,
        Finset.insert_subset_iff]

  · exact move23_exact_star hJ s hlegal
  · exact move23_legal_of_exact_star hK hJ s hlegal
  · exact hK.move23Site_replace_closedCore s
  · intro X hX
    exact move23_family_replace X hX s

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.starLegal_of_exact_sources
#print axioms Poincare.DelayedInsertionAudit.starLegal_source_realized
#print axioms Poincare.DelayedInsertionAudit.starLegal_filtered_family
#print axioms Poincare.DelayedInsertionAudit.starLegal_count_eq
#print axioms Poincare.DelayedInsertionAudit.small_forward_legal_diamond
#print axioms Poincare.DelayedInsertionAudit.move23_exact_star
#print axioms Poincare.DelayedInsertionAudit.move23_legal_of_exact_star
#print axioms Poincare.DelayedInsertionAudit.move23_delayed_insertion_diamond

namespace Poincare.DelayedInsertionAudit

theorem move32_exact_star
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hlegal : s.LegalIn K) :
    StarLegal
      (facetFamily K.tets)
      (fun q => ({s.d, s.e} : Finset Nat) ⊆ q)
      (fun q => ({s.a, s.b, s.c} : Finset Nat) ⊆ q)
      (facetFamily
        [s.targetTet₀, s.targetTet₁, s.targetTet₂]) := by
  apply starLegal_of_exact_sources
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hlegal.1.1
    · exact hlegal.1.2.1
    · exact hlegal.1.2.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [Move32Site.targetTet₀, Tet.verts,
        Finset.insert_subset_iff]
    · simp [Move32Site.targetTet₁, Tet.verts,
        Finset.insert_subset_iff]
    · simp [Move32Site.targetTet₂, Tet.verts,
        Finset.insert_subset_iff]
  · intro t ht hs
    have hp : s.d ∈ t.verts ∧ s.e ∈ t.verts := by
      simpa only [Finset.insert_subset_iff,
        Finset.singleton_subset_iff,
        List.mem_toFinset] using hs
    rcases hcore.move32Site_same_target_of_contains_sharedEdge
        s hlegal ht hp.1 hp.2 with h0 | h1 | h2
    · exact ⟨s.targetTet₀, by simp, h0⟩
    · exact ⟨s.targetTet₁, by simp, h1⟩
    · exact ⟨s.targetTet₂, by simp, h2⟩
  · intro t ht hc
    apply hlegal.2.2 t ht
    simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff,
      List.mem_toFinset] using hc

theorem move32_legal_of_exact_star
    {K J : Triangulation}
    (hK : ClosedTriangulationCore K)
    (hJ : ClosedTriangulationCore J)
    (s : Move32Site)
    (hlegal : s.LegalIn J)
    (hStar : StarLegal
      (facetFamily K.tets)
      (fun q => ({s.d, s.e} : Finset Nat) ⊆ q)
      (fun q => ({s.a, s.b, s.c} : Finset Nat) ⊆ q)
      (facetFamily
        [s.targetTet₀, s.targetTet₁, s.targetTet₂])) :
    s.LegalIn K := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact starLegal_source_realized hStar
      (by simp : s.targetTet₀ ∈
        [s.targetTet₀, s.targetTet₁, s.targetTet₂])
  · exact starLegal_source_realized hStar
      (by simp : s.targetTet₁ ∈
        [s.targetTet₀, s.targetTet₁, s.targetTet₂])
  · exact starLegal_source_realized hStar
      (by simp : s.targetTet₂ ∈
        [s.targetTet₀, s.targetTet₁, s.targetTet₂])
  · have hc := starLegal_count_eq hK hJ
      {s.d, s.e} {s.a, s.b, s.c}
      [s.targetTet₀, s.targetTet₁, s.targetTet₂]
      (fun t => decide
        (s.d ∈ t.verts ∧ s.e ∈ t.verts))
      (by
        intro t
        simp only [decide_eq_true_eq,
          Finset.insert_subset_iff,
          Finset.singleton_subset_iff,
          List.mem_toFinset])
      hStar (move32_exact_star hJ s hlegal)
    exact hc.trans hlegal.2.1
  · intro t ht hp
    apply hStar.2 t.verts.toFinset
    refine ⟨⟨t, ht, rfl⟩, ?_⟩
    simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff,
      List.mem_toFinset] using hp

theorem move32_delayed_insertion_diamond
    (K J : Triangulation)
    (hK : ClosedTriangulationCore K)
    (hJ : ClosedTriangulationCore J)
    (s : Move32Site)
    (hlegal : s.LegalIn J)
    (T : Finset Nat)
    (v : Nat)
    (hT : facetFamily K.tets T)
    (hCard : T.card = 4)
    (hfresh : ∀ q, facetFamily K.tets q → v ∉ q)
    (hvS : v ∉ ({s.d, s.e} : Finset Nat))
    (hvC : v ∉ ({s.a, s.b, s.c} : Finset Nat))
    (hInsert : facetFamily J.tets =
      replace (facetFamily K.tets)
        (fun q => q = T) (stellarFacets T v)) :
    s.LegalIn K ∧
      ∃ (L : Triangulation) (w : Move41Site),
        w.LegalIn L ∧
        facetFamily (w.replace L).tets =
          facetFamily (s.replace K).tets ∧
        w.targetTet.verts.toFinset = T ∧
        w.e = v ∧
        facetFamily L.tets =
          facetFamily (s.replace J).tets := by
  classical
  let S : Finset Nat := {s.d, s.e}
  let C : Finset Nat := {s.a, s.b, s.c}

  have hSCard : S.card < 4 := by
    have h1 := Finset.card_insert_le
      s.d ({s.e} : Finset Nat)
    simp only [Finset.card_singleton] at h1
    change ({s.d, s.e} : Finset Nat).card < 4
    omega

  have hCCard : C.card < 4 := by
    have h1 := Finset.card_insert_le
      s.a ({s.b, s.c} : Finset Nat)
    have h2 := Finset.card_insert_le
      s.b ({s.c} : Finset Nat)
    simp only [Finset.card_singleton] at h2
    change ({s.a, s.b, s.c} : Finset Nat).card < 4
    omega

  apply small_forward_legal_diamond
    K J hK hJ T S C v
    [s.targetTet₀, s.targetTet₁, s.targetTet₂]
    [s.sourceTet₀, s.sourceTet₁]
    s.replace s.LegalIn
    hT hCard hSCard hCCard
    hfresh hvS hvC hInsert

  · rintro q ⟨t, ht, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl
    · intro x hx
      simp [Move32Site.targetTet₀, Tet.verts] at hx
      simp [S, C]
      tauto
    · intro x hx
      simp [Move32Site.targetTet₁, Tet.verts] at hx
      simp [S, C]
      tauto
    · intro x hx
      simp [Move32Site.targetTet₂, Tet.verts] at hx
      simp [S, C]
      tauto

  · rintro q ⟨t, ht, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl
    · intro x hx
      simp [Move32Site.sourceTet₀, Tet.verts] at hx
      simp [S, C]
      tauto
    · intro x hx
      simp [Move32Site.sourceTet₁, Tet.verts] at hx
      simp [S, C]
      tauto

  · rintro q ⟨t, ht, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl
    · simp [C, Move32Site.sourceTet₀, Tet.verts,
        Finset.insert_subset_iff]
    · simp [C, Move32Site.sourceTet₁, Tet.verts,
        Finset.insert_subset_iff]

  · exact move32_exact_star hJ s hlegal
  · exact move32_legal_of_exact_star hK hJ s hlegal
  · exact hK.move32Site_replace_closedCore s
  · intro X hX
    exact move32_family_replace X hX s

theorem move41_target_card
    (s : Move41Site) :
    s.targetTet.verts.toFinset.card = 4 := by
  have hd := s.distinct
  have hn : s.targetTet.verts.Nodup := by
    simp [Move41Site.targetTet, Tet.verts]
    simp at hd
    aesop
  simpa [Tet.verts] using List.toFinset_card_of_nodup hn

theorem move41_exact_star
    {K : Triangulation}
    {s : Move41Site}
    (hlegal : s.LegalIn K) :
    StarLegal
      (facetFamily K.tets)
      (fun q => ({s.e} : Finset Nat) ⊆ q)
      (fun q => s.targetTet.verts.toFinset ⊆ q)
      (facetFamily s.sourceTets) := by
  apply starLegal_of_exact_sources
  · intro r hr
    obtain ⟨t, ht, he⟩ :=
      move41_source_family_subset hlegal
        r.verts.toFinset ⟨r, hr, rfl⟩
    exact ⟨t, ht,
      (sameTetVertices_iff_finset t r).2 he⟩
  · intro r hr
    have hf : facetFamily s.sourceTets
        r.verts.toFinset := ⟨r, hr, rfl⟩
    rw [move41_source_family_stellar] at hf
    exact Finset.singleton_subset_iff.mpr
      (stellar_center_mem _ _ _ hf)
  · intro t ht hs
    apply hlegal.centerSaturated t ht
    exact List.mem_toFinset.mp
      (Finset.singleton_subset_iff.mp hs)
  · intro t ht hs
    have hc : t.verts.toFinset.card = 4 := by
      simpa [Tet.verts] using
        List.toFinset_card_of_nodup
          (hlegal.closedCore.1 t ht)
    have he : s.targetTet.verts.toFinset =
        t.verts.toFinset :=
      Finset.eq_of_subset_of_card_le hs
        (by rw [hc, move41_target_card])
    exact hlegal.targetAbsent t ht
      ((sameTetVertices_iff_finset t s.targetTet).2
        he.symm)

theorem move41_legal_of_exact_star
    {K J : Triangulation}
    (hK : ClosedTriangulationCore K)
    (s : Move41Site)
    (hlegal : s.LegalIn J)
    (hStar : StarLegal
      (facetFamily K.tets)
      (fun q => ({s.e} : Finset Nat) ⊆ q)
      (fun q => s.targetTet.verts.toFinset ⊆ q)
      (facetFamily s.sourceTets)) :
    s.LegalIn K := by
  refine ⟨hK, ?_,
    hlegal.sourcePairwiseDistinct, ?_, ?_⟩
  · intro source hs
    apply Poincare.filter_length_one_of_pairwise
    · apply hK.2.1.imp
      intro t u hne hmatch
      have ht :=
        (sameTetVerticesBool_eq_true_iff t source).1
          hmatch.1
      have hu :=
        (sameTetVerticesBool_eq_true_iff u source).1
          hmatch.2
      exact hne
        (sameTetVertices_trans ht
          (sameTetVertices_symm hu))
    · obtain ⟨t, ht, hm⟩ :=
        starLegal_source_realized hStar hs
      exact ⟨t, ht,
        (sameTetVerticesBool_eq_true_iff t source).2 hm⟩
  · intro t ht he
    have hf :=
      (hStar.1 t.verts.toFinset).2
        ⟨⟨t, ht, rfl⟩,
          Finset.singleton_subset_iff.mpr
            (List.mem_toFinset.mpr he)⟩
    obtain ⟨r, hr, hm⟩ := hf
    exact ⟨r, hr,
      (sameTetVertices_iff_finset t r).2 hm.symm⟩
  · intro t ht hm
    apply hStar.2 t.verts.toFinset
    refine ⟨⟨t, ht, rfl⟩, ?_⟩
    rw [(sameTetVertices_iff_finset t s.targetTet).1 hm]

theorem move41_delayed_insertion_diamond
    (K J : Triangulation)
    (hK : ClosedTriangulationCore K)
    (s : Move41Site)
    (hlegal : s.LegalIn J)
    (T : Finset Nat)
    (v : Nat)
    (hT : facetFamily K.tets T)
    (hCard : T.card = 4)
    (hfresh : ∀ q, facetFamily K.tets q → v ∉ q)
    (hvC : v ∉ s.targetTet.verts.toFinset)
    (hvCenter : v ≠ s.e)
    (hNoBoundary : NoFiveBoundary (facetFamily K.tets))
    (hInsert : facetFamily J.tets =
      replace (facetFamily K.tets)
        (fun q => q = T) (stellarFacets T v)) :
    s.LegalIn K ∧
      ∃ (L : Triangulation) (w : Move41Site),
        w.LegalIn L ∧
        facetFamily (w.replace L).tets =
          facetFamily (s.replace K).tets ∧
        w.targetTet.verts.toFinset = T ∧
        w.e = v ∧
        facetFamily L.tets =
          facetFamily (s.replace J).tets := by
  let C := s.targetTet.verts.toFinset

  have hwC : s.e ∉ C := by
    have hd := s.distinct
    simp [C, Move41Site.targetTet, Tet.verts]
    simp at hd
    aesop

  have hs := move41_exact_star hlegal
  rw [move41_source_family_stellar, hInsert] at hs

  have hs' : StarLegal
      (replace (facetFamily K.tets)
        (fun q => q = T) (stellarFacets T v))
      (fun q => s.e ∈ q)
      (fun q => C ⊆ q)
      (stellarFacets C s.e) := by
    simpa only [Finset.singleton_subset_iff] using hs

  have hc := stellar_commutation_41
    (facetFamily K.tets) T C v s.e
    hT hCard (move41_target_card s)
    hfresh hvC hvCenter hwC hNoBoundary hs'

  have hStar : StarLegal
      (facetFamily K.tets)
      (fun q => ({s.e} : Finset Nat) ⊆ q)
      (fun q => C ⊆ q)
      (facetFamily s.sourceTets) := by
    rw [move41_source_family_stellar]
    simpa only [Finset.singleton_subset_iff] using hc.1

  have hl := move41_legal_of_exact_star hK s hlegal hStar

  have htarget : facetFamily [s.targetTet] =
      (fun q => q = C) := by
    funext q
    apply propext
    simp only [facetFamily_cons, facetFamily_nil, or_false, C]

  have hrK := move41_family_replace K hK s
  have hrJ := move41_family_replace J hlegal.closedCore s

  rw [move41_source_family_stellar, htarget] at hrK hrJ

  have hTAfter : facetFamily (s.replace K).tets T := by
    rw [hrK]
    exact hc.2.1

  have hFreshAfter :
      ∀ q, facetFamily (s.replace K).tets q → v ∉ q := by
    intro q hq hv
    rw [hrK] at hq
    rcases hq with h | he
    · exact hfresh q h.1 hv
    · apply hvC
      change v ∈ C
      rw [← he]
      exact hv

  obtain ⟨L, w, hw, hb, ht, hv, hf⟩ :=
    arbitrary_stellar_insertion_exists
      (s.replace K)
      (hK.move41Site_replace_closedCore s hl)
      T v hTAfter hFreshAfter

  refine ⟨hl, L, w, hw, hb, ht, hv, ?_⟩
  rw [hf, hrJ, hInsert, hc.2.2.2, hrK]

theorem independent_insertions_legal_diamond
    (K J M : Triangulation)
    (hK : ClosedTriangulationCore K)
    (T U : Finset Nat)
    (v w : Nat)
    (hT : facetFamily K.tets T)
    (hCard : T.card = 4)
    (hvFresh : ∀ q, facetFamily K.tets q → v ∉ q)
    (hInsert : facetFamily J.tets =
      replace (facetFamily K.tets)
        (fun q => q = T) (stellarFacets T v))
    (hU : facetFamily J.tets U)
    (hUv : v ∉ U)
    (hwFresh : ∀ q, facetFamily J.tets q → w ∉ q)
    (hSecond : facetFamily M.tets =
      replace (facetFamily J.tets)
        (fun q => q = U) (stellarFacets U w)) :
    ∃ (L N : Triangulation) (a b : Move41Site),
      a.LegalIn L ∧ b.LegalIn N ∧
      facetFamily (a.replace L).tets = facetFamily K.tets ∧
      a.targetTet.verts.toFinset = U ∧ a.e = w ∧
      facetFamily (b.replace N).tets = facetFamily L.tets ∧
      b.targetTet.verts.toFinset = T ∧ b.e = v ∧
      facetFamily N.tets = facetFamily M.tets := by

  have hU' := hU
  have hwFresh' := hwFresh
  rw [hInsert] at hU' hwFresh'

  obtain ⟨hUold, _hUne, _hvw, hwOld,
    hTsurvives, hvAfter, hComm⟩ :=
    independent_insertions_commute
      (facetFamily K.tets) T U v w
      hT hCard hvFresh hU' hUv hwFresh'

  obtain ⟨L, a, ha, hback, ht, hw, hf⟩ :=
    arbitrary_stellar_insertion_exists
      K hK U w hUold hwOld

  have hTL : facetFamily L.tets T := by
    rw [hf]
    exact hTsurvives

  have hvL : ∀ q, facetFamily L.tets q → v ∉ q := by
    intro q hq
    rw [hf] at hq
    exact hvAfter q hq

  obtain ⟨N, b, hb, hback2, ht2, hv, hf2⟩ :=
    arbitrary_stellar_insertion_exists
      L ha.closedCore T v hTL hvL

  refine ⟨L, N, a, b, ha, hb, hback, ht, hw,
    hback2, ht2, hv, ?_⟩

  rw [hf2, hf, hSecond, hInsert, hComm]

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.move32_exact_star
#print axioms Poincare.DelayedInsertionAudit.move32_legal_of_exact_star
#print axioms Poincare.DelayedInsertionAudit.move32_delayed_insertion_diamond
#print axioms Poincare.DelayedInsertionAudit.move41_target_card
#print axioms Poincare.DelayedInsertionAudit.move41_exact_star
#print axioms Poincare.DelayedInsertionAudit.move41_legal_of_exact_star
#print axioms Poincare.DelayedInsertionAudit.move41_delayed_insertion_diamond
#print axioms Poincare.DelayedInsertionAudit.independent_insertions_legal_diamond

namespace Poincare.DelayedInsertionAudit

def nonInsertionCount
    {α : Type*} (isInsert : α → Bool) :
    List α → Nat
  | [] => 0
  | a :: rest =>
      (if isInsert a then 0 else 1) +
        nonInsertionCount isInsert rest

def insertionInversions
    {α : Type*} (isInsert : α → Bool) :
    List α → Nat
  | [] => 0
  | a :: rest =>
      (if isInsert a
        then nonInsertionCount isInsert rest
        else 0) +
      insertionInversions isInsert rest

theorem swap_nonInsertionCount
    {α : Type*}
    (isInsert : α → Bool)
    (pre : List α)
    (a b : α)
    (post : List α)
    (ha : isInsert a = true)
    (hb : isInsert b = false) :
    nonInsertionCount isInsert
      (pre ++ a :: b :: post) =
    nonInsertionCount isInsert
      (pre ++ b :: a :: post) := by
  induction pre with
  | nil =>
      simp [nonInsertionCount, ha, hb]
  | cons x pre ih =>
      simp [nonInsertionCount, ih]

theorem delayed_swap_reduces_inversions
    {α : Type*}
    (isInsert : α → Bool)
    (pre : List α)
    (a b : α)
    (post : List α)
    (ha : isInsert a = true)
    (hb : isInsert b = false) :
    insertionInversions isInsert
      (pre ++ a :: b :: post) =
    insertionInversions isInsert
      (pre ++ b :: a :: post) + 1 := by
  induction pre with
  | nil =>
      simp [insertionInversions,
        nonInsertionCount, ha, hb,
        Nat.add_comm,
        Nat.add_left_comm]
  | cons x pre ih =>
      simp only [
        List.cons_append,
        insertionInversions,
        swap_nonInsertionCount
          isInsert pre a b post ha hb,
        ih,
        Nat.add_assoc
      ]

theorem delayed_insertion_normal_form
    {α : Type*}
    (isInsert : α → Bool)
    (P : List α → Prop)
    (swapOK :
      List α → α → α → List α → Prop)
    (hClose :
      ∀ pre a b post,
        isInsert a = true →
        isInsert b = false →
        swapOK pre a b post →
        P (pre ++ a :: b :: post) →
        P (pre ++ b :: a :: post))
    (initial : List α)
    (hInitial : P initial) :
    ∃ w, P w ∧
      ∀ pre a b post,
        w = pre ++ a :: b :: post →
        isInsert a = true →
        isInsert b = false →
        ¬ swapOK pre a b post := by
  classical

  let Q : Nat → Prop := fun n =>
    ∃ w, P w ∧
      insertionInversions isInsert w = n

  have hex : ∃ n, Q n :=
    ⟨insertionInversions isInsert initial,
      initial, hInitial, rfl⟩

  obtain ⟨w, hw, hscore⟩ :=
    Nat.find_spec hex

  refine ⟨w, hw, ?_⟩

  intro pre a b post heq ha hb hok

  have hp : P (pre ++ a :: b :: post) := by
    rw [← heq]
    exact hw

  have hp' :=
    hClose pre a b post ha hb hok hp

  have hmin :=
    Nat.find_min' hex
      (show Q
        (insertionInversions isInsert
          (pre ++ b :: a :: post)) from
        ⟨pre ++ b :: a :: post, hp', rfl⟩)

  have hswap :=
    delayed_swap_reduces_inversions
      isInsert pre a b post ha hb

  rw [heq] at hscore
  omega

theorem delayed_swap_preserves_upper_bound
    (initial insertion other cap : Int)
    (hOriginal : initial + insertion ≤ cap)
    (hOther : other ≤ insertion) :
    initial + other ≤ cap := by
  omega

theorem delayed_swap_preserves_defect_cap
    (initial other cap : Int)
    (hOriginal : initial + 8 ≤ cap)
    (hOther : other = 4 ∨ other = -4 ∨ other = -8) :
    initial + other ≤ cap := by
  omega

theorem delayed_swap_preserves_vertex_cap
    (initial other cap : Int)
    (hOriginal : initial + 1 ≤ cap)
    (hOther : other = 0 ∨ other = -1) :
    initial + other ≤ cap := by
  omega

def finiteStellar
    (K : Finset (Finset Nat))
    (T : Finset Nat) (v : Nat) :
    Finset (Finset Nat) :=
  K.erase T ∪
    T.image (fun a => insert v (T.erase a))

def finiteFlip23
    (K : Finset (Finset Nat))
    (F : Finset Nat) (x y : Nat) :
    Finset (Finset Nat) :=
  (K.erase (insert x F)).erase (insert y F) ∪
    F.image
      (fun a => insert x (insert y (F.erase a)))

def normalizationFixture :
    Finset (Finset Nat) :=
  {{0, 1, 2, 3},
   {0, 1, 2, 4},
   {0, 1, 3, 4},
   {0, 2, 3, 4},
   {1, 2, 3, 4}}

def fixtureFirst :
    Finset (Finset Nat) :=
  finiteStellar normalizationFixture
    {0, 1, 2, 3} 5

def fixtureSecond :
    Finset (Finset Nat) :=
  finiteStellar fixtureFirst
    {0, 1, 2, 4} 6

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem simultaneous_activation_fixture :
    ({0, 1, 2, 3} : Finset Nat) ∈
      normalizationFixture ∧
    ({0, 1, 2, 4} : Finset Nat) ∈
      fixtureFirst ∧
    normalizationFixture.card = 5 ∧
    fixtureFirst.card = 8 ∧
    fixtureSecond.card = 11 ∧
    fixtureSecond.filter
      (fun t => ({0, 1, 2} : Finset Nat) ⊆ t) =
        {{0, 1, 2, 5}, {0, 1, 2, 6}} ∧
    fixtureSecond.filter
      (fun t => ({5, 6} : Finset Nat) ⊆ t) = ∅ ∧
    fixtureSecond =
      finiteStellar
        (finiteStellar normalizationFixture
          {0, 1, 2, 4} 6)
        {0, 1, 2, 3} 5 := by
  decide

def fixtureNested :
    Finset (Finset Nat) :=
  finiteStellar fixtureFirst
    {0, 1, 2, 5} 6

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem simultaneous_activation_nested_rewrite :
    fixtureNested.filter
      (fun t => ({0, 1, 2} : Finset Nat) ⊆ t) =
        {{0, 1, 2, 6}, {0, 1, 2, 4}} ∧
    fixtureNested.filter
      (fun t => ({4, 6} : Finset Nat) ⊆ t) = ∅ ∧
    finiteFlip23 fixtureSecond {0, 1, 2} 5 6 =
      finiteFlip23 fixtureNested {0, 1, 2} 4 6 := by
  decide

end Poincare.DelayedInsertionAudit

#print axioms Poincare.DelayedInsertionAudit.swap_nonInsertionCount
#print axioms Poincare.DelayedInsertionAudit.delayed_swap_reduces_inversions
#print axioms Poincare.DelayedInsertionAudit.delayed_insertion_normal_form
#print axioms Poincare.DelayedInsertionAudit.delayed_swap_preserves_upper_bound
#print axioms Poincare.DelayedInsertionAudit.delayed_swap_preserves_defect_cap
#print axioms Poincare.DelayedInsertionAudit.delayed_swap_preserves_vertex_cap
#print axioms Poincare.DelayedInsertionAudit.simultaneous_activation_fixture
#print axioms Poincare.DelayedInsertionAudit.simultaneous_activation_nested_rewrite
