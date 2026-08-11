import Poincare.Triangulation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Count

namespace Poincare

open scoped BigOperators

inductive PachnerMove where
| move23
| move32
| move14
| move41


structure Move23Site where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  distinct :
    [a, b, c, d, e].Nodup

def Move23Site.leftTet (s : Move23Site) : Tet :=
  ⟨s.a, s.b, s.c, s.d⟩

def Move23Site.rightTet (s : Move23Site) : Tet :=
  ⟨s.a, s.b, s.c, s.e⟩

def Move23Site.newTet₀ (s : Move23Site) : Tet :=
  ⟨s.a, s.b, s.d, s.e⟩

def Move23Site.newTet₁ (s : Move23Site) : Tet :=
  ⟨s.a, s.c, s.d, s.e⟩

def Move23Site.newTet₂ (s : Move23Site) : Tet :=
  ⟨s.b, s.c, s.d, s.e⟩


def SameTetVertices (τ σ : Tet) : Prop :=
  ∀ v : Nat, v ∈ τ.verts ↔ v ∈ σ.verts

def Move23Site.RealizedIn (s : Move23Site) (K : Triangulation) : Prop :=
  (∃ τ ∈ K.tets, SameTetVertices τ s.leftTet) ∧
  (∃ τ ∈ K.tets, SameTetVertices τ s.rightTet)


def Move23Site.NewEdgeAbsent (s : Move23Site) (K : Triangulation) : Prop :=
  ∀ τ ∈ K.tets, ¬ (s.d ∈ τ.verts ∧ s.e ∈ τ.verts)


def Move23Site.SharedFaceExactlyTwo
    (s : Move23Site) (K : Triangulation) : Prop :=
  (K.tets.filter
      (fun τ =>
        s.a ∈ τ.verts ∧
        s.b ∈ τ.verts ∧
        s.c ∈ τ.verts)).length = 2


def Move23Site.LegalIn (s : Move23Site) (K : Triangulation) : Prop :=
  s.RealizedIn K ∧
  s.SharedFaceExactlyTwo K ∧
  s.NewEdgeAbsent K


def sameTetVerticesBool (τ σ : Tet) : Bool :=
  τ.verts.all (fun v => σ.verts.contains v) &&
  σ.verts.all (fun v => τ.verts.contains v)


theorem sameTetVerticesBool_eq_true_iff
    (τ σ : Tet) :
    sameTetVerticesBool τ σ = true ↔ SameTetVertices τ σ := by
  simp [sameTetVerticesBool, SameTetVertices]
  constructor
  · rintro ⟨hτσ, hστ⟩ v
    constructor
    · exact hτσ v
    · exact hστ v
  · intro h
    constructor
    · intro v hv
      exact (h v).1 hv
    · intro v hv
      exact (h v).2 hv

def eraseFirstSameTet (target : Tet) : List Tet → List Tet
  | [] => []
  | τ :: rest =>
      if sameTetVerticesBool τ target then
        rest
      else
        τ :: eraseFirstSameTet target rest


theorem eraseFirstSameTet_count_flatMap
    (target : Tet) (tets : List Tet) (v : Nat)
    (hex : ∃ τ ∈ tets, SameTetVertices τ target)
    (hcount :
      ∀ τ ∈ tets,
        SameTetVertices τ target →
        τ.verts.count v = target.verts.count v) :
    (tets.flatMap Tet.verts).count v =
      ((eraseFirstSameTet target tets).flatMap Tet.verts).count v +
        target.verts.count v := by
  induction tets with
  | nil =>
      simp at hex
  | cons τ rest ih =>
      by_cases hb : sameTetVerticesBool τ target = true
      · have hm : SameTetVertices τ target :=
          (sameTetVerticesBool_eq_true_iff τ target).1 hb
        have hc :
            τ.verts.count v = target.verts.count v :=
          hcount τ (by simp) hm
        simp [eraseFirstSameTet, hb, hc, Nat.add_comm]
      · have hbfalse : sameTetVerticesBool τ target = false := by
          cases hbool : sameTetVerticesBool τ target with
          | false =>
              rfl
          | true =>
              exact (hb hbool).elim

        have hhead : ¬ SameTetVertices τ target := by
          intro hm
          exact hb ((sameTetVerticesBool_eq_true_iff τ target).2 hm)

        have hexrest :
            ∃ σ ∈ rest, SameTetVertices σ target := by
          rcases hex with ⟨σ, hmem, hm⟩
          have hs : σ = τ ∨ σ ∈ rest := by
            simpa using hmem
          cases hs with
          | inl heq =>
              subst σ
              exact (hhead hm).elim
          | inr hrest =>
              exact ⟨σ, hrest, hm⟩

        have hcountrest :
            ∀ σ ∈ rest,
              SameTetVertices σ target →
              σ.verts.count v = target.verts.count v := by
          intro σ hmem hm
          exact hcount σ (by simp [hmem]) hm

        have hi := ih hexrest hcountrest
        simp [eraseFirstSameTet, hbfalse, hi, Nat.add_assoc]


theorem Move23Site.sourceMatch_count_eq
    (s : Move23Site) (target τ : Tet)
    (htarget : target = s.leftTet ∨ target = s.rightTet)
    (hmatch : SameTetVertices τ target)
    (v : Nat) :
    τ.verts.count v = target.verts.count v := by
  have htargetNodup : target.verts.Nodup := by
    rcases htarget with hleft | hright
    · subst target
      have hs := s.distinct
      simp_all [Move23Site.leftTet, Tet.verts]
    · subst target
      have hs := s.distinct
      simp_all [Move23Site.rightTet, Tet.verts]

  have hfin :
      τ.verts.toFinset = target.verts.toFinset := by
    ext x
    simpa using hmatch x

  have hcardτ :
      τ.verts.toFinset.card = τ.verts.length := by
    rw [hfin]
    rw [List.toFinset_card_of_nodup htargetNodup]
    simp [Tet.verts]

  have hτmulti :
      (↑τ.verts : Multiset Nat).Nodup := by
    apply (Multiset.toFinset_card_eq_card_iff_nodup).1
    simpa using hcardτ

  have hτNodup : τ.verts.Nodup := by
    simpa using hτmulti

  by_cases hv : v ∈ target.verts
  · have hvτ : v ∈ τ.verts := (hmatch v).2 hv
    calc
      τ.verts.count v = 1 :=
        List.count_eq_one_of_mem hτNodup hvτ
      _ = target.verts.count v :=
        (List.count_eq_one_of_mem htargetNodup hv).symm
  · have hvτ : v ∉ τ.verts := by
      intro hmem
      exact hv ((hmatch v).1 hmem)

    have hτzero : τ.verts.count v = 0 := by
      have hm :
          Multiset.count v (↑τ.verts : Multiset Nat) = 0 :=
        Multiset.count_eq_zero_of_notMem (by simpa using hvτ)
      simpa using hm

    have htargetzero : target.verts.count v = 0 := by
      have hm :
          Multiset.count v (↑target.verts : Multiset Nat) = 0 :=
        Multiset.count_eq_zero_of_notMem (by simpa using hv)
      simpa using hm

    rw [hτzero, htargetzero]


theorem Move23Site.leftTet_not_same_rightTet
    (s : Move23Site) :
    ¬ SameTetVertices s.leftTet s.rightTet := by
  intro h

  have hdLeft : s.d ∈ s.leftTet.verts := by
    simp [Move23Site.leftTet, Tet.verts]

  have hdRight : s.d ∈ s.rightTet.verts :=
    (h s.d).1 hdLeft

  have hdCases :
      s.d = s.a ∨
      s.d = s.b ∨
      s.d = s.c ∨
      s.d = s.e := by
    simpa [Move23Site.rightTet, Tet.verts] using hdRight

  have had : s.a ≠ s.d := by
    intro had
    have hs := s.distinct
    simp [had] at hs

  have hbd : s.b ≠ s.d := by
    intro hbd
    have hs := s.distinct
    simp [hbd] at hs

  have hcd : s.c ≠ s.d := by
    intro hcd
    have hs := s.distinct
    simp [hcd] at hs

  have hde : s.d ≠ s.e := by
    intro hde
    have hs := s.distinct
    simp [hde] at hs

  rcases hdCases with hda | hdb | hdc | hdeq
  · exact had hda.symm
  · exact hbd hdb.symm
  · exact hcd hdc.symm
  · exact hde hdeq


theorem Move23Site.rightMatch_survives_eraseLeft
    (s : Move23Site) (tets : List Tet)
    (hex : ∃ τ ∈ tets, SameTetVertices τ s.rightTet) :
    ∃ τ ∈ eraseFirstSameTet s.leftTet tets,
      SameTetVertices τ s.rightTet := by
  induction tets with
  | nil =>
      simp at hex
  | cons τ rest ih =>
      by_cases hb : sameTetVerticesBool τ s.leftTet = true
      · have hleft : SameTetVertices τ s.leftTet :=
          (sameTetVerticesBool_eq_true_iff τ s.leftTet).1 hb

        have hnotRight : ¬ SameTetVertices τ s.rightTet := by
          intro hright
          apply s.leftTet_not_same_rightTet
          intro v
          constructor
          · intro hvLeft
            exact (hright v).1 ((hleft v).2 hvLeft)
          · intro hvRight
            exact (hleft v).1 ((hright v).2 hvRight)

        rcases hex with ⟨σ, hmem, hright⟩
        have hs : σ = τ ∨ σ ∈ rest := by
          simpa using hmem
        cases hs with
        | inl heq =>
            subst σ
            exact (hnotRight hright).elim
        | inr hrest =>
            refine ⟨σ, ?_, hright⟩
            simpa [eraseFirstSameTet, hb] using hrest

      · have hbfalse : sameTetVerticesBool τ s.leftTet = false := by
          cases hbool : sameTetVerticesBool τ s.leftTet with
          | false =>
              rfl
          | true =>
              exact (hb hbool).elim

        rcases hex with ⟨σ, hmem, hright⟩
        have hs : σ = τ ∨ σ ∈ rest := by
          simpa using hmem
        cases hs with
        | inl heq =>
            subst σ
            refine ⟨τ, ?_, hright⟩
            simp [eraseFirstSameTet, hbfalse]
        | inr hrest =>
            have hsurvive :=
              ih ⟨σ, hrest, hright⟩
            rcases hsurvive with ⟨ρ, hρmem, hρright⟩
            refine ⟨ρ, ?_, hρright⟩
            simp [eraseFirstSameTet, hbfalse, hρmem]


theorem Move23Site.twoSourceErasure_count
    (s : Move23Site) (K : Triangulation)
    (hlegal : s.LegalIn K)
    (v : Nat) :
    (K.tets.flatMap Tet.verts).count v =
      ((eraseFirstSameTet s.rightTet
        (eraseFirstSameTet s.leftTet K.tets)).flatMap Tet.verts).count v +
        s.leftTet.verts.count v +
        s.rightTet.verts.count v := by
  have hrealized : s.RealizedIn K := hlegal.1
  rcases hrealized with ⟨hleft, hright⟩

  have hleftGuard :
      ∀ τ ∈ K.tets,
        SameTetVertices τ s.leftTet →
        τ.verts.count v = s.leftTet.verts.count v := by
    intro τ _ hmatch
    exact
      s.sourceMatch_count_eq
        s.leftTet τ (Or.inl rfl) hmatch v

  have hleftErase :
      (K.tets.flatMap Tet.verts).count v =
        ((eraseFirstSameTet s.leftTet K.tets).flatMap Tet.verts).count v +
          s.leftTet.verts.count v :=
    eraseFirstSameTet_count_flatMap
      s.leftTet K.tets v hleft hleftGuard

  have hrightSurvives :
      ∃ τ ∈ eraseFirstSameTet s.leftTet K.tets,
        SameTetVertices τ s.rightTet :=
    s.rightMatch_survives_eraseLeft K.tets hright

  have hrightGuard :
      ∀ τ ∈ eraseFirstSameTet s.leftTet K.tets,
        SameTetVertices τ s.rightTet →
        τ.verts.count v = s.rightTet.verts.count v := by
    intro τ _ hmatch
    exact
      s.sourceMatch_count_eq
        s.rightTet τ (Or.inr rfl) hmatch v

  have hrightErase :
      ((eraseFirstSameTet s.leftTet K.tets).flatMap Tet.verts).count v =
        ((eraseFirstSameTet s.rightTet
          (eraseFirstSameTet s.leftTet K.tets)).flatMap Tet.verts).count v +
          s.rightTet.verts.count v :=
    eraseFirstSameTet_count_flatMap
      s.rightTet
      (eraseFirstSameTet s.leftTet K.tets)
      v
      hrightSurvives
      hrightGuard

  calc
    (K.tets.flatMap Tet.verts).count v =
        ((eraseFirstSameTet s.leftTet K.tets).flatMap Tet.verts).count v +
          s.leftTet.verts.count v := hleftErase
    _ =
        (((eraseFirstSameTet s.rightTet
          (eraseFirstSameTet s.leftTet K.tets)).flatMap Tet.verts).count v +
          s.rightTet.verts.count v) +
          s.leftTet.verts.count v := by
            rw [hrightErase]
    _ =
        ((eraseFirstSameTet s.rightTet
          (eraseFirstSameTet s.leftTet K.tets)).flatMap Tet.verts).count v +
          s.leftTet.verts.count v +
          s.rightTet.verts.count v := by
            ac_rfl

def Move23Site.replace (s : Move23Site) (K : Triangulation) : Triangulation :=
  let afterLeft := eraseFirstSameTet s.leftTet K.tets
  let afterRight := eraseFirstSameTet s.rightTet afterLeft
  { tets :=
      s.newTet₀ ::
      s.newTet₁ ::
      s.newTet₂ ::
      afterRight }


theorem Move23Site.replace_vertexDegree_balance
    (s : Move23Site) (K : Triangulation)
    (hlegal : s.LegalIn K)
    (v : Nat) :
    vertexDegree K v +
        s.newTet₀.verts.count v +
        s.newTet₁.verts.count v +
        s.newTet₂.verts.count v =
      vertexDegree (s.replace K) v +
        s.leftTet.verts.count v +
        s.rightTet.verts.count v := by
  have hErase :=
    s.twoSourceErasure_count K hlegal v

  have hReplace :
      ((s.replace K).tets.flatMap Tet.verts).count v =
        s.newTet₀.verts.count v +
          s.newTet₁.verts.count v +
          s.newTet₂.verts.count v +
          ((eraseFirstSameTet s.rightTet
            (eraseFirstSameTet s.leftTet K.tets)).flatMap
              Tet.verts).count v := by
    simp [Move23Site.replace, Nat.add_assoc]

  change
    (K.tets.flatMap Tet.verts).count v +
        s.newTet₀.verts.count v +
        s.newTet₁.verts.count v +
        s.newTet₂.verts.count v =
      ((s.replace K).tets.flatMap Tet.verts).count v +
        s.leftTet.verts.count v +
        s.rightTet.verts.count v

  calc
    (K.tets.flatMap Tet.verts).count v +
          s.newTet₀.verts.count v +
          s.newTet₁.verts.count v +
          s.newTet₂.verts.count v =
        (((eraseFirstSameTet s.rightTet
            (eraseFirstSameTet s.leftTet K.tets)).flatMap
              Tet.verts).count v +
          s.leftTet.verts.count v +
          s.rightTet.verts.count v) +
          s.newTet₀.verts.count v +
          s.newTet₁.verts.count v +
          s.newTet₂.verts.count v := by
            rw [hErase]
    _ =
        (s.newTet₀.verts.count v +
          s.newTet₁.verts.count v +
          s.newTet₂.verts.count v +
          ((eraseFirstSameTet s.rightTet
            (eraseFirstSameTet s.leftTet K.tets)).flatMap
              Tet.verts).count v) +
          s.leftTet.verts.count v +
          s.rightTet.verts.count v := by
            ac_rfl
    _ =
        ((s.replace K).tets.flatMap Tet.verts).count v +
          s.leftTet.verts.count v +
          s.rightTet.verts.count v := by
            rw [← hReplace]

def applyMove (T : Triangulation) (_ : PachnerMove) : Triangulation := T
def selectMove (_T : Triangulation) : PachnerMove := PachnerMove.move23


theorem Move23Site.replace_vertexDegree_site
    (s : Move23Site) (K : Triangulation)
    (hlegal : s.LegalIn K) :
    vertexDegree (s.replace K) s.a = vertexDegree K s.a ∧
    vertexDegree (s.replace K) s.b = vertexDegree K s.b ∧
    vertexDegree (s.replace K) s.c = vertexDegree K s.c ∧
    vertexDegree (s.replace K) s.d = vertexDegree K s.d + 2 ∧
    vertexDegree (s.replace K) s.e = vertexDegree K s.e + 2 := by

  have hab : s.a ≠ s.b := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hac : s.a ≠ s.c := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have had : s.a ≠ s.d := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hae : s.a ≠ s.e := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hbc : s.b ≠ s.c := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hbd : s.b ≠ s.d := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hbe : s.b ≠ s.e := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hcd : s.c ≠ s.d := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hce : s.c ≠ s.e := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hde : s.d ≠ s.e := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hba : s.b ≠ s.a := fun h => hab h.symm
  have hca : s.c ≠ s.a := fun h => hac h.symm
  have hda : s.d ≠ s.a := fun h => had h.symm
  have hea : s.e ≠ s.a := fun h => hae h.symm
  have hcb : s.c ≠ s.b := fun h => hbc h.symm
  have hdb : s.d ≠ s.b := fun h => hbd h.symm
  have heb : s.e ≠ s.b := fun h => hbe h.symm
  have hdc : s.d ≠ s.c := fun h => hcd h.symm
  have hec : s.e ≠ s.c := fun h => hce h.symm
  have hed : s.e ≠ s.d := fun h => hde h.symm

  have hA :=
    s.replace_vertexDegree_balance K hlegal s.a
  have hB :=
    s.replace_vertexDegree_balance K hlegal s.b
  have hC :=
    s.replace_vertexDegree_balance K hlegal s.c
  have hD :=
    s.replace_vertexDegree_balance K hlegal s.d
  have hE :=
    s.replace_vertexDegree_balance K hlegal s.e

  simp [
    Move23Site.leftTet,
    Move23Site.rightTet,
    Move23Site.newTet₀,
    Move23Site.newTet₁,
    Move23Site.newTet₂,
    Tet.verts,
    hab, hac, had, hae,
    hbc, hbd, hbe,
    hcd, hce, hde,
    hba, hca, hda, hea,
    hcb, hdb, heb,
    hdc, hec, hed
  ] at hA hB hC hD hE

  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega


theorem Move23Site.replace_vertexDegree_offSite
    (s : Move23Site) (K : Triangulation)
    (hlegal : s.LegalIn K)
    (v : Nat)
    (hva : v ≠ s.a)
    (hvb : v ≠ s.b)
    (hvc : v ≠ s.c)
    (hvd : v ≠ s.d)
    (hve : v ≠ s.e) :
    vertexDegree (s.replace K) v = vertexDegree K v := by

  have hav : s.a ≠ v := by
    intro h
    exact hva h.symm

  have hbv : s.b ≠ v := by
    intro h
    exact hvb h.symm

  have hcv : s.c ≠ v := by
    intro h
    exact hvc h.symm

  have hdv : s.d ≠ v := by
    intro h
    exact hvd h.symm

  have hev : s.e ≠ v := by
    intro h
    exact hve h.symm

  have h :=
    s.replace_vertexDegree_balance K hlegal v

  simp [
    Move23Site.leftTet,
    Move23Site.rightTet,
    Move23Site.newTet₀,
    Move23Site.newTet₁,
    Move23Site.newTet₂,
    Tet.verts,
    hav, hbv, hcv, hdv, hev
  ] at h

  omega


theorem Move23Site.replace_vertexSupport_mem_iff
    (s : Move23Site) (K : Triangulation)
    (hlegal : s.LegalIn K)
    (v : Nat) :
    v ∈ vertexSupport (s.replace K) ↔
      v ∈ vertexSupport K := by

  have hsupportDegree :
      ∀ (J : Triangulation) (x : Nat),
        x ∈ vertexSupport J ↔ 0 < vertexDegree J x := by
    intro J x
    rw [mem_vertexSupport_iff]
    change x ∈ allVerts J ↔ 0 < (allVerts J).count x
    simp

  have hrealized : s.RealizedIn K := hlegal.1
  rcases hrealized with ⟨hleft, hright⟩
  rcases hleft with ⟨τd, hτdK, hτdMatch⟩
  rcases hright with ⟨τe, hτeK, hτeMatch⟩

  have hdTarget : s.d ∈ s.leftTet.verts := by
    simp [Move23Site.leftTet, Tet.verts]

  have heTarget : s.e ∈ s.rightTet.verts := by
    simp [Move23Site.rightTet, Tet.verts]

  have hdTau : s.d ∈ τd.verts :=
    (hτdMatch s.d).2 hdTarget

  have heTau : s.e ∈ τe.verts :=
    (hτeMatch s.e).2 heTarget

  have hdAll : s.d ∈ allVerts K := by
    simp only [allVerts, List.mem_flatMap]
    exact ⟨τd, hτdK, hdTau⟩

  have heAll : s.e ∈ allVerts K := by
    simp only [allVerts, List.mem_flatMap]
    exact ⟨τe, hτeK, heTau⟩

  have hdSupport : s.d ∈ vertexSupport K :=
    (mem_vertexSupport_iff K s.d).2 hdAll

  have heSupport : s.e ∈ vertexSupport K :=
    (mem_vertexSupport_iff K s.e).2 heAll

  have hdPos : 0 < vertexDegree K s.d :=
    (hsupportDegree K s.d).1 hdSupport

  have hePos : 0 < vertexDegree K s.e :=
    (hsupportDegree K s.e).1 heSupport

  have hsite :=
    s.replace_vertexDegree_site K hlegal

  rcases hsite with
    ⟨ha, hb, hc, hd, he⟩

  rw [
    hsupportDegree (s.replace K) v,
    hsupportDegree K v
  ]

  by_cases hva : v = s.a
  · subst v
    rw [ha]

  by_cases hvb : v = s.b
  · subst v
    rw [hb]

  by_cases hvc : v = s.c
  · subst v
    rw [hc]

  by_cases hvd : v = s.d
  · subst v
    constructor
    · intro _
      exact hdPos
    · intro _
      omega

  by_cases hve : v = s.e
  · subst v
    constructor
    · intro _
      exact hePos
    · intro _
      omega

  have hoff :=
    s.replace_vertexDegree_offSite
      K hlegal v hva hvb hvc hvd hve

  rw [hoff]


theorem eraseDups_nodup_nat :
    ∀ xs : List Nat, xs.eraseDups.Nodup
  | [] => by
      simp
  | x :: xs => by
      rw [List.eraseDups_cons]

      apply List.Nodup.cons
      · intro hx

        have hxFilter :
            x ∈ List.filter (fun b : Nat => ! b == x) xs := by
          exact (List.mem_eraseDups.mp hx)

        simp at hxFilter

      · exact
          eraseDups_nodup_nat
            (List.filter (fun b : Nat => ! b == x) xs)
termination_by xs => xs.length
decreasing_by
  have hle :
      (List.filter (fun b : Nat => ! b == x) xs).length ≤
        xs.length :=
    List.length_filter_le
      (fun b : Nat => ! b == x) xs

  simpa using Nat.lt_succ_of_le hle


theorem phiSupport_eq_finset_sum
    (K : Triangulation) :
    PhiSupport K =
      ∑ v ∈ (vertexSupport K).toFinset,
        vertexDefect K v := by
  unfold PhiSupport

  have hnodup : (vertexSupport K).Nodup := by
    unfold vertexSupport
    exact eraseDups_nodup_nat (allVerts K)

  have aux :
      ∀ (xs : List Nat) (acc : Nat),
        xs.Nodup →
        xs.foldl
            (fun a v => a + vertexDefect K v) acc =
          acc +
            ∑ v ∈ xs.toFinset,
              vertexDefect K v := by
    intro xs
    induction xs with
    | nil =>
        intro acc _
        simp
    | cons x xs ih =>
        intro acc h
        have hh : x ∉ xs ∧ xs.Nodup := by
          simpa using h
        rcases hh with ⟨hx, hxs⟩

        simp only [List.foldl]
        rw [ih (acc + vertexDefect K x) hxs]
        simp [hx, Nat.add_assoc]

  simpa using aux (vertexSupport K) 0 hnodup


theorem Move23Site.replace_PhiSupport_balance
    (s : Move23Site) (K : Triangulation)
    (hlegal : s.LegalIn K) :
    PhiSupport K +
        vertexDefect (s.replace K) s.d +
        vertexDefect (s.replace K) s.e =
      PhiSupport (s.replace K) +
        vertexDefect K s.d +
        vertexDefect K s.e := by

  let S : Finset Nat :=
    (vertexSupport K).toFinset

  have hSupportFinset :
      (vertexSupport (s.replace K)).toFinset = S := by
    ext x
    simpa [S] using
      s.replace_vertexSupport_mem_iff K hlegal x

  have hrealized : s.RealizedIn K :=
    hlegal.1

  rcases hrealized with ⟨hleft, hright⟩
  rcases hleft with ⟨τd, hτdK, hτdMatch⟩
  rcases hright with ⟨τe, hτeK, hτeMatch⟩

  have hdTarget : s.d ∈ s.leftTet.verts := by
    simp [Move23Site.leftTet, Tet.verts]

  have heTarget : s.e ∈ s.rightTet.verts := by
    simp [Move23Site.rightTet, Tet.verts]

  have hdTau : s.d ∈ τd.verts :=
    (hτdMatch s.d).2 hdTarget

  have heTau : s.e ∈ τe.verts :=
    (hτeMatch s.e).2 heTarget

  have hdSupport : s.d ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨τd, hτdK, hdTau⟩

  have heSupport : s.e ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨τe, hτeK, heTau⟩

  have hdS : s.d ∈ S := by
    simpa [S] using hdSupport

  have heS : s.e ∈ S := by
    simpa [S] using heSupport

  have hde : s.d ≠ s.e := by
    intro h
    have hs := s.distinct
    simp [h] at hs

  have hed : s.e ≠ s.d := by
    intro h
    exact hde h.symm

  have heErase : s.e ∈ S.erase s.d := by
    simp [heS, hed]

  have hsite :=
    s.replace_vertexDegree_site K hlegal

  rcases hsite with
    ⟨ha, hb, hc, hd, he⟩

  have hDegreeExceptDE :
      ∀ v : Nat,
        v ≠ s.d →
        v ≠ s.e →
        vertexDegree (s.replace K) v =
          vertexDegree K v := by
    intro v hvd hve

    by_cases hva : v = s.a
    · subst v
      exact ha

    by_cases hvb : v = s.b
    · subst v
      exact hb

    by_cases hvc : v = s.c
    · subst v
      exact hc

    exact
      s.replace_vertexDegree_offSite
        K hlegal v hva hvb hvc hvd hve

  have hDefectExceptDE :
      ∀ v : Nat,
        v ≠ s.d →
        v ≠ s.e →
        vertexDefect (s.replace K) v =
          vertexDefect K v := by
    intro v hvd hve
    unfold vertexDefect
    rw [hDegreeExceptDE v hvd hve]

  have hRest :
      (∑ v ∈ (S.erase s.d).erase s.e,
          vertexDefect (s.replace K) v) =
        ∑ v ∈ (S.erase s.d).erase s.e,
          vertexDefect K v := by
    apply Finset.sum_congr rfl
    intro v hv

    have hve : v ≠ s.e :=
      (Finset.mem_erase.mp hv).1

    have hvEraseD : v ∈ S.erase s.d :=
      (Finset.mem_erase.mp hv).2

    have hvd : v ≠ s.d :=
      (Finset.mem_erase.mp hvEraseD).1

    exact hDefectExceptDE v hvd hve

  have hOld :
      (∑ v ∈ S, vertexDefect K v) =
        (∑ v ∈ (S.erase s.d).erase s.e,
            vertexDefect K v) +
          vertexDefect K s.e +
          vertexDefect K s.d := by
    calc
      (∑ v ∈ S, vertexDefect K v) =
          (∑ v ∈ S.erase s.d,
              vertexDefect K v) +
            vertexDefect K s.d :=
        (Finset.sum_erase_add
          S (vertexDefect K) hdS).symm

      _ =
          ((∑ v ∈ (S.erase s.d).erase s.e,
              vertexDefect K v) +
            vertexDefect K s.e) +
            vertexDefect K s.d := by
        rw [
          (Finset.sum_erase_add
            (S.erase s.d)
            (vertexDefect K)
            heErase).symm
        ]

  have hNew :
      (∑ v ∈ S, vertexDefect (s.replace K) v) =
        (∑ v ∈ (S.erase s.d).erase s.e,
            vertexDefect (s.replace K) v) +
          vertexDefect (s.replace K) s.e +
          vertexDefect (s.replace K) s.d := by
    calc
      (∑ v ∈ S, vertexDefect (s.replace K) v) =
          (∑ v ∈ S.erase s.d,
              vertexDefect (s.replace K) v) +
            vertexDefect (s.replace K) s.d :=
        (Finset.sum_erase_add
          S
          (vertexDefect (s.replace K))
          hdS).symm

      _ =
          ((∑ v ∈ (S.erase s.d).erase s.e,
              vertexDefect (s.replace K) v) +
            vertexDefect (s.replace K) s.e) +
            vertexDefect (s.replace K) s.d := by
        rw [
          (Finset.sum_erase_add
            (S.erase s.d)
            (vertexDefect (s.replace K))
            heErase).symm
        ]

  rw [
    phiSupport_eq_finset_sum K,
    phiSupport_eq_finset_sum (s.replace K),
    hSupportFinset
  ]

  change
    (∑ v ∈ S, vertexDefect K v) +
        vertexDefect (s.replace K) s.d +
        vertexDefect (s.replace K) s.e =
      (∑ v ∈ S, vertexDefect (s.replace K) v) +
        vertexDefect K s.d +
        vertexDefect K s.e

  rw [hOld, hNew, hRest]
  ac_rfl


theorem vertexDefect_of_degree_add_two
    (K K' : Triangulation) (v : Nat)
    (hdeg :
      vertexDegree K' v =
        vertexDegree K v + 2) :
    (vertexDegree K v ≤ 2 →
      vertexDefect K' v + 2 =
        vertexDefect K v) ∧
    (vertexDegree K v = 3 →
      vertexDefect K' v =
        vertexDefect K v) ∧
    (4 ≤ vertexDegree K v →
      vertexDefect K' v =
        vertexDefect K v + 2) := by

  constructor
  · intro hle

    have hcases :
        vertexDegree K v = 0 ∨
        vertexDegree K v = 1 ∨
        vertexDegree K v = 2 := by
      omega

    rcases hcases with h0 | h1 | h2
    · norm_num [
        vertexDefect,
        targetDegree,
        hdeg,
        h0
      ]
    · norm_num [
        vertexDefect,
        targetDegree,
        hdeg,
        h1
      ]
    · norm_num [
        vertexDefect,
        targetDegree,
        hdeg,
        h2
      ]

  constructor
  · intro h3

    norm_num [
      vertexDefect,
      targetDegree,
      hdeg,
      h3
    ]

  · intro h4

    have hnonneg :
        (0 : Int) ≤
          (vertexDegree K v : Int) - 4 := by
      omega

    unfold vertexDefect
    rw [hdeg]

    change
      Int.natAbs
          ((((vertexDegree K v + 2 : Nat) : Int) - 4)) =
        Int.natAbs
            (((vertexDegree K v : Int) - 4)) +
          2

    have hrewrite :
        (((vertexDegree K v + 2 : Nat) : Int) - 4) =
          ((vertexDegree K v : Int) - 4) + 2 := by
      omega

    rw [hrewrite]

    rw [
      Int.natAbs_add_of_nonneg
        hnonneg
        (by norm_num)
    ]

    norm_num


theorem Move23Site.replace_PhiSupport_sign
    (s : Move23Site) (K : Triangulation)
    (hlegal : s.LegalIn K) :
    (
      PhiSupport (s.replace K) < PhiSupport K ↔
        vertexDegree K s.d ≤ 3 ∧
        vertexDegree K s.e ≤ 3 ∧
        (
          vertexDegree K s.d ≤ 2 ∨
          vertexDegree K s.e ≤ 2
        )
    ) ∧
    (
      PhiSupport (s.replace K) = PhiSupport K ↔
        (
          vertexDegree K s.d = 3 ∧
          vertexDegree K s.e = 3
        ) ∨
        (
          vertexDegree K s.d ≤ 2 ∧
          4 ≤ vertexDegree K s.e
        ) ∨
        (
          4 ≤ vertexDegree K s.d ∧
          vertexDegree K s.e ≤ 2
        )
    ) ∧
    (
      PhiSupport K < PhiSupport (s.replace K) ↔
        3 ≤ vertexDegree K s.d ∧
        3 ≤ vertexDegree K s.e ∧
        (
          4 ≤ vertexDegree K s.d ∨
          4 ≤ vertexDegree K s.e
        )
    ) := by

  have hsite :=
    s.replace_vertexDegree_site K hlegal

  rcases hsite with
    ⟨ha, hb, hc, hd, he⟩

  have hbalance :=
    s.replace_PhiSupport_balance K hlegal

  have hdClass :=
    vertexDefect_of_degree_add_two
      K (s.replace K) s.d hd

  have heClass :=
    vertexDefect_of_degree_add_two
      K (s.replace K) s.e he

  have hdCases :
      vertexDegree K s.d ≤ 2 ∨
      vertexDegree K s.d = 3 ∨
      4 ≤ vertexDegree K s.d := by
    omega

  have heCases :
      vertexDegree K s.e ≤ 2 ∨
      vertexDegree K s.e = 3 ∨
      4 ≤ vertexDegree K s.e := by
    omega

  rcases hdCases with hdLow | hdMid | hdHigh

  · rcases heCases with heLow | heMid | heHigh

    · have hdRel := hdClass.1 hdLow
      have heRel := heClass.1 heLow

      constructor
      · constructor <;> omega

      constructor
      · constructor <;> omega
      · constructor <;> omega

    · have hdRel := hdClass.1 hdLow
      have heRel := heClass.2.1 heMid

      constructor
      · constructor <;> omega

      constructor
      · constructor <;> omega
      · constructor <;> omega

    · have hdRel := hdClass.1 hdLow
      have heRel := heClass.2.2 heHigh

      constructor
      · constructor <;> omega

      constructor
      · constructor <;> omega
      · constructor <;> omega

  · rcases heCases with heLow | heMid | heHigh

    · have hdRel := hdClass.2.1 hdMid
      have heRel := heClass.1 heLow

      constructor
      · constructor <;> omega

      constructor
      · constructor <;> omega
      · constructor <;> omega

    · have hdRel := hdClass.2.1 hdMid
      have heRel := heClass.2.1 heMid

      constructor
      · constructor <;> omega

      constructor
      · constructor <;> omega
      · constructor <;> omega

    · have hdRel := hdClass.2.1 hdMid
      have heRel := heClass.2.2 heHigh

      constructor
      · constructor <;> omega

      constructor
      · constructor <;> omega
      · constructor <;> omega

  · rcases heCases with heLow | heMid | heHigh

    · have hdRel := hdClass.2.2 hdHigh
      have heRel := heClass.1 heLow

      constructor
      · constructor <;> omega

      constructor
      · constructor <;> omega
      · constructor <;> omega

    · have hdRel := hdClass.2.2 hdHigh
      have heRel := heClass.2.1 heMid

      constructor
      · constructor <;> omega

      constructor
      · constructor <;> omega
      · constructor <;> omega

    · have hdRel := hdClass.2.2 hdHigh
      have heRel := heClass.2.2 heHigh

      constructor
      · constructor <;> omega

      constructor
      · constructor <;> omega
      · constructor <;> omega


theorem exists_positive_PhiSupport_without_legal_move23 :
    ∃ K : Triangulation,
      PhiSupport K = 12 ∧
      ∀ s : Move23Site, ¬ s.LegalIn K := by

  let τ : Tet :=
    ⟨0, 1, 2, 3⟩

  let K : Triangulation :=
    { tets := [τ] }

  refine ⟨K, ?_, ?_⟩

  · native_decide

  · intro s hlegal

    have hrealized : s.RealizedIn K :=
      hlegal.1

    rcases hrealized with
      ⟨hleft, hright⟩

    rcases hleft with
      ⟨τL, hτLmem, hL⟩

    rcases hright with
      ⟨τR, hτRmem, hR⟩

    have hτL : τL = τ := by
      simpa [K] using hτLmem

    have hτR : τR = τ := by
      simpa [K] using hτRmem

    subst τL
    subst τR

    apply s.leftTet_not_same_rightTet

    intro v
    constructor

    · intro hvLeft
      have hvTau : v ∈ τ.verts :=
        (hL v).2 hvLeft
      exact (hR v).1 hvTau

    · intro hvRight
      have hvTau : v ∈ τ.verts :=
        (hR v).2 hvRight
      exact (hL v).1 hvTau

end Poincare
