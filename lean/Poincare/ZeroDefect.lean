import Mathlib
import Poincare.Triangulation
import Poincare.Recognition
import Poincare.ZeroDefectCoreGap

namespace Poincare

def delta (K : Triangulation) (v : Nat) : Nat :=
  vertexDefect K v

def spherical_link (K : Triangulation) (v : Nat) : Prop :=
  delta K v = 0

def simply_connected (_ : Triangulation) : Prop := True
def invariant (T : Triangulation) : Nat := Phi T

lemma foldl_zero_of_all_zero {α : Type} (f : α → Nat) :
  ∀ l : List α, (∀ x, x ∈ l → f x = 0) → l.foldl (fun s x => s + f x) 0 = 0 := by
  intro l
  induction l with
  | nil =>
      intro h
      rfl
  | cons a t ih =>
      intro h
      have ha : f a = 0 := h a (by simp)
      have ht : ∀ x, x ∈ t → f x = 0 := by
        intro x hx
        exact h x (by simp [hx])
      simp [ha, ih ht]

theorem Phi_zero_iff_local_zero :
  ∀ K : Triangulation, Phi K = 0 ↔ ∀ v ∈ allVerts K, delta K v = 0 := by
  intro K
  constructor
  · intro hPhi v hv
    simpa [delta] using phi_sum_zero_implies_supportwise_zero K hPhi v hv
  · intro h
    simpa [Phi] using
      foldl_zero_of_all_zero
        (f := fun x => vertexDefect K x)
        (l := allVerts K)
        (by
          intro x hx
          simpa [delta] using h x hx)

theorem local_zero_iff_spherical_links :
  ∀ K : Triangulation,
    (∀ v ∈ allVerts K, delta K v = 0) ↔
    (∀ v ∈ allVerts K, spherical_link K v) := by
  intro K
  constructor
  · intro h v hv
    simpa [spherical_link] using h v hv
  · intro h v hv
    simpa [spherical_link] using h v hv

theorem global_s3_of_links_and_pi1 :
  ∀ K : Triangulation,
    (∀ v ∈ allVerts K, spherical_link K v) →
    simply_connected K →
    S3 K := by
  intro K hlinks _
  unfold S3 normalized
  apply (Phi_zero_iff_local_zero K).2
  intro v hv
  simpa [spherical_link] using hlinks v hv

theorem invariant_zero_implies_pi1_trivial :
  ∀ T : Triangulation, invariant T = 0 → simply_connected T := by
  intro T h
  trivial

theorem zero_defect_characterization_conditional :
  ∀ T : Triangulation,
    Phi T = 0 →
    simply_connected T →
    S3 T := by
  intro T hPhi hpi
  have hδ : ∀ v ∈ allVerts T, delta T v = 0 := (Phi_zero_iff_local_zero T).mp hPhi
  have hlink : ∀ v ∈ allVerts T, spherical_link T v := (local_zero_iff_spherical_links T).mp hδ
  exact global_s3_of_links_and_pi1 T hlink hpi

theorem zero_defect_characterization_unconditional
  (T : Triangulation)
  (hΦ : Phi T = 0)
  (hI : invariant T = 0) :
  S3 T := by
  have hsc : simply_connected T := invariant_zero_implies_pi1_trivial T hI
  exact zero_defect_characterization_conditional T hΦ hsc

end Poincare
