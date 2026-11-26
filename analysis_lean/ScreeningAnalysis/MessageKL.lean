import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Disclosure lemma on finite alphabets, with arbitrary real probabilities.
The output contains the free record even when the encoder sends nothing. -/
namespace ScreeningAnalysis.MessageKL

open scoped BigOperators

noncomputable def term (p q : ℝ) := p * Real.log (p / q)
noncomputable def chi (p q : ℝ) := (p-q)^2 / q

private theorem log_bound {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (support : q = 0 → p = 0) : term p q ≤ p-q + chi p q := by
  rcases eq_or_lt_of_le hq with hz | hq
  · have hp0 := support hz.symm
    simp [term, chi, hz.symm, hp0]
  rcases eq_or_lt_of_le hp with hz | hp'
  · rw [← hz]
    simp [term, chi, sq, hq.ne']
  · have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hp' hq)) hp
    calc term p q ≤ p * (p/q-1) := h
         _ = p-q + chi p q := by unfold chi; field_simp; ring

private theorem square_budget {p q z e : ℝ} (hq : 0 ≤ q) (hz : 0 ≤ z) (he : 0 ≤ e)
    (h₁ : |p-q| ≤ e*q) (h₂ : |p-q| ≤ e*z) : chi p q ≤ e^2*z := by
  rcases eq_or_lt_of_le hq with hq | hq
  · simp [chi, ← hq, mul_nonneg (sq_nonneg e) hz]
  · apply (div_le_iff₀ hq).mpr
    have h := mul_le_mul h₁ h₂ (abs_nonneg _) (mul_nonneg he hq.le)
    rw [← sq, sq_abs] at h
    nlinarith only [h]

private theorem single_block {A : Type*} [Fintype A]
    (p q : A → ℝ) (s t e : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/2) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (band : ∀ a, |p a - q a| ≤ e*q a) (silent : |s-t| ≤ e*t)
    (free : s + ∑ a, p a = t + ∑ a, q a) :
    term s t + ∑ a, term (p a) (q a) ≤ 4*e^2 * ∑ a, p a := by
  have d : s-t = -(∑ a, (p a - q a)) := by rw [Finset.sum_sub_distrib]; linarith
  have zm : |s-t| ≤ e * ∑ a, q a := by
    rw [d, abs_neg, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => band a)
  have zq : 0 ≤ ∑ a, q a := Finset.sum_nonneg fun a _ => hq a
  have tbound := square_budget ht zq he silent zm
  have bound (a : A) := square_budget (hq a) (hq a) he (band a) (band a)
  have supported {x y : ℝ} (b : |x-y| ≤ e*y) (h : y = 0) : x = 0 := by
    simpa [h] using b
  have marked : (∑ a, term (p a) (q a)) ≤
      (∑ a, p a) - (∑ a, q a) + e^2 * ∑ a, q a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ =>
      (log_bound (hp a) (hq a) (supported (band a))).trans
        (add_le_add_left (bound a) _)
  have sent : (∑ a, q a) ≤ 2 * ∑ a, p a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have lower := (abs_le.mp (band a)).1
    nlinarith only [lower, mul_le_mul_of_nonneg_right he' (hq a)]
  have paid := mul_le_mul_of_nonneg_left sent (sq_nonneg e)
  have unmarked := log_bound hs ht (supported silent)
  linarith only [marked, unmarked, tbound, free, paid]

/-- The common free record may have zero mass; none of the proof conditions
divide by that mass. Marked letters from different records may have different laws. -/
theorem output_information {F A : Type*} [Fintype F] [Fintype A]
    (p q : F → A → ℝ) (s t : F → ℝ) (e : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/2)
    (hs : ∀ f, 0 ≤ s f) (ht : ∀ f, 0 ≤ t f)
    (hp : ∀ f a, 0 ≤ p f a) (hq : ∀ f a, 0 ≤ q f a)
    (band : ∀ f a, |p f a - q f a| ≤ e*q f a)
    (silent : ∀ f, |s f-t f| ≤ e*t f)
    (free : ∀ f, s f + ∑ a, p f a = t f + ∑ a, q f a) :
    (∑ f, (term (s f) (t f) + ∑ a, term (p f a) (q f a))) ≤
      4*e^2 * ∑ f, ∑ a, p f a := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun f _ =>
    single_block (p f) (q f) (s f) (t f) e he he' (hs f) (ht f)
      (hp f) (hq f) (band f) (silent f) (free f)

noncomputable def through {X : Type*} [Fintype X] (p k : X → ℝ) := ∑ x, p x * k x

private theorem through_band {X : Type*} [Fintype X] {p q : X → ℝ} {e : ℝ}
    (band : ∀ x, |p x-q x| ≤ e*q x) (k : X → ℝ) (hk : ∀ x, 0 ≤ k x) :
    |through p k - through q k| ≤ e * through q k := by
  unfold through
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [← sub_mul, abs_mul, abs_of_nonneg (hk x), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (band x) (hk x)

private theorem through_free {X A : Type*} [Fintype X] [Fintype A]
    (p k0 kfree : X → ℝ) (k : X → A → ℝ) (splits : ∀ x, k0 x + ∑ a, k x a = kfree x) :
    through p k0 + ∑ a, through p (fun x => k x a) = through p kfree := by
  unfold through
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, ← mul_add, splits]

/-- Lemma 13 for finite real-valued input, free-record and message alphabets.
The common encoder is arbitrary: each send probability may depend on x.
A normalized probability kernel has k0(x,f)+Σa k(x,f,a) equal to the
indicator of its public record; allowing a randomized free record also works.
Finite nonnegative masses need not be normalized for this homogeneous bound. -/
theorem encoder_information {X F A : Type*} [Fintype X] [Fintype F] [Fintype A]
    (p q : X → ℝ) (k0 kfree : X → F → ℝ) (k : X → F → A → ℝ) (e : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (h0 : ∀ x f, 0 ≤ k0 x f) (hk : ∀ x f a, 0 ≤ k x f a)
    (he : 0 ≤ e) (he' : e ≤ 1/2) (band : ∀ x, |p x-q x| ≤ e*q x)
    (splits : ∀ x f, k0 x f + ∑ a, k x f a = kfree x f)
    (free : ∀ f, through p (fun x => kfree x f) = through q (fun x => kfree x f)) :
    (∑ f, (term (through p (fun x => k0 x f)) (through q (fun x => k0 x f)) +
      ∑ a, term (through p (fun x => k x f a)) (through q (fun x => k x f a)))) ≤
      4*e^2 * ∑ f, ∑ a, through p (fun x => k x f a) := by
  have pos (w v : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ x, 0 ≤ v x) :
      0 ≤ through w v := Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hv x)
  apply output_information _ _ _ _ _ he he'
  · exact fun f => pos _ _ hp (fun x => h0 x f)
  · exact fun f => pos _ _ hq (fun x => h0 x f)
  · exact fun f a => pos _ _ hp (fun x => hk x f a)
  · exact fun f a => pos _ _ hq (fun x => hk x f a)
  · exact fun f a => through_band band _ (fun x => hk x f a)
  · exact fun f => through_band band _ (fun x => h0 x f)
  · intro f
    rw [through_free p _ _ _ (fun x => splits x f),
      through_free q _ _ _ (fun x => splits x f), free]

end ScreeningAnalysis.MessageKL
