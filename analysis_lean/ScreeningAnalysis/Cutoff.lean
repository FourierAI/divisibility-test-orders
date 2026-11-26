import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite two-law lower bound in Proposition 40. Rank, fallback cost, and
randomization are explicit. The separate integer-realization and asymptotic
estimates in the manuscript are outside the scope of this module. -/

namespace ScreeningAnalysis.Cutoff

open Finset

def survival (q pair : ℝ) (t : ℕ) : ℝ :=
  1 - t * q + pair * (t.choose 2 : ℝ)

/-- The cost of attempting t tests, charging B when all t tests miss. -/
def cost (q pair B : ℝ) (t : ℕ) : ℝ :=
  (∑ i ∈ range t, survival q pair i) + B * survival q pair t

def center (q : ℝ) (t : ℕ) : ℝ := q ^ 2 * (t.choose 3 : ℝ)

def shift (d B : ℝ) (t : ℕ) : ℝ :=
  d * ((t.choose 3 : ℝ) + B * (t.choose 2 : ℝ))

private theorem cost_formula (q pair B : ℝ) (t : ℕ) (h : B * q = 1) :
    cost q pair B t = B + pair * (t.choose 3 : ℝ) +
      (B * pair - q) * (t.choose 2 : ℝ) := by
  induction t with
  | zero => simp [cost, survival]
  | succ n ih =>
    unfold cost at *
    rw [sum_range_succ]
    have h2 : ((n+1).choose 2 : ℝ) = n + (n.choose 2 : ℝ) := by
      rw [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_one_right]
    have h3 : ((n+1).choose 3 : ℝ) = (n.choose 2 : ℝ) + (n.choose 3 : ℝ) := by
      rw [Nat.choose_succ_succ, Nat.cast_add]
    unfold survival at *
    rw [h2,h3,Nat.cast_succ]
    linarith only [ih,h]

theorem signed_cost (q e B : ℝ) (t : ℕ) (h : B * q = 1) :
    cost q (q^2+e) B t = B + center q t + shift e B t := by
  rw [cost_formula q _ B t h]
  unfold center shift
  have cancel : B*q^2 = q := by rw [pow_two, ← mul_assoc, h, one_mul]
  rw [mul_add,cancel]
  ring

/-- Arbitrary random cutoff on 0,…,m, with its common nonnegative probability
weights under both laws. Comparing with the feasible actions 0 and m suffices. -/
theorem randomized_cutoff_gap (q d B : ℝ) (m : ℕ) (h : B*q=1)
    (w : Fin (m+1) → ℝ) (hw : ∀ i, 0 ≤ w i) (unit : ∑ i, w i = 1) :
    let loss (pair : ℝ) := ∑ i, w i * cost q pair B i.val
    let gain := shift d B m - center q m
    gain / 2 ≤ max (loss (q^2+d) - cost q (q^2+d) B 0)
      (loss (q^2-d) - cost q (q^2-d) B m) := by
  dsimp only
  have point (i : Fin (m+1)) :
      2*B*w i ≤ w i*cost q (q^2+d) B i.val + w i*cost q (q^2-d) B i.val := by
    rw [sub_eq_add_neg, signed_cost q d B _ h, signed_cost q (-d) B _ h]
    unfold center shift
    have nn : 0 ≤ w i * q^2 * (i.val.choose 3 : ℝ) := mul_nonneg (mul_nonneg (hw i) (sq_nonneg q)) (Nat.cast_nonneg _)
    linarith only [nn]
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => point i)
  rw [← Finset.mul_sum, unit, mul_one, Finset.sum_add_distrib] at total
  have zero : cost q (q^2+d) B 0 = B := by simp [cost, survival]
  have last : cost q (q^2-d) B m = B + center q m - shift d B m := by
    rw [sub_eq_add_neg, signed_cost q (-d) B m h]; unfold shift; ring
  rw [zero,last]
  exact le_of_not_gt (by
    intro contra
    have h₁ := lt_of_le_of_lt (le_max_left _ _) contra
    have h₂ := lt_of_le_of_lt (le_max_right _ _) contra
    linarith only [h₁, h₂, total])

end ScreeningAnalysis.Cutoff
