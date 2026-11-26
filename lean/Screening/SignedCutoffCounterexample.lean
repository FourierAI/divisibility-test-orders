import Screening.IntervalCounts
import Screening.ScreeningCost

/-!
The relative-cost proposition `prop:relative` in `screening_orders.tex`
only bounds the *largest* of the consecutive odd integers. On its literal
signed domain, take the uniform law on -3M,-3M+2, with M the product of
the menu primes. Each test detects the first word and misses the second.
The expected costs below are multiplied by two to retain exact integers.
The positive interval [2L,4L) used in the main theorems excludes this family.
-/
namespace Screening.SignedCutoffCounterexample

open Screening.IntervalCounts Screening.ScreeningCost

def OddPrimeMenu (ps : List Nat) : Prop :=
  ps.Nodup ∧ ∀ p ∈ ps, IsPrime p ∧ p%2 = 1

private theorem prime_divisor (n : Nat) (hn : 2 ≤ n) : ∃ p, IsPrime p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : IsPrime n
    · exact ⟨n, h, Nat.dvd_refl n⟩
    · have bad : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
        apply Classical.byContradiction
        intro neg
        apply h
        refine ⟨hn, fun d hd => ?_⟩
        by_cases one : d = 1
        · exact Or.inl one
        by_cases same : d = n
        · exact Or.inr same
        exact False.elim (neg ⟨d, hd, one, same⟩)
      obtain ⟨d, hd, notOne, notSame⟩ := bad
      have pos := Nat.pos_of_dvd_of_pos hd (by omega)
      have le := Nat.le_of_dvd (by omega) hd
      obtain ⟨p, hp, divides⟩ := ih d (by omega) (by omega)
      exact ⟨p, hp, Nat.dvd_trans divides hd⟩

private theorem divides_product {ps : List Nat} (h : OddPrimeMenu ps) {p : Nat}
    (hp : p ∈ ps) : p ∣ product ps :=
  ((product_dvd_iff ps h.1 (fun j hj => (h.2 j hj).1) _).mp (Nat.dvd_refl _)) p hp

/-- The counterexamples are unbounded in menu length. -/
theorem menus_exist (m : Nat) : ∃ ps, OddPrimeMenu ps ∧ ps.length = m := by
  induction m with
  | zero => exact ⟨[], ⟨by simp, by simp⟩, rfl⟩
  | succ m ih =>
    obtain ⟨ps, menu, size⟩ := ih
    have odd := odd_product ps (fun j hj => (menu.2 j hj).2)
    obtain ⟨p, prime, hd⟩ := prime_divisor (2*product ps+1) (by omega)
    have hp := prime.1
    have fresh : p ∉ ps := by
      intro inp
      have aux := Nat.dvd_sub hd (Nat.dvd_trans (divides_product menu inp)
        (Nat.dvd_mul_left (product ps) 2))
      simp only [Nat.add_sub_cancel_left] at aux
      have := Nat.eq_one_of_dvd_one aux
      omega
    have po : p%2 = 1 := by
      apply Classical.byContradiction
      intro bad
      have ev := Nat.dvd_of_mod_eq_zero (show p%2 = 0 by omega)
      obtain ⟨k, hk⟩ := Nat.dvd_trans ev hd
      omega
    refine ⟨p::ps, ⟨List.nodup_cons.mpr ⟨fresh, menu.1⟩, ?_⟩, by simp [size]⟩
    intro j hj
    rcases List.mem_cons.mp hj with same | mem
    · exact same ▸ ⟨prime, po⟩
    · exact menu.2 j mem

def first (ps : List Nat) : Int := -(3*(product ps : Int))
def second (ps : List Nat) : Int := first ps + 2
def hit (w : Int) (p : Nat) : Bool := decide ((p : Int) ∣ w)

/-- Both odd words are negative. The largest word satisfies the stated cap 4L=8. -/
theorem interval_conditions {ps : List Nat} (menu : OddPrimeMenu ps) :
    first ps % 2 = 1 ∧ second ps = first ps + 2 ∧ second ps % 2 = 1 ∧
      second ps < 0 ∧ second ps ≤ 8 := by
  have := odd_product ps (fun j hj => (menu.2 j hj).2)
  have odd : (product ps : Int) % 2 = 1 := by exact_mod_cast this
  simp only [second, first]
  constructor
  · omega
  refine ⟨True.intro, ?_, ?_, ?_⟩ <;> omega

/-- Every menu hit is proper in the signed sense 1<p<|w|. For each prime
exactly one of the two equally likely words hits, hence q=1/2. -/
theorem hits_exactly_first {ps : List Nat} (menu : OddPrimeMenu ps) {p : Nat}
    (mem : p ∈ ps) :
    hit (first ps) p = true ∧ hit (second ps) p = false ∧ 1 < p ∧ p < (first ps).natAbs := by
  have od := odd_product ps (fun j hj => (menu.2 j hj).2)
  have half := (menu.2 p mem).2
  have two := (menu.2 p mem).1.1
  have hd := divides_product menu mem
  have le := Nat.le_of_dvd (by omega) hd
  have divides : (p : Int) ∣ first ps := by
    apply Int.dvd_neg.mpr
    exact_mod_cast (Nat.dvd_trans hd (Nat.dvd_mul_left (product ps) 3))
  have misses : ¬ (p : Int) ∣ second ps := by
    intro hitsBoth
    have delta := Int.dvd_sub hitsBoth divides
    have dif : second ps - first ps = 2 := by unfold second; omega
    rw [dif] at delta
    have hd2 : p ∣ 2 := Int.ofNat_dvd.mp delta
    have := Nat.le_of_dvd (by decide) hd2
    omega
  refine ⟨by simp [hit,divides], by simp [hit,misses], by omega, ?_⟩
  simp [first, Int.natAbs_mul]
  omega

/-- Combined cost on the two equally weighted integer outcomes, fallback B=3. -/
noncomputable def twiceCost (ps order : List Nat) : Nat :=
  scan (hit (first ps)) 3 order + scan (hit (second ps)) 3 order

private theorem all_miss (f : Nat → Bool) (xs : List Nat) (h : ∀ i ∈ xs, f i = false) :
    scan f 3 xs = xs.length + 3 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have tail := ih (fun i hi => h i (by simp [hi]))
    simp only [scan,h x (by simp),Bool.false_eq_true,↓reduceIte,tail,List.length_cons]
    omega

theorem nonempty_plan_cost {ps : List Nat} (menu : OddPrimeMenu ps) (x : Nat) (xs : List Nat)
    (legal : ∀ p ∈ x::xs, p ∈ ps) : twiceCost ps (x::xs) = (x::xs).length + 4 := by
  have hx := (hits_exactly_first menu (legal x (by simp))).1
  have failed := all_miss (hit (second ps)) (x::xs)
    (fun i hi => (hits_exactly_first menu (legal i hi)).2.1)
  unfold twiceCost
  rw [failed]
  simp only [scan,hx,↓reduceIte]
  omega

/-- A singleton attains the global minimum 5/2 over every ordered subset,
including immediate fallback. When m>0 the full menu costs (m+4)/2. -/
theorem optimal_costs {ps : List Nat} (menu : OddPrimeMenu ps) (nonempty : ps ≠ []) :
    twiceCost ps ps = ps.length + 4 ∧
    (∃ p ∈ ps, twiceCost ps [p] = 5) ∧
    (∀ xs, (∀ p ∈ xs, p ∈ ps) → 5 ≤ twiceCost ps xs) := by
  cases ps with
  | nil => contradiction
  | cons x xs =>
    refine ⟨nonempty_plan_cost menu x xs (fun _ h => h),
      ⟨x,by simp,nonempty_plan_cost menu x [] (by simp)⟩,?_⟩
    intro ys legal
    cases ys with
    | nil => change 5 ≤ 3+3; decide
    | cons y ys => rw [nonempty_plan_cost menu y ys legal]; simp

/-- With Bq=3/2>1 the proposed rule takes the full menu. For every proposed
constant C its expected cost exceeds C times optimum on some signed interval. -/
theorem no_uniform_factor (C : Nat) :
    ∃ ps, OddPrimeMenu ps ∧ 5*C < twiceCost ps ps ∧
      (∃ p ∈ ps, twiceCost ps [p] = 5) ∧
      (∀ xs, (∀ p ∈ xs, p ∈ ps) → 5 ≤ twiceCost ps xs) := by
  obtain ⟨ps, menu, size⟩ := menus_exist (5*C+1)
  have nonempty : ps ≠ [] := by intro h; simp [h] at size
  obtain ⟨full, one, opt⟩ := optimal_costs menu nonempty
  exact ⟨ps, menu, by omega, one, opt⟩

end Screening.SignedCutoffCounterexample
