import Std
import Std.Internal.Rat

/-! The opening four-prime experiment, with equiprobable tickets representing
the two distributions. A test checks divisibility of an actual natural number.
All expected costs below are exact rational numbers. -/

namespace Screening.FourPrimes

open Std.Internal (Rat)

private def rationalNat (n : Nat) : Rat := (Int.ofNat n : Int)

inductive PrimeLabel where
  | three | five | seven | eleven
  deriving DecidableEq, BEq, Repr

open PrimeLabel

def prime : PrimeLabel → Nat
  | three => 3
  | five => 5
  | seven => 7
  | eleven => 11

def menu : List PrimeLabel := [three, five, seven, eleven]

inductive Source where
  | plus | minus
  deriving DecidableEq, Repr

/-- Each of the twelve positions has probability one twelfth. The positions
are grouped by their largest prime factor. -/
def tickets : Source → List Nat
  | .plus =>
    [3*5, 3*5, 3*7, 3*7, 3*7, 5*7, 3*11, 5*11, 5*11, 5*11, 7*11, 7*11]
  | .minus =>
    [3*5, 3*5, 3*7, 5*7, 5*7, 5*7, 3*11, 3*11, 3*11, 5*11, 7*11, 7*11]

def hits (n : Nat) : List PrimeLabel :=
  menu.filter (fun p => n % prime p == 0)

def countAndLargest (n : Nat) : Nat × Nat :=
  let factors := hits n
  (factors.length, (factors.map prime).foldl Nat.max 0)

theorem exact_joint_observations :
    (tickets .plus).map countAndLargest =
      [(2,5),(2,5),(2,7),(2,7),(2,7),(2,7),
       (2,11),(2,11),(2,11),(2,11),(2,11),(2,11)] ∧
    (tickets .plus).map countAndLargest = (tickets .minus).map countAndLargest := by decide

/-- Equal counts for every joint observation, even observations outside the support. -/
theorem identical_count_largest_laws (z : Nat × Nat) :
    ((tickets .plus).map countAndLargest).count z =
    ((tickets .minus).map countAndLargest).count z :=
  congrArg (fun xs : List (Nat × Nat) => xs.count z) exact_joint_observations.2

theorem marginal_is_one_half (s : Source) (p : PrimeLabel) :
    rationalNat ((tickets s).filter (fun n => n % prime p == 0)).length /
      rationalNat (tickets s).length = 1/2 := by
  cases s <;> cases p <;> decide

theorem two_hit_laws_differ :
    ((tickets .plus).map hits).count [three, seven] = 3 ∧
    ((tickets .minus).map hits).count [three, seven] = 1 := by decide

/-- A raw order has four slots, each containing a prime from the menu.
A complete order contains all four labels. -/
structure Order where
  a : PrimeLabel
  b : PrimeLabel
  c : PrimeLabel
  d : PrimeLabel
  deriving DecidableEq, BEq, Repr

def Order.labels (o : Order) := [o.a, o.b, o.c, o.d]

def Order.complete (o : Order) : Bool :=
  menu.all (fun p => o.labels.contains p)

private def allFourSlots : List Order :=
  menu.flatMap fun a => menu.flatMap fun b =>
    menu.flatMap fun c => menu.map fun d => ⟨a,b,c,d⟩

def orders : List Order := allFourSlots.filter Order.complete

private theorem in_menu (p : PrimeLabel) : p ∈ menu := by cases p <;> simp [menu]

private theorem in_allFourSlots (o : Order) : o ∈ allFourSlots := by
  rcases o with ⟨a,b,c,d⟩
  apply List.mem_flatMap.mpr
  exact ⟨a, in_menu a, List.mem_flatMap.mpr ⟨b, in_menu b,
    List.mem_flatMap.mpr ⟨c, in_menu c, List.mem_map.mpr ⟨d, in_menu d, rfl⟩⟩⟩⟩

theorem mem_orders_iff_complete (o : Order) : o ∈ orders ↔ o.complete = true := by
  simp [orders, in_allFourSlots]

set_option maxRecDepth 8192 in
theorem exactly_24_orders : orders.length = 24 ∧ orders.Nodup := by decide

private def survivorCheck (o : Order) : Bool :=
  (tickets .plus ++ tickets .minus).all fun n =>
    (n % prime o.a == 0) || (n % prime o.b == 0) || (n == prime o.c * prime o.d)

set_option maxRecDepth 8192 in
private theorem all_survivors : orders.all survivorCheck = true := by decide

/-- After two misses the only possible input is the product of the two
untested prime labels. -/
theorem only_untested_product (s : Source) (o : Order) (h : o.complete = true)
    (n : Nat) (hn : n ∈ tickets s) (ha : n % prime o.a ≠ 0) (hb : n % prime o.b ≠ 0) :
    n = prime o.c * prime o.d := by
  have h₁ := List.all_eq_true.mp all_survivors o ((mem_orders_iff_complete o).mpr h)
  have h₂ : n ∈ tickets .plus ++ tickets .minus := by
    cases s <;> simp [hn]
  have h₃ := List.all_eq_true.mp h₁ n h₂
  simpa [ha, hb] using h₃

/-- Charge one for the current probe; stop at the first divisor. -/
def probes (n : Nat) : List PrimeLabel → Nat
  | [] => 0
  | p :: rest => if n % prime p == 0 then 1 else 1 + probes n rest

def totalCost (s : Source) (o : Order) : Nat :=
  ((tickets s).map (fun n => probes n o.labels)).sum

def expectedCost (s : Source) (o : Order) : Rat :=
  rationalNat (totalCost s o) / rationalNat (tickets s).length

/-- The larger of the two source-specific expected costs. -/
def worstCost (o : Order) : Rat :=
  if expectedCost .plus o ≤ expectedCost .minus o then expectedCost .minus o else expectedCost .plus o

def threeSeven : Order := ⟨three,seven,five,eleven⟩
def threeEleven : Order := ⟨three,eleven,five,seven⟩
def increasing : Order := ⟨three,five,seven,eleven⟩

theorem example_costs :
    expectedCost .plus threeSeven = 7/4 ∧ expectedCost .minus threeSeven = 19/12 ∧
    expectedCost .plus threeEleven = 19/12 ∧ expectedCost .minus threeEleven = 7/4 ∧
    expectedCost .plus increasing = 5/3 ∧ expectedCost .minus increasing = 5/3 := by
  decide

private def costShape (o : Order) : Bool :=
  let a := totalCost .plus o
  let b := totalCost .minus o
  (a == 19 && b == 21) || (a == 20 && b == 20) || (a == 21 && b == 19)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem all_cost_shapes : orders.all costShape = true := by decide

theorem pair_of_costs (o : Order) (h : o.complete = true) :
    (totalCost .plus o = 19 ∧ totalCost .minus o = 21) ∨
    (totalCost .plus o = 20 ∧ totalCost .minus o = 20) ∨
    (totalCost .plus o = 21 ∧ totalCost .minus o = 19) := by
  have hc := List.all_eq_true.mp all_cost_shapes o ((mem_orders_iff_complete o).mpr h)
  simpa only [costShape, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] using hc

theorem every_order (o : Order) (h : o.complete = true) :
    19/12 ≤ expectedCost .plus o ∧ 19/12 ≤ expectedCost .minus o ∧
    (expectedCost .plus o + expectedCost .minus o) / 2 = 5/3 ∧
    5/3 ≤ worstCost o := by
  rcases pair_of_costs o h with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    simp only [worstCost, expectedCost, ha, hb] <;> decide

/-- Each source achieves its lower bound, using different orders. -/
theorem source_optimum (s : Source) :
    (∀ o : Order, o.complete = true → 19/12 ≤ expectedCost s o) ∧
    ∃ o : Order, o.complete = true ∧ expectedCost s o = 19/12 := by
  cases s with
  | plus =>
    exact ⟨fun o h => (every_order o h).1, threeEleven, by decide, example_costs.2.2.1⟩
  | minus =>
    exact ⟨fun o h => (every_order o h).2.1, threeSeven, by decide, example_costs.2.1⟩

/-- A single order attaining the worst-source lower bound identifies the
deterministic two-source minimax value. Its excess over 19/12 is 1/12. -/
theorem common_order_minimax :
    (∀ o : Order, o.complete = true →
      5/3 ≤ worstCost o) ∧
    (∃ o : Order, o.complete = true ∧
      worstCost o = 5/3) ∧
    (5/3 - 19/12 : Rat) = 1/12 := by
  exact ⟨fun o h => (every_order o h).2.2.2,
    ⟨increasing, by decide, by decide⟩, by decide⟩

/-- An arbitrary finite rational lottery on complete orders can be written
as a list with repetitions. Denominators below count equally likely tickets. -/
def lotteryTotal (s : Source) (strategies : List Order) : Nat :=
  (strategies.map (totalCost s)).sum

theorem lottery_pair_sum (strategies : List Order)
    (valid : ∀ o ∈ strategies, o.complete = true) :
    lotteryTotal .plus strategies + lotteryTotal .minus strategies = 40 * strategies.length := by
  induction strategies with
  | nil => rfl
  | cons o rest ih =>
    have ho := valid o (by simp)
    have hr := ih (fun x hx => valid x (by simp [hx]))
    have hpair : totalCost .plus o + totalCost .minus o = 40 := by
      rcases pair_of_costs o ho with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> omega
    simp only [lotteryTotal, List.map_cons, List.sum_cons, List.length_cons,
      Nat.mul_succ] at hr ⊢
    omega

/-- Since every order costs 40 probe-tickets across both twelve-ticket laws,
the worst law costs at least 20 per order-ticket, or 20/12 = 5/3 probes. -/
theorem randomized_lower_bound (strategies : List Order)
    (valid : ∀ o ∈ strategies, o.complete = true) :
    20 * strategies.length ≤
      max (lotteryTotal .plus strategies) (lotteryTotal .minus strategies) := by
  have h := lottery_pair_sum strategies valid
  omega

end Screening.FourPrimes
