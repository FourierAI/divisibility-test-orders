import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Std
import Std.Internal.Rat

/-! Standard-library proofs from Learning Divisibility Test Orders from the Largest Hits. Generated with tools/standalone.py. See PROOFS.md for coverage. -/

/- Source module: Screening.FourPrimes -/

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

/- Source module: Screening.LargestHits -/

namespace Screening.LargestHits

/-- Every probe rank differs from its index in natural order by at most `w`. -/
def Displacement (rank : Nat → Nat) (w : Nat) : Prop :=
  ∀ i, i ≤ rank i + w ∧ rank i ≤ i + w

/-- An earlier natural index can beat a later index only inside a `2w` window. -/
theorem beating_close {rank : Nat → Nat} {w i j : Nat}
    (band : Displacement rank w) (beats : rank j < rank i) : j ≤ i + 2 * w := by
  obtain ⟨_, iUpper⟩ := band i
  obtain ⟨jLower, _⟩ := band j
  omega

/-- The reversed-order rank gap is at most `2w`. -/
theorem beating_gap_le {rank : Nat → Nat} {w i j : Nat}
    (band : Displacement rank w) (indices : i ≤ j) : rank i ≤ rank j + 2 * w := by
  obtain ⟨_, iUpper⟩ := band i
  obtain ⟨jLower, _⟩ := band j
  omega

/-- Maximum probe rank among the supplied hits, with zero for an empty list. -/
def maxRank (rank : Nat → Nat) : List Nat → Nat
  | [] => 0
  | i :: rest => max (rank i) (maxRank rank rest)

private theorem rank_le_maxRank {rank : Nat → Nat} {i : Nat} {hits : List Nat}
    (member : i ∈ hits) : rank i ≤ maxRank rank hits := by
  induction hits with
  | nil => simp at member
  | cons j rest ih =>
    change rank i ≤ max (rank j) (maxRank rank rest)
    rw [List.mem_cons] at member
    rcases member with equal | inside
    · subst i
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih inside) (Nat.le_max_right _ _)

private theorem maxRank_le {rank : Nat → Nat} {hits : List Nat} {bound : Nat}
    (pointwise : ∀ i ∈ hits, rank i ≤ bound) : maxRank rank hits ≤ bound := by
  induction hits with
  | nil => simp [maxRank]
  | cons i rest ih =>
    change max (rank i) (maxRank rank rest) ≤ bound
    exact Nat.max_le.mpr
      ⟨pointwise i (by simp), ih (fun j member => pointwise j (by simp [member]))⟩

private theorem maxRank_attained (rank : Nat → Nat) {hits : List Nat}
    (nonempty : hits ≠ []) : ∃ i ∈ hits, maxRank rank hits = rank i := by
  induction hits with
  | nil => exact False.elim (nonempty rfl)
  | cons i rest ih =>
    by_cases restEmpty : rest = []
    · subst rest
      exact ⟨i, by simp, by simp [maxRank]⟩
    · by_cases larger : rank i ≤ maxRank rank rest
      · obtain ⟨j, inside, equal⟩ := ih restEmpty
        exact ⟨j, by simp [inside], by rw [maxRank, Nat.max_eq_right larger, equal]⟩
      · have larger' : maxRank rank rest ≤ rank i := by omega
        exact ⟨i, by simp, by rw [maxRank, Nat.max_eq_left larger']⟩

/-- Hits in descending natural order, with the greatest numerical index first. -/
def Descending (hits : List Nat) : Prop :=
  hits.Pairwise (fun i j => j ≤ i)

private theorem drop_le_take_succ {hits : List Nat} {ℓ x y : Nat}
    (sorted : Descending hits) (discarded : x ∈ hits.drop ℓ)
    (retainedOrNext : y ∈ hits.take (ℓ + 1)) : x ≤ y := by
  unfold Descending at sorted
  induction ℓ generalizing hits with
  | zero =>
    cases hits with
    | nil => simp at retainedOrNext
    | cons j rest =>
      have yHead : y = j := by simpa using retainedOrNext
      change x ∈ j :: rest at discarded
      rw [List.mem_cons] at discarded
      rcases discarded with xHead | xTail
      · omega
      · rw [yHead]
        exact (List.pairwise_cons.mp sorted).1 _ xTail
  | succ ℓ ih =>
    cases hits with
    | nil => simp at retainedOrNext
    | cons j rest =>
      change x ∈ rest.drop ℓ at discarded
      change y ∈ j :: rest.take (ℓ + 1) at retainedOrNext
      obtain ⟨headBound, tailSorted⟩ := List.pairwise_cons.mp sorted
      rw [List.mem_cons] at retainedOrNext
      rcases retainedOrNext with yHead | yTail
      · rw [yHead]
        exact headBound _ (List.mem_of_mem_drop discarded)
      · exact ih tailSorted discarded yTail

private theorem head_le_maxRank_take {rank : Nat → Nat} {ℓ j : Nat} {rest : List Nat}
    (positive : 0 < ℓ) : rank j ≤ maxRank rank ((j :: rest).take ℓ) := by
  apply rank_le_maxRank
  cases ℓ with
  | zero => omega
  | succ n => simp

/-- The full maximum rank is at most `2w` larger than the retained maximum. -/
theorem rank_replacement_bound {rank : Nat → Nat} {w j ℓ : Nat} {rest : List Nat}
    (band : Displacement rank w) (sorted : Descending (j :: rest)) (positive : 0 < ℓ) :
    maxRank rank ((j :: rest).take ℓ) ≤ maxRank rank (j :: rest) ∧
      maxRank rank (j :: rest) - maxRank rank ((j :: rest).take ℓ) ≤ 2 * w := by
  constructor
  · exact maxRank_le (fun i member => rank_le_maxRank (List.mem_of_mem_take member))
  · unfold Descending at sorted
    have headBound := (List.pairwise_cons.mp sorted).1
    have retained : rank j ≤ maxRank rank ((j :: rest).take ℓ) :=
      head_le_maxRank_take positive
    have full : maxRank rank (j :: rest) ≤ rank j + 2 * w := by
      apply maxRank_le
      intro i member
      apply beating_gap_le band
      rw [List.mem_cons] at member
      rcases member with equal | inside
      · omega
      · exact headBound _ inside
    omega

/-- A strict error forces a discarded maximizing hit and clusters the first
`ℓ + 1` numerical hits inside the `2w` window ending at the greatest hit. -/
theorem cluster_of_strict_error {rank : Nat → Nat} {w j ℓ : Nat} {rest : List Nat}
    (band : Displacement rank w) (sorted : Descending (j :: rest)) (positive : 0 < ℓ)
    (error : maxRank rank ((j :: rest).take ℓ) < maxRank rank (j :: rest)) :
    ∃ i ∈ (j :: rest).drop ℓ, maxRank rank (j :: rest) = rank i ∧
      ℓ + 1 ≤ (j :: rest).length ∧
      ∀ k ∈ (j :: rest).take (ℓ + 1), k ≤ j ∧ j ≤ k + 2 * w := by
  obtain ⟨i, inside, equal⟩ := maxRank_attained rank (hits := j :: rest) (by simp)
  have retained : rank j ≤ maxRank rank ((j :: rest).take ℓ) :=
    head_le_maxRank_take positive
  have discarded : i ∈ (j :: rest).drop ℓ := by
    have membership : i ∈ (j :: rest).take ℓ ++ (j :: rest).drop ℓ := by
      rwa [List.take_append_drop]
    rw [List.mem_append] at membership
    rcases membership with kept | discarded
    · have bound : rank i ≤ maxRank rank ((j :: rest).take ℓ) := rank_le_maxRank kept
      omega
    · exact discarded
  have discardNonempty : (j :: rest).drop ℓ ≠ [] := by
    intro empty
    simp [empty] at discarded
  have discardLength : 0 < ((j :: rest).drop ℓ).length :=
    List.length_pos_iff.mpr discardNonempty
  rw [List.length_drop] at discardLength
  have enough : ℓ + 1 ≤ (j :: rest).length := by omega
  have atMostHead : ∀ k ∈ j :: rest, k ≤ j := by
    intro k member
    rw [List.mem_cons] at member
    rcases member with equal | inside
    · omega
    · exact (List.pairwise_cons.mp sorted).1 _ inside
  have close : j ≤ i + 2 * w := beating_close band (by omega)
  refine ⟨i, discarded, equal, enough, ?_⟩
  intro k member
  have ik : i ≤ k := drop_le_take_succ sorted discarded member
  exact ⟨atMostHead k (List.mem_of_mem_take member), by omega⟩

/-- The free record is the hit count and the first `ℓ` descending numerical hits. -/
def record (ℓ : Nat) (hits : List Nat) : Nat × List Nat :=
  (hits.length, hits.take ℓ)

/-- Retaining the greatest numerical hits gives a rank surrogate. -/
def proxyRank (rank : Nat → Nat) (ℓ : Nat) (hits : List Nat) : Nat :=
  maxRank rank (hits.take ℓ)

/-- Hit lists with the same recorded count and top tuple have the same surrogate. -/
theorem proxy_factors_of_record_eq {rank : Nat → Nat} {ℓ : Nat} {xs ys : List Nat}
    (sameRecord : record ℓ xs = record ℓ ys) : proxyRank rank ℓ xs = proxyRank rank ℓ ys :=
  congrArg (fun entry : Nat × List Nat => maxRank rank entry.2) sameRecord

/-- An empirical surrogate sum can be computed from the recorded tuples. -/
theorem empirical_proxy_sum (rank : Nat → Nat) (ℓ : Nat) (samples : List (List Nat)) :
    (samples.map (proxyRank rank ℓ)).sum =
      ((samples.map (record ℓ)).map (fun entry => maxRank rank entry.2)).sum := by
  rw [List.map_map]
  rfl

/-- Selection by the number of hits and summation of the proxy also factor
through the free records. -/
theorem empirical_proxy_sum_at_count (rank : Nat → Nat) (ℓ h : Nat)
    (samples : List (List Nat)) :
    ((samples.filter (fun hits => hits.length == h)).map (proxyRank rank ℓ)).sum =
      (((samples.map (record ℓ)).filter (fun entry => entry.1 == h)).map
        (fun entry => maxRank rank entry.2)).sum := by
  induction samples with
  | nil => rfl
  | cons hits samples ih =>
    simp only [record, proxyRank] at ih
    cases count : (hits.length == h) <;> simp [record, proxyRank, count, ih]

private theorem sum_of_perm {xs ys : List Nat} (same : xs.Perm ys) : xs.sum = ys.sum := by
  induction same with
  | nil => rfl
  | cons head _ ih => simp [ih]
  | swap i j tail => simp [Nat.add_left_comm]
  | trans _ _ first second => exact first.trans second

/-- The histogram of records suffices for the count-stratified proxy sum,
so the sample order can be discarded. -/
theorem empirical_proxy_sum_of_record_perm (rank : Nat → Nat) (ℓ h : Nat)
    {xs ys : List (List Nat)} (sameRecords : (xs.map (record ℓ)).Perm (ys.map (record ℓ))) :
    ((xs.filter (fun hits => hits.length == h)).map (proxyRank rank ℓ)).sum =
      ((ys.filter (fun hits => hits.length == h)).map (proxyRank rank ℓ)).sum := by
  rw [empirical_proxy_sum_at_count, empirical_proxy_sum_at_count]
  exact sum_of_perm ((List.Perm.filter (fun entry => entry.1 == h) sameRecords).map
    (fun entry => maxRank rank entry.2))

/-- The top `ℓ + 1` numerical hits lie in the window of width `2w` at the head. -/
def nearCluster (w ℓ : Nat) : List Nat → Bool
  | [] => false
  | j :: rest =>
    decide (ℓ + 1 ≤ (j :: rest).length) &&
      ((j :: rest).take (ℓ + 1)).all (fun i => decide (i ≤ j ∧ j ≤ i + 2 * w))

private theorem natAbs_sub_nat_le {a b w : Nat}
    (upper : a ≤ b + w) (lower : b ≤ a + w) :
    ((a : Int) - (b : Int)).natAbs ≤ w := by
  by_cases order : b ≤ a
  · rw [← Int.ofNat_sub order, Int.natAbs_ofNat]
    omega
  · have order' : a ≤ b := by omega
    rw [← Int.natAbs_neg, Int.neg_sub, ← Int.ofNat_sub order', Int.natAbs_ofNat]
    omega

/-- Centering a maximum rank at increasing order gives a difference of modulus at most `w`. -/
theorem centered_rank_bound {rank : Nat → Nat} {w : Nat}
    (band : Displacement rank w) (hits : List Nat) :
    ((maxRank rank hits : Int) - (maxRank id hits : Int)).natAbs ≤ w := by
  apply natAbs_sub_nat_le
  · apply maxRank_le
    intro i member
    have natural : i ≤ maxRank id hits := rank_le_maxRank (rank := id) member
    obtain ⟨_, upper⟩ := band i
    omega
  · apply maxRank_le
    intro i member
    have ranked := rank_le_maxRank (rank := rank) member
    obtain ⟨lower, _⟩ := band i
    change i ≤ maxRank rank hits + w
    omega

/-- A row outside the near-cluster event contributes exactly zero rank error. -/
theorem rank_error_le_nearCluster {rank : Nat → Nat} {w ℓ : Nat} {hits : List Nat}
    (band : Displacement rank w) (sorted : Descending hits) (positive : 0 < ℓ) :
    ((maxRank rank hits : Int) - (proxyRank rank ℓ hits : Int)).natAbs ≤
      if nearCluster w ℓ hits then 2 * w else 0 := by
  cases hits with
  | nil => simp [nearCluster, maxRank, proxyRank]
  | cons j rest =>
    obtain ⟨mono, gap⟩ := rank_replacement_bound band sorted positive
    unfold proxyRank
    rw [← Int.ofNat_sub mono, Int.natAbs_ofNat]
    cases near : nearCluster w ℓ (j :: rest) with
    | true => simpa only [near, Bool.true_eq, if_true] using gap
    | false =>
      by_cases equal : maxRank rank ((j :: rest).take ℓ) = maxRank rank (j :: rest)
      · simp [equal]
      · have strict : maxRank rank ((j :: rest).take ℓ) < maxRank rank (j :: rest) := by omega
        obtain ⟨_, _, _, enough, nearby⟩ := cluster_of_strict_error band sorted positive strict
        have allNear : nearCluster w ℓ (j :: rest) = true := by
          unfold nearCluster
          exact Bool.and_eq_true_iff.mpr
            ⟨decide_eq_true enough, List.all_eq_true.mpr (fun i member =>
                decide_eq_true (nearby i member))⟩
        simp [allNear] at near

/-- A containment moment with scaled integer weight, including its inclusion–exclusion sign. -/
structure MomentRow where
  hits : List Nat
  weight : Int

private theorem natAbs_sum_sub_le {α : Type} (rows : List α) (f g : α → Int) (bound : α → Nat)
    (pointwise : ∀ row ∈ rows, (f row - g row).natAbs ≤ bound row) :
    ((rows.map f).sum - (rows.map g).sum).natAbs ≤ (rows.map bound).sum := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    simp only [List.map_cons, List.sum_cons]
    have tail := ih (fun x inside => pointwise x (List.mem_cons_of_mem _ inside))
    have head := pointwise row (List.mem_cons_self ..)
    have split : f row + (rows.map f).sum - (g row + (rows.map g).sum) =
        (f row - g row) + ((rows.map f).sum - (rows.map g).sum) := by omega
    rw [split]
    exact Nat.le_trans (Int.natAbs_add_le ..) (Nat.add_le_add head tail)

private theorem sum_indicator {α : Type} (rows : List α) (test : α → Bool) (value : Nat) :
    (rows.map (fun row => if test row then value else 0)).sum = value * rows.countP test := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    cases mark : test row <;> simp [mark, ih, Nat.mul_succ, Nat.add_comm]

private theorem sum_zero_map {α : Type} (rows : List α) :
    (rows.map (fun _ => (0 : Int))).sum = 0 := by
  induction rows <;> simp_all

/-- Keep a centered weighted contribution from a containment moment. -/
def weightedCentered (rankOf : List Nat → Nat) (row : MomentRow) : Int :=
  row.weight * ((rankOf row.hits : Int) - (maxRank id row.hits : Int))

/-- The centered surrogate feature determined by one count-and-top-hits record. -/
def recordedFeature (rank : Nat → Nat) (entry : Nat × List Nat) : Int :=
  (maxRank rank entry.2 : Int) - (maxRank id entry.2 : Int)

private theorem natural_proxy_exact {ℓ : Nat} {hits : List Nat}
    (positive : 0 < ℓ) (sorted : Descending hits) :
    maxRank id (hits.take ℓ) = maxRank id hits := by
  cases hits with
  | nil => simp
  | cons j rest =>
    have band : Displacement id 0 := by simp [Displacement]
    obtain ⟨mono, gap⟩ := rank_replacement_bound band sorted positive
    omega

/-- A weighted centered proxy uses only the row's weight and its free record. -/
theorem weightedCentered_proxy_factors (rank : Nat → Nat) (ℓ : Nat) (row : MomentRow)
    (positive : 0 < ℓ) (sorted : Descending row.hits) :
    weightedCentered (proxyRank rank ℓ) row =
      row.weight * recordedFeature rank (record ℓ row.hits) := by
  unfold weightedCentered proxyRank recordedFeature record
  rw [natural_proxy_exact positive sorted]

/-- Each record group contributes its total signed moment weight times a known feature. -/
theorem weighted_proxy_for_record_group (rank : Nat → Nat) (ℓ : Nat)
    (entry : Nat × List Nat) (rows : List MomentRow) (positive : 0 < ℓ)
    (sorted : ∀ row ∈ rows, Descending row.hits)
    (sameRecord : ∀ row ∈ rows, record ℓ row.hits = entry) :
    (rows.map (weightedCentered (proxyRank rank ℓ))).sum =
      (rows.map MomentRow.weight).sum * recordedFeature rank entry := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have member : row ∈ row :: rows := List.mem_cons_self ..
    have head := weightedCentered_proxy_factors rank ℓ row positive (sorted row member)
    rw [sameRecord row member] at head
    have tail := ih (fun x inside => sorted x (List.mem_cons_of_mem _ inside))
      (fun x inside => sameRecord x (List.mem_cons_of_mem _ inside))
    simp only [List.map_cons, List.sum_cons, head, tail, Int.add_mul]

/-- The reference cost plus the true high- and low-degree moment deviations. -/
def trueScore (reference : (Nat → Nat) → Int) (top low : List MomentRow)
    (rank : Nat → Nat) : Int :=
  reference rank + (top.map (weightedCentered (maxRank rank))).sum +
    (low.map (weightedCentered (maxRank rank))).sum

/-- Keep the reference cost and replace top-degree rank maxima by their recorded proxies. -/
def surrogateScore (reference : (Nat → Nat) → Int) (ℓ : Nat) (top : List MomentRow)
    (rank : Nat → Nat) : Int :=
  reference rank + (top.map (weightedCentered (proxyRank rank ℓ))).sum

/-- Uniform deterministic error from high-degree rank replacement and low-degree rounding. -/
def surrogateErrorBound (w ℓ topBound lowBound : Nat) (top low : List MomentRow) : Nat :=
  (2 * w * topBound) * top.countP (fun row => nearCluster w ℓ row.hits) +
    (w * lowBound) * low.length

/-- The finite, signed-weight surrogate objective has a two-term uniform error bound.
The same statement applies to finitely many rational moments after a common scaling. -/
theorem surrogate_error_le {reference : (Nat → Nat) → Int} {rank : Nat → Nat}
    {w ℓ topBound lowBound : Nat} {top low : List MomentRow}
    (band : Displacement rank w) (positive : 0 < ℓ)
    (topSorted : ∀ row ∈ top, Descending row.hits)
    (topWeights : ∀ row ∈ top, row.weight.natAbs ≤ topBound)
    (lowWeights : ∀ row ∈ low, row.weight.natAbs ≤ lowBound) :
    (trueScore reference top low rank - surrogateScore reference ℓ top rank).natAbs ≤
      surrogateErrorBound w ℓ topBound lowBound top low := by
  have high := natAbs_sum_sub_le top (weightedCentered (maxRank rank))
    (weightedCentered (proxyRank rank ℓ))
    (fun row => if nearCluster w ℓ row.hits then 2 * w * topBound else 0) ?_
  · rw [sum_indicator] at high
    have lower := natAbs_sum_sub_le low (weightedCentered (maxRank rank)) (fun _ => 0)
      (fun row => if (fun _ : MomentRow => true) row then w * lowBound else 0) ?_
    · rw [sum_indicator] at lower
      simp [sum_zero_map] at lower
      unfold trueScore surrogateScore surrogateErrorBound
      have split : reference rank + (top.map (weightedCentered (maxRank rank))).sum +
          (low.map (weightedCentered (maxRank rank))).sum -
          (reference rank + (top.map (weightedCentered (proxyRank rank ℓ))).sum) =
          ((top.map (weightedCentered (maxRank rank))).sum -
            (top.map (weightedCentered (proxyRank rank ℓ))).sum) +
          (low.map (weightedCentered (maxRank rank))).sum := by omega
      rw [split]
      exact Nat.le_trans (Int.natAbs_add_le ..) (Nat.add_le_add high lower)
    · intro row member
      simp only [weightedCentered, Int.sub_zero, Bool.true_eq, if_true, Int.natAbs_mul]
      rw [Nat.mul_comm w lowBound]
      exact Nat.mul_le_mul (lowWeights row member) (centered_rank_bound band row.hits)
  · intro row member
    unfold weightedCentered
    rw [← Int.mul_sub]
    have cancel : ((maxRank rank row.hits : Int) - (maxRank id row.hits : Int)) -
          ((proxyRank rank ℓ row.hits : Int) - (maxRank id row.hits : Int)) =
        (maxRank rank row.hits : Int) - (proxyRank rank ℓ row.hits : Int) := by omega
    rw [cancel, Int.natAbs_mul]
    have gap := rank_error_le_nearCluster band (topSorted row member) positive
    have product := Nat.mul_le_mul (topWeights row member) gap
    cases near : nearCluster w ℓ row.hits <;> simpa [near, Nat.mul_comm] using product

private theorem sub_le_cast_of_natAbs_le {a b : Int} {bound : Nat}
    (error : (a - b).natAbs ≤ bound) : a - b ≤ (bound : Int) :=
  Int.le_trans Int.le_natAbs (Int.ofNat_le.mpr error)

private theorem rev_sub_le_cast_of_natAbs_le {a b : Int} {bound : Nat}
    (error : (a - b).natAbs ≤ bound) : b - a ≤ (bound : Int) := by
  have negative := Int.le_natAbs (a := -(a - b))
  rw [Int.natAbs_neg] at negative
  have upper := Int.le_trans negative (Int.ofNat_le.mpr error)
  omega

/-- A comparison within the stated additive slack on the surrogate carries
over to the true objective with twice the uniform error. -/
theorem surrogate_comparison_regret {reference : (Nat → Nat) → Int} {chosen oracle : Nat → Nat}
    {w ℓ topBound lowBound slack : Nat} {top low : List MomentRow}
    (chosenBand : Displacement chosen w) (oracleBand : Displacement oracle w)
    (positive : 0 < ℓ)
    (topSorted : ∀ row ∈ top, Descending row.hits)
    (topWeights : ∀ row ∈ top, row.weight.natAbs ≤ topBound)
    (lowWeights : ∀ row ∈ low, row.weight.natAbs ≤ lowBound)
    (comparison : surrogateScore reference ℓ top chosen ≤
      surrogateScore reference ℓ top oracle + (slack : Int)) :
    trueScore reference top low chosen - trueScore reference top low oracle ≤
      (2 * surrogateErrorBound w ℓ topBound lowBound top low + slack : Nat) := by
  have chosenError := surrogate_error_le (reference := reference)
    chosenBand positive topSorted topWeights lowWeights
  have oracleError := surrogate_error_le (reference := reference)
    oracleBand positive topSorted topWeights lowWeights
  have chosenUpper := sub_le_cast_of_natAbs_le chosenError
  have oracleUpper := rev_sub_le_cast_of_natAbs_le oracleError
  omega

/-- A population surrogate minimizer has true cost at most twice the uniform
surrogate error above a banded oracle. -/
theorem surrogate_minimizer_regret {reference : (Nat → Nat) → Int} {chosen oracle : Nat → Nat}
    {w ℓ topBound lowBound : Nat} {top low : List MomentRow}
    (chosenBand : Displacement chosen w) (oracleBand : Displacement oracle w)
    (positive : 0 < ℓ)
    (topSorted : ∀ row ∈ top, Descending row.hits)
    (topWeights : ∀ row ∈ top, row.weight.natAbs ≤ topBound)
    (lowWeights : ∀ row ∈ low, row.weight.natAbs ≤ lowBound)
    (beatsOracle : surrogateScore reference ℓ top chosen ≤ surrogateScore reference ℓ top oracle) :
    trueScore reference top low chosen - trueScore reference top low oracle ≤
      (2 * surrogateErrorBound w ℓ topBound lowBound top low : Nat) := by
  simpa using surrogate_comparison_regret (slack := 0)
    chosenBand oracleBand positive topSorted topWeights lowWeights (by simpa using beatsOracle)

/-- An empirical surrogate comparison adds twice the estimation error and its
additive optimization slack to the deterministic regret bound. -/
theorem empirical_surrogate_regret {reference empirical : (Nat → Nat) → Int}
    {chosen oracle : Nat → Nat} {w ℓ topBound lowBound estimate slack : Nat}
    {top low : List MomentRow}
    (chosenBand : Displacement chosen w) (oracleBand : Displacement oracle w)
    (positive : 0 < ℓ)
    (topSorted : ∀ row ∈ top, Descending row.hits)
    (topWeights : ∀ row ∈ top, row.weight.natAbs ≤ topBound)
    (lowWeights : ∀ row ∈ low, row.weight.natAbs ≤ lowBound)
    (estimateChosen : (empirical chosen - surrogateScore reference ℓ top chosen).natAbs ≤ estimate)
    (estimateOracle : (empirical oracle - surrogateScore reference ℓ top oracle).natAbs ≤ estimate)
    (comparison : empirical chosen ≤ empirical oracle + (slack : Int)) :
    trueScore reference top low chosen - trueScore reference top low oracle ≤
      (2 * surrogateErrorBound w ℓ topBound lowBound top low + (2 * estimate + slack) : Nat) := by
  apply surrogate_comparison_regret chosenBand oracleBand positive topSorted topWeights lowWeights
  have chosenUpper := rev_sub_le_cast_of_natAbs_le estimateChosen
  have oracleUpper := sub_le_cast_of_natAbs_le estimateOracle
  omega

end Screening.LargestHits

/- Source module: Screening.Indistinguishability -/

/-!
Finite observation and decision arguments for the largest-hits lower bound.
Hit sets are represented by lists in decreasing numerical order. Integer
atom weights permit signed changes and rational laws after common scaling.
The last theorem treats arbitrary random tapes and probability scalars, so
the decision lower bound does not require rational output probabilities.
-/

namespace Screening.Indistinguishability

/-- Cardinality and the first `ell` members of a descending hit list. -/
def largestRecord (ell : Nat) (hits : List α) : Nat × List α :=
  (hits.length, hits.take ell)

private theorem take_prefix (shown rest : List α) :
    (shown ++ rest).take shown.length = shown := by
  induction shown with
  | nil => rfl
  | cons x xs ih => simp [List.take, ih]

/-- An unreported group member may vary without changing either recorded field. -/
theorem hidden_tag_same_record (shown rest : List α) (pos neg : α) :
    largestRecord shown.length (shown ++ pos :: rest) =
      largestRecord shown.length (shown ++ neg :: rest) := by
  simp [largestRecord, take_prefix]

/-- The two ways a balanced group appears in the exact-cell expansion.
If the group is absent both signs affect the same cell. If all groups
are present, a hidden tag follows the `ell` retained tags. -/
inductive PairedCell (α : Type) (ell : Nat) where
  | absent (cell : List α)
  | hidden (shown rest : List α) (pos neg : α) (length_eq : shown.length = ell)

def PairedCell.cells : PairedCell α ell → List α × List α
  | .absent cell => (cell, cell)
  | .hidden shown rest pos neg _ => (shown ++ pos :: rest, shown ++ neg :: rest)

theorem PairedCell.same_record (p : PairedCell α ell) :
    largestRecord ell p.cells.1 = largestRecord ell p.cells.2 := by
  cases p with
  | absent => rfl
  | hidden shown rest pos neg length_eq =>
    subst ell
    exact hidden_tag_same_record shown rest pos neg

/-- Signed multilinear coefficient of the group labels, before multiplication
by the common cube amplitude and the exact-cell expansion sign. -/
def signProduct : List Bool → Int
  | [] => 1
  | b :: rest => (if b then 1 else -1) * signProduct rest

theorem opposite_parity_coefficients (before after : List Bool) :
    signProduct (before ++ true :: after) = -signProduct (before ++ false :: after) := by
  induction before with
  | nil => simp [signProduct]
  | cons b bs ih =>
    cases b <;> simp [signProduct, ih]

/-- Push a signed atomic measure through a record map, allowing repeated atoms. -/
def observedMass [DecidableEq R] (record : X → R) (o : R) :
    List (X × Int) → Int
  | [] => 0
  | (x, w) :: rest => (if record x = o then w else 0) + observedMass record o rest

/-- Add the two opposite contributions before the remainder of the expansion. -/
def perturb (sgn : Int) (pairs : List (PairedCell α ell × Int))
    (base : List (List α × Int)) : List (List α × Int) :=
  match pairs with
  | [] => base
  | (p, d) :: rest =>
    (p.cells.1, sgn * d) :: (p.cells.2, -(sgn * d)) :: perturb sgn rest base

theorem balanced_pushforward [DecidableEq α] (sgn : Int)
    (pairs : List (PairedCell α ell × Int)) (base : List (List α × Int))
    (o : Nat × List α) :
    observedMass (largestRecord ell) o (perturb sgn pairs base) =
      observedMass (largestRecord ell) o base := by
  induction pairs with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨p, d⟩ := head
    simp only [perturb, observedMass, p.same_record, ih]
    by_cases hh : largestRecord ell p.cells.2 = o <;> simp [hh] <;> omega

/-- One orbit of the tag flip in a signed cube expansion. The `context`
contains the common amplitude, the exact-cell sign, and any multiplicity. -/
structure CubeFiber (α : Type) (ell : Nat) where
  cell : PairedCell α ell
  beforeTags : List Bool
  afterTags : List Bool
  context : Int

def cubeAtoms (sgn : Int) (fibers : List (CubeFiber α ell))
    (base : List (List α × Int)) : List (List α × Int) :=
  match fibers with
  | [] => base
  | f :: rest =>
    (f.cell.cells.1, sgn * (f.context * signProduct (f.beforeTags ++ true :: f.afterTags))) ::
    (f.cell.cells.2, sgn * (f.context * signProduct (f.beforeTags ++ false :: f.afterTags))) ::
    cubeAtoms sgn rest base

theorem cube_pushforward [DecidableEq α] (sgn : Int)
    (fibers : List (CubeFiber α ell)) (base : List (List α × Int)) (o : Nat × List α) :
    observedMass (largestRecord ell) o (cubeAtoms sgn fibers base) =
      observedMass (largestRecord ell) o base := by
  induction fibers with
  | nil => rfl
  | cons f rest ih =>
    have h := opposite_parity_coefficients f.beforeTags f.afterTags
    simp only [cubeAtoms, observedMass, f.cell.same_record, ih, h, Int.mul_neg]
    by_cases hv : largestRecord ell f.cell.cells.2 = o <;> simp [hv] <;> omega

theorem opposite_sources_same_record [DecidableEq α]
    (pairs : List (PairedCell α ell × Int)) (base : List (List α × Int)) :
    (fun o => observedMass (largestRecord ell) o (perturb 1 pairs base)) =
      (fun o => observedMass (largestRecord ell) o (perturb (-1) pairs base)) := by
  funext o
  rw [balanced_pushforward, balanced_pushforward]

/-- Even an oracle learner supplied with the entire compressed population
histogram and an arbitrary random tape has identical coupled output. -/
theorem same_oracle_output [DecidableEq α] (fibers : List (CubeFiber α ell))
    (base : List (List α × Int)) (learner : ((Nat × List α) → Int) → Ω → A) :
    learner (fun o => observedMass (largestRecord ell) o (cubeAtoms 1 fibers base)) =
      learner (fun o => observedMass (largestRecord ell) o (cubeAtoms (-1) fibers base)) := by
  apply congrArg learner
  funext o
  rw [cube_pushforward, cube_pushforward]

/-- Product mass of an iid finite compressed history. Scaling every record
mass by a common denominator merely scales a length-n history by its n-th power. -/
def historyMass (mass : R → Int) : List R → Int
  | [] => 1
  | r :: rs => mass r * historyMass mass rs

/-- Integrating the same randomized rule over all histories. The list may
also be restricted to any chosen subset of the histories. -/
def outputMass (histories : List (List R)) (mass : R → Int)
    (kernel : List R → A → Int) (a : A) : Int :=
  (histories.map (fun rs => historyMass mass rs * kernel rs a)).sum

theorem same_randomized_output (histories : List (List R)) (mass₁ mass₂ : R → Int)
    (equal_records : ∀ r, mass₁ r = mass₂ r) (kernel : List R → A → Int) (a : A) :
    outputMass histories mass₁ kernel a = outputMass histories mass₂ kernel a := by
  rw [show mass₁ = mass₂ from funext equal_records]

/-- Constant-sum order costs and two opposite favorable plans imply
a pointwise separation. All costs and the gain may be rational after scaling. -/
theorem opposite_regrets (cp cm op om baseline gain : Int)
    (common : 2 * baseline ≤ cp + cm)
    (plus_opt : op ≤ baseline - gain) (minus_opt : om ≤ baseline - gain) :
    2 * gain ≤ (cp - op) + (cm - om) := by omega

def weightMass (weights : List (A × Nat)) : Nat :=
  (weights.map Prod.snd).sum

def badMass (regret : A → Int) (gain : Int) : List (A × Nat) → Nat
  | [] => 0
  | (a, w) :: rest => (if gain ≤ regret a then w else 0) + badMass regret gain rest

/-- The unnormalized integral on a finite weighted output space. -/
def weightedCost (cost : A → Int) : List (A × Nat) → Int
  | [] => 0
  | (a, w) :: rest => (w : Int) * cost a + weightedCost cost rest

theorem integrated_gap (weights : List (A × Nat)) (plus minus : A → Int)
    (gain : Int) (gap : ∀ a, 2 * gain ≤ plus a + minus a) :
    (weightMass weights : Int) * (2 * gain) ≤
      weightedCost plus weights + weightedCost minus weights := by
  induction weights with
  | nil => simp [weightMass, weightedCost]
  | cons aw rest ih =>
    obtain ⟨a, w⟩ := aw
    have localGap := Int.mul_le_mul_of_nonneg_left (gap a) (Int.ofNat_zero_le w)
    rw [Int.mul_add] at localGap
    change ((w + weightMass rest : Nat) : Int) * (2 * gain) ≤
      ((w : Int) * plus a + weightedCost plus rest) +
      ((w : Int) * minus a + weightedCost minus rest)
    rw [Int.natCast_add, Int.add_mul]
    omega

theorem one_law_expectation (weights : List (A × Nat)) (plus minus : A → Int)
    (gain : Int) (gap : ∀ a, 2 * gain ≤ plus a + minus a) :
    (weightMass weights : Int) * gain ≤ weightedCost plus weights ∨
    (weightMass weights : Int) * gain ≤ weightedCost minus weights := by
  have sep := integrated_gap weights plus minus gain gap
  rw [Int.mul_left_comm] at sep
  omega

/-- Pointwise separation makes the two bad events cover every atom of
the common randomized output law. -/
theorem bad_masses_cover (weights : List (A × Nat)) (plus minus : A → Int)
    (gain : Int) (gap : ∀ a, 2 * gain ≤ plus a + minus a) :
    weightMass weights ≤ badMass plus gain weights + badMass minus gain weights := by
  induction weights with
  | nil => simp [weightMass, badMass]
  | cons aw rest ih =>
    obtain ⟨a, w⟩ := aw
    have point := gap a
    change w + weightMass rest ≤
      ((if gain ≤ plus a then w else 0) + badMass plus gain rest) +
      ((if gain ≤ minus a then w else 0) + badMass minus gain rest)
    by_cases hp : gain ≤ plus a <;> by_cases hm : gain ≤ minus a <;>
      simp only [hp, hm, if_true, if_false] <;> omega

/-- A single source has probability at least one half of incurring
regret at least `gain`, for every finite rational output distribution. -/
theorem one_law_half (weights : List (A × Nat)) (plus minus : A → Int)
    (gain : Int) (gap : ∀ a, 2 * gain ≤ plus a + minus a) :
    weightMass weights ≤ 2 * badMass plus gain weights ∨
      weightMass weights ≤ 2 * badMass minus gain weights := by
  have h := bad_masses_cover weights plus minus gain gap
  omega

/-- End-to-end finite two-source result. The rule sees the actual population
histogram for the source in question. The two returned weight lists need
not be assumed equal: their equality follows from the signed cube expansion.
Weights need only have positive total when converting the displayed bounds
to normalized probabilities and expectations. -/
theorem paired_laws_lower [DecidableEq α]
    (fibers : List (CubeFiber α ell)) (base : List (List α × Int))
    (learner : ((Nat × List α) → Int) → List (A × Nat))
    (plus minus : A → Int) (gain : Int) (gap : ∀ a, 2 * gain ≤ plus a + minus a) :
    let output := fun sgn => learner (fun o =>
      observedMass (largestRecord ell) o (cubeAtoms sgn fibers base))
    ((weightMass (output 1) : Int) * gain ≤ weightedCost plus (output 1) ∨
     (weightMass (output (-1)) : Int) * gain ≤ weightedCost minus (output (-1))) ∧
    (weightMass (output 1) ≤ 2 * badMass plus gain (output 1) ∨
     weightMass (output (-1)) ≤ 2 * badMass minus gain (output (-1))) := by
  dsimp only
  simp only [cube_pushforward]
  exact ⟨one_law_expectation _ plus minus gain gap, one_law_half _ plus minus gain gap⟩

/-- The same conclusion for an arbitrary common random tape, using only
monotonicity and the complement identity on the two measurable events.
The scalar hypotheses are elementary laws of a linearly ordered additive
group, supplied explicitly to avoid importing a measure or real-number library. -/
theorem arbitrary_random_tape_half {Ω A M : Type} [LE M] [Add M]
    (P : (Ω → Prop) → M) (half : M) (result : Ω → A)
    (plus minus : A → Int) (gain : Int)
    (gap : ∀ a, 2 * gain ≤ plus a + minus a)
    (reflLE : ∀ x : M, x ≤ x)
    (transLE : ∀ {x y z : M}, x ≤ y → y ≤ z → x ≤ z)
    (totalLE : ∀ x y : M, x ≤ y ∨ y ≤ x)
    (addMono : ∀ {a b c d : M}, a ≤ b → c ≤ d → a + c ≤ b + d)
    (cancelDouble : ∀ {x y : M}, x + x ≤ y + y → x ≤ y)
    (meas : (Ω → Prop) → Prop)
    (measPlus : meas (fun ω => gain ≤ plus (result ω)))
    (measMinus : meas (fun ω => gain ≤ minus (result ω)))
    (measCompl : ∀ e, meas e → meas (fun ω => ¬ e ω))
    (monoP : ∀ e f : Ω → Prop, meas e → meas f → (∀ ω, e ω → f ω) → P e ≤ P f)
    (complement : ∀ e : Ω → Prop, meas e → P e + P (fun ω => ¬ e ω) = half + half) :
    half ≤ P (fun ω => gain ≤ plus (result ω)) ∨
      half ≤ P (fun ω => gain ≤ minus (result ω)) := by
  let e := fun ω => gain ≤ plus (result ω)
  let f := fun ω => gain ≤ minus (result ω)
  change half ≤ P e ∨ half ≤ P f
  have included : ∀ ω, ¬ e ω → f ω := by
    intro ω h
    have hgap := gap (result ω)
    change ¬ gain ≤ plus (result ω) at h
    change gain ≤ minus (result ω)
    omega
  rcases totalLE (P e) (P (fun ω => ¬ e ω)) with h | h
  · right
    refine transLE ?_ (monoP _ _ (measCompl e measPlus) measMinus included)
    apply cancelDouble
    rw [← complement e measPlus]
    exact addMono h (reflLE _)
  · left
    apply cancelDouble
    rw [← complement e measPlus]
    exact addMono (reflLE _) h

end Screening.Indistinguishability

/- Source module: Screening.StoppedTrace -/

/-! Population identities used in the proof of the stopped-trace theorem.
The valuation can take values in any type admitting the indicated difference
on nested events. No assumption on independence of the hit indicators is used. -/

namespace Screening.StoppedTrace

universe u v w

def observes (hit : ι → Ω → Bool) (yes no : List ι) (word : Ω) : Prop :=
  (∀ i ∈ yes, hit i word = true) ∧ (∀ i ∈ no, hit i word = false)

def exclusion (minus : V → V → V) (moments : List ι → V)
    (yes : List ι) : List ι → V
  | [] => moments yes
  | i :: rest => minus (exclusion minus moments yes rest)
      (exclusion minus moments (i :: yes) rest)

/-- Inclusion-exclusion with arbitrary required and excluded hits. The only
law on the valuation is finite additivity for a single binary split. -/
theorem exclusion_eq (hit : ι → Ω → Bool) (mass : (Ω → Prop) → V)
    (minus : V → V → V)
    (split : ∀ (A : Ω → Prop) i,
      mass (fun x => A x ∧ hit i x = false) =
        minus (mass A) (mass (fun x => A x ∧ hit i x = true)))
    (yes no : List ι) :
    mass (observes hit yes no) =
      exclusion minus (fun s => mass (observes hit s [])) yes no := by
  induction no generalizing yes with
  | nil => rfl
  | cons i rest ih =>
    have off : observes hit yes (i :: rest) =
        (fun x => observes hit yes rest x ∧ hit i x = false) := by
      funext x
      simp only [observes, List.forall_mem_cons]
      apply propext
      exact ⟨fun ⟨p, n, r⟩ => ⟨⟨p, r⟩, n⟩,
        fun ⟨⟨p, r⟩, n⟩ => ⟨p, n, r⟩⟩
    have on : (fun x => observes hit yes rest x ∧ hit i x = true) =
        observes hit (i :: yes) rest := by
      funext x
      simp only [observes, List.forall_mem_cons]
      apply propext
      exact ⟨fun ⟨⟨p, r⟩, n⟩ => ⟨⟨n, p⟩, r⟩,
        fun ⟨⟨n, p⟩, r⟩ => ⟨⟨p, r⟩, n⟩⟩
    rw [off, split, on, ih, ih]
    rfl

def massOf {Ω : Type u} (sample : List Ω) (weight : Ω → Int) (A : Ω → Prop)
    [DecidablePred A] : Int :=
  (sample.map fun x => if A x then weight x else 0).sum

/-- Concrete witness for the split law: arbitrary signed integer weights,
so normalization by a common positive mass covers finite rational laws. -/
theorem massOf_split (sample : List Ω) (weight : Ω → Int) (A : Ω → Prop)
    (hit : Ω → Bool) :
    letI := Classical.propDecidable
    massOf sample weight (fun x => A x ∧ hit x = false) =
      massOf sample weight A - massOf sample weight (fun x => A x ∧ hit x = true) := by
  classical
  induction sample with
  | nil => simp [massOf]
  | cons x xs ih =>
    cases h : hit x <;> by_cases ha : A x <;>
      simp_all [massOf]
    all_goals omega

/-- Identifiability direction for subset-priority queries: given the mass
of avoiding each sublist of blockers, recover the mass hitting them all. -/
theorem recover_required (hit : ι → Ω → Bool) (mass : (Ω → Prop) → V)
    (minus : V → V → V)
    (split : ∀ (A : Ω → Prop) i,
      mass (fun x => A x ∧ hit i x = true) =
        minus (mass A) (mass (fun x => A x ∧ hit i x = false)))
    (blockers : List ι) :
    mass (observes hit blockers []) =
      exclusion minus (fun s => mass (observes hit [] s)) [] blockers := by
  let miss : ι → Ω → Bool := fun i x => !(hit i x)
  have dual (a b : List ι) : observes miss a b = observes hit b a := by
    funext x
    apply propext
    simp [observes, miss, and_comm]
  have split' (A : Ω → Prop) (i : ι) :
      mass (fun x => A x ∧ miss i x = false) =
        minus (mass A) (mass (fun x => A x ∧ miss i x = true)) := by
    simpa [miss] using split A i
  have h := exclusion_eq miss mass minus split' [] blockers
  simpa only [dual] using h

/-- Expand the exclusion recursion as a sum over sublists of forbidden tests.
The sublists are stored in reverse selection order; containment ignores order. -/
def subsets : List ι → List (List ι)
  | [] => [[]]
  | i :: rest => subsets rest ++ (subsets rest).map (· ++ [i])

def paritySign : Nat → Int
  | 0 => 1
  | n + 1 => -paritySign n

private theorem negate_sum (xs : List α) (f : α → Int) :
    (xs.map (fun x => -(f x))).sum = -(xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem sum_cat (x y : List Int) : (x ++ y).sum = x.sum + y.sum := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih, Int.add_assoc]

theorem exclusion_as_signed_sum (F : List ι → Int) (yes no : List ι) :
    exclusion (· - ·) F yes no =
      ((subsets no).map (fun b => paritySign b.length * F (b ++ yes))).sum := by
  induction no generalizing yes with
  | nil => simp [exclusion, subsets, paritySign]
  | cons i rest ih =>
    simp only [exclusion, ih, subsets, List.map_append, sum_cat,
      List.map_map, Function.comp_def, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add, paritySign, List.append_assoc, List.cons_append,
      List.nil_append, Int.neg_mul]
    rw [negate_sum]
    omega

private theorem split_capped (xs : List (List ι)) (weight : List ι → Int) (k : Nat)
    (cap : ∀ b ∈ xs, k < b.length → weight b = 0) :
    (xs.map (fun b => paritySign b.length * weight b)).sum =
      (xs.map (fun b => if b.length < k then paritySign b.length * weight b else 0)).sum +
      paritySign k * (xs.map (fun b => if b.length = k then weight b else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have tail := ih (fun b hb => cap b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons, tail, Int.mul_add]
    by_cases lt : a.length < k
    · simp [lt, Nat.ne_of_lt lt]; omega
    · by_cases eq : a.length = k
      · simp [eq]; omega
      · have zero := cap a (by simp) (by omega)
        simp [lt, eq, zero]

/-- With a hit cap, the law of the trace separates into known lower moments
and one signed sum at the highest possible additional degree. -/
theorem top_degree_trace_sum (F : List ι → Int) (yes no : List ι) (k : Nat)
    (cap : ∀ b ∈ subsets no, k < b.length → F (b ++ yes) = 0) :
    exclusion (· - ·) F yes no =
      ((subsets no).map (fun b => if b.length < k then
        paritySign b.length * F (b ++ yes) else 0)).sum +
      paritySign k * ((subsets no).map (fun b => if b.length = k then F (b ++ yes)
        else 0)).sum := by
  rw [exclusion_as_signed_sum]
  exact split_capped _ _ k cap

/-- Filtering a prefix, then including its successful endpoint, describes
exactly the record up to that endpoint under a scan capped at its length. -/
private theorem anchoredTake [DecidableEq ι] (j : ι) (tail : List ι)
    (xs ys : List ι) (hx : j ∉ xs) (hy : j ∉ ys) :
    (xs ++ j :: tail).take (ys.length + 1) = ys ++ [j] ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have ne : j ≠ y := fun e => hy (by simp [e])
      simp [List.take_succ_cons, ne]
  | cons x xs ih =>
    have nx : j ≠ x := fun e => hx (by simp [e])
    have hx' : j ∉ xs := fun hh => hx (List.mem_cons_of_mem _ hh)
    cases ys with
    | nil => simp [List.take_succ_cons, Ne.symm nx]
    | cons y ys =>
      have hy' : j ∉ ys := fun hh => hy (List.mem_cons_of_mem _ hh)
      simp [List.take_succ_cons, ih ys hx' hy']

theorem stopped_at [DecidableEq ι] (hit : ι → Bool) (pre post target : List ι)
    (j : ι) (hp : j ∉ pre) (hs : j ∉ post) (ht : j ∉ target) :
    ((pre ++ j :: post).filter hit).take (target.length + 1) = target ++ [j] ↔
      pre.filter hit = target ∧ hit j = true := by
  have hp' : j ∉ pre.filter hit := fun h => hp (List.mem_filter.mp h).1
  cases hh : hit j with
  | true =>
    simpa [List.filter_append, hh] using
      (anchoredTake j (post.filter hit) (pre.filter hit) target hp' ht)
  | false =>
    simp only [List.filter_append, List.filter_cons, hh, Bool.false_eq_true,
      ↓reduceIte, and_false, iff_false]
    intro bad
    have hj : j ∈ target ++ [j] := by simp
    rw [← bad] at hj
    have hfull := List.mem_of_mem_take hj
    rcases List.mem_append.mp hfull with h | h
    · exact hp' h
    · exact hs (List.mem_filter.mp h).1

/-- The joint law of the first r successful tests at a specified trace is
given by the inclusion-exclusion transform of the containment moments.
Here r is one plus the number of marked hits before the endpoint j. -/
theorem saturated_trace_inversion [DecidableEq ι] (hit : ι → Ω → Bool)
    (mass : (Ω → Prop) → V) (minus : V → V → V)
    (split : ∀ (A : Ω → Prop) i,
      mass (fun x => A x ∧ hit i x = false) =
        minus (mass A) (mass (fun x => A x ∧ hit i x = true)))
    (pre post : List ι) (j : ι) (marked : ι → Bool)
    (hp : j ∉ pre) (hs : j ∉ post) :
    let pos := pre.filter marked
    let neg := pre.filter fun i => !(marked i)
    mass (fun word =>
      ((pre ++ j :: post).filter (fun i => hit i word)).take (pos.length + 1) =
        pos ++ [j]) =
      exclusion minus (fun s => mass (observes hit s [])) (j :: pos) neg := by
  dsimp only
  rw [← exclusion_eq hit mass minus split]
  apply congrArg mass
  funext word
  apply propext
  rw [stopped_at (fun i => hit i word) pre post (pre.filter marked) j hp hs
    (fun h => hp (List.mem_filter.mp h).1)]
  constructor
  · rintro ⟨he, hj⟩
    constructor
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hm
      · exact hj
      · rw [← he] at hm
        exact (List.mem_filter.mp hm).2
    · intro i hi
      rcases List.mem_filter.mp hi with ⟨hm, hn⟩
      cases h : hit i word with
      | false => rfl
      | true =>
        have hh : i ∈ pre.filter (fun k => hit k word) := List.mem_filter.mpr ⟨hm, h⟩
        rw [he] at hh
        simp [(List.mem_filter.mp hh).2] at hn
  · rintro ⟨yes, no⟩
    refine ⟨List.filter_congr ?_, yes j (by simp)⟩
    intro i hi
    cases h : marked i with
    | false => exact no i (List.mem_filter.mpr ⟨hi, by simp [h]⟩)
    | true => exact yes i (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hi, h⟩))

end Screening.StoppedTrace

/- Source module: Screening.ClusterCount -/

/-! Finite counting step in the population upper bound for largest-hit records. -/
namespace Screening.ClusterCount

open Screening.LargestHits

private theorem flat_length {s : List α} {f : α → List β} {k : Nat}
    (h : ∀ a ∈ s, (f a).length = k) : (s.flatMap f).length = s.length * k := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb])), Nat.succ_mul, Nat.add_comm]

private def words (alphabet : List Nat) (tails : List (List Nat)) : Nat → List (List Nat)
  | 0 => tails
  | n + 1 => alphabet.flatMap fun i => (words alphabet tails n).map (i :: ·)

private theorem words_length (a : List Nat) (tails : List (List Nat)) (k : Nat) :
    (words a tails k).length = a.length ^ k * tails.length := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    rw [words, flat_length (k := (words a tails k).length) (by simp), ih,
      Nat.pow_succ, Nat.mul_comm (a.length ^ k) a.length, Nat.mul_assoc]

private theorem words_mem (a : List Nat) (tails : List (List Nat)) (xs tail : List Nat)
    (inside : ∀ x ∈ xs, x ∈ a) (ends : tail ∈ tails) :
    xs ++ tail ∈ words a tails xs.length := by
  induction xs with
  | nil => simpa [words] using ends
  | cons x xs ih =>
    apply List.mem_flatMap.mpr
    refine ⟨x, inside x (by simp), List.mem_map.mpr ⟨xs ++ tail, ?_, rfl⟩⟩
    exact ih (fun y hy => inside y (by simp [hy]))

private def below (j w : Nat) := (List.range (2 * w + 1)).map (fun d => j - d)

private def cover (menu : List Nat) (w ℓ k : Nat) : List (List Nat) :=
  menu.flatMap fun j => (words (below j w) (words menu [[]] k) ℓ).map (j :: ·)

private theorem cover_length (menu : List Nat) (w ℓ k : Nat) :
    (cover menu w ℓ k).length = menu.length * ((2 * w + 1)^ℓ * menu.length^k) := by
  unfold cover
  rw [flat_length (k := (2 * w + 1)^ℓ * menu.length^k) (by simp [words_length, below])]

private theorem cover_mem {w ℓ h : Nat} {menu xs : List Nat}
    (size : xs.length = h) (bounded : ∀ x ∈ xs, x ∈ menu)
    (close : nearCluster w ℓ xs = true) : xs ∈ cover menu w ℓ (h - 1 - ℓ) := by
  cases xs with
  | nil => simp [nearCluster] at close
  | cons j ys =>
    simp only [nearCluster, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at close
    obtain ⟨enough, neighbours⟩ := close
    have good (x) (hx : x ∈ ys.take ℓ) : x ∈ below j w := by
      have hh : x ∈ (j :: ys).take (ℓ + 1) := by simp [hx]
      obtain ⟨lo, hi⟩ := neighbours x hh
      apply List.mem_map.mpr
      exact ⟨j - x, List.mem_range.mpr (by omega), by omega⟩
    have tail := words_mem menu [[]] (ys.drop ℓ) []
      (fun x hx => bounded x (List.mem_cons_of_mem _ (List.mem_of_mem_drop hx))) (by simp)
    have seq := words_mem (below j w) (words menu [[]] (ys.drop ℓ).length)
      (ys.take ℓ) (ys.drop ℓ) good (by simpa using tail)
    have lens : (ys.take ℓ).length = ℓ := by
      simp only [List.length_take, List.length_cons] at *
      omega
    have lend : (ys.drop ℓ).length = h - 1 - ℓ := by
      simp only [List.length_drop, List.length_cons] at *
      omega
    rw [List.take_append_drop, lens, lend] at seq
    exact List.mem_flatMap.mpr ⟨j, bounded j (by simp),
      List.mem_map.mpr ⟨ys, seq, rfl⟩⟩

private theorem nodup_length_le [DecidableEq α] {xs ys : List α}
    (unique : xs.Nodup) (subset : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ha := subset a List.mem_cons_self
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp unique
    have sub (x) (hx : x ∈ xs) : x ∈ ys.erase a := by
      have ne : x ≠ a := fun e => fresh (e ▸ hx)
      exact (List.mem_erase_of_ne ne).mpr (subset x (List.mem_cons_of_mem _ hx))
    have H := ih rest sub
    rw [List.length_erase_of_mem ha] at H
    have hp := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- For distinct h-tuples in any finite menu, the number that can
contribute approximation error is bounded uniformly in the ordering.
The cover can have repeats; only the input list is required to be distinct. -/
theorem count_near_menu {w ℓ h : Nat} (menu : List Nat) (edges : List (List Nat))
    (unique : edges.Nodup) (sizes : ∀ e ∈ edges, e.length = h)
    (bounded : ∀ e ∈ edges, ∀ x ∈ e, x ∈ menu) :
    edges.countP (nearCluster w ℓ) ≤ menu.length * ((2 * w + 1)^ℓ * menu.length^(h - 1 - ℓ)) := by
  rw [List.countP_eq_length_filter, ← cover_length]
  apply nodup_length_le (unique.filter _)
  intro e he
  obtain ⟨he, close⟩ := List.mem_filter.mp he
  exact cover_mem (sizes e he) (bounded e he) close

/-- The counted deterministic population bound, with explicit constants
for the high- and lower-degree errors and no unknown cluster count. -/
theorem counted_surrogate_regret {reference : (Nat → Nat) → Int}
    {chosen oracle : Nat → Nat} {h w ℓ topBound lowBound : Nat} {top low : List MomentRow}
    (menu : List Nat)
    (chosenBand : Displacement chosen w) (oracleBand : Displacement oracle w)
    (positive : 0 < ℓ) (unique : (top.map MomentRow.hits).Nodup)
    (sizes : ∀ row ∈ top, row.hits.length = h)
    (bounded : ∀ row ∈ top, ∀ i ∈ row.hits, i ∈ menu)
    (sorted : ∀ row ∈ top, Descending row.hits)
    (topWeights : ∀ row ∈ top, row.weight.natAbs ≤ topBound)
    (lowWeights : ∀ row ∈ low, row.weight.natAbs ≤ lowBound)
    (preferred : surrogateScore reference ℓ top chosen ≤ surrogateScore reference ℓ top oracle) :
    trueScore reference top low chosen - trueScore reference top low oracle ≤
      (2 * ((2*w*topBound) * (menu.length * ((2*w+1)^ℓ * menu.length^(h-1-ℓ))) +
        (w*lowBound)*low.length) : Nat) := by
  have coverBound := count_near_menu (w := w) (ℓ := ℓ) (h := h) menu
    (top.map MomentRow.hits) unique
    (fun e he => by obtain ⟨row, hr, rfl⟩ := List.mem_map.mp he; exact sizes row hr)
    (fun e he => by obtain ⟨row, hr, rfl⟩ := List.mem_map.mp he; exact bounded row hr)
  rw [List.countP_map] at coverBound
  apply Int.le_trans (surrogate_minimizer_regret chosenBand oracleBand positive sorted
    topWeights lowWeights preferred)
  apply Int.ofNat_le.mpr
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ coverBound) _)

end Screening.ClusterCount

/- Source module: Screening.ScreeningCost -/

/-!
First-hit costs for unit-price tests. A miss on the entire order incurs a
fallback charge, including when the order is empty. We give the signed
exchange criterion for integer-weighted finite laws and additive identities
for arbitrary finite weights. All identities also hold separately per outcome.
-/

namespace Screening.ScreeningCost

/-- Operational cost of running the scan on a single outcome. -/
def scan (hit : T → Bool) (fallback : Nat) : List T → Nat
  | [] => fallback
  | i :: tail => if hit i then 1 else 1 + scan hit fallback tail

/-- Whether the scan finds no hit amongst the specified tests. -/
def survives (hit : T → Bool) (tests : List T) : Bool :=
  tests.all (fun i => !(hit i))

/-- Prefixes of lengths 0, 1, ..., n-1, one for each attempted-test position. -/
def properPrefixes (tests : List T) : List (List T) :=
  (List.range tests.length).map (fun k => tests.take k)

private theorem properPrefixes_cons (i : T) (tail : List T) :
    properPrefixes (i :: tail) = [] :: (properPrefixes tail).map (i :: ·) := by
  simp [properPrefixes, List.range_succ_eq_map, List.map_map, Function.comp_def]

def total (xs : List A) (f : A → Nat) : Nat := (xs.map f).sum

private theorem total_cons (a : A) (xs : List A) (f : A → Nat) :
    total (a :: xs) f = f a + total xs f := rfl

private theorem total_zero (xs : List A) : total xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [total_cons, ih]

private theorem total_map (xs : List A) (g : A → B) (f : B → Nat) :
    total (xs.map g) f = total xs (fun x => f (g x)) := by
  simp [total, List.map_map, Function.comp_def]

private theorem total_add (xs : List A) (f g : A → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [total_cons, ih]
    omega

/-- A test costs one precisely when its predecessors have all missed. -/
theorem scan_eq_prefix_survivals (hit : T → Bool) (fallback : Nat) (order : List T) :
    scan hit fallback order =
      total (properPrefixes order) (fun pre => (survives hit pre).toNat) +
      fallback * (survives hit order).toNat := by
  induction order with
  | nil => simp [scan, properPrefixes, total, survives]
  | cons i tail ih =>
    rw [properPrefixes_cons, total_cons, total_map]
    cases hc : hit i with
    | true => simp [scan, survives, hc, total_zero]
    | false =>
      simpa [scan, survives, hc, Nat.add_assoc] using ih

/-- On an arbitrary outcome this event is exactly "i hits and all of pre miss." -/
def newHit (hit : T → Bool) (pre : List T) (i : T) : Nat :=
  (survives hit pre && hit i).toNat

/-- Inserting a test anywhere in a prefix partitions the previously surviving
outcomes into survivors and new hits. This applies separately to each changed
prefix of a nonadjacent exchange. -/
theorem inserted_test_partition (hit : T → Bool) (pre middle : List T) (i : T) :
    (survives hit (pre ++ i :: middle)).toNat + newHit hit (pre ++ middle) i =
      (survives hit (pre ++ middle)).toNat := by
  cases hp : survives hit pre <;> cases hm : survives hit middle <;> cases hi : hit i <;>
    simp [newHit, survives, List.all_append] at hp hm ⊢ <;>
    simp_all

/-- Adjacent interchange, expressed in naturals without truncated subtraction. -/
theorem swap_balance (hit : T → Bool) (fallback : Nat) (pre suf : List T) (i j : T) :
    scan hit fallback (pre ++ i :: j :: suf) + newHit hit pre i =
      scan hit fallback (pre ++ j :: i :: suf) + newHit hit pre j := by
  induction pre with
  | nil =>
    cases hi : hit i <;> cases hj : hit j <;>
      simp [scan, newHit, survives, hi, hj]
  | cons k pre ih =>
    cases hk : hit k with
    | true => simp [scan, newHit, survives, hk]
    | false =>
      simpa [scan, newHit, survives, hk, Nat.add_assoc] using ih

/-- Sum over an explicitly weighted finite population, permitting repeats. -/
def weighted (law : List (X × Nat)) (f : X → Nat) : Nat :=
  total law (fun atom => atom.2 * f atom.1)

private theorem weighted_add (law : List (X × Nat)) (f g : X → Nat) :
    weighted law (fun x => f x + g x) = weighted law f + weighted law g := by
  simp only [weighted, Nat.mul_add, total_add]

private theorem weighted_mul (law : List (X × Nat)) (c : Nat) (f : X → Nat) :
    weighted law (fun x => c * f x) = c * weighted law f := by
  induction law with
  | nil => simp [weighted, total]
  | cons atom law ih =>
    change atom.2 * (c * f atom.1) + weighted law (fun x => c * f x) =
      c * (atom.2 * f atom.1 + weighted law f)
    rw [ih, Nat.mul_add, Nat.mul_left_comm atom.2 c]

private theorem weighted_total (law : List (X × Nat)) (ys : List A) (f : X → A → Nat) :
    weighted law (fun x => total ys (f x)) =
      total ys (fun y => weighted law (fun x => f x y)) := by
  induction ys with
  | nil =>
    change total law (fun atom => atom.2 * 0) = 0
    simpa only [Nat.mul_zero] using total_zero law
  | cons y ys ih =>
    simp only [total_cons, weighted_add, ih]

def populationCost (law : List (X × Nat)) (hit : X → T → Bool)
    (fallback : Nat) (order : List T) : Nat :=
  weighted law (fun x => scan (hit x) fallback order)

def survivalMass (law : List (X × Nat)) (hit : X → T → Bool) (pre : List T) : Nat :=
  weighted law (fun x => (survives (hit x) pre).toNat)

def newHitMass (law : List (X × Nat)) (hit : X → T → Bool) (pre : List T) (i : T) : Nat :=
  weighted law (fun x => newHit (hit x) pre i)

/-- Prefixwise replacement identity for the nonadjacent precedence argument.
Here pre and middle contain precisely the tests common to the two prefixes. -/
theorem survival_replacement (law : List (X × Nat)) (hit : X → T → Bool)
    (pre middle : List T) (i j : T) :
    (survivalMass law hit (pre ++ j :: middle) : Int) -
      survivalMass law hit (pre ++ i :: middle) =
      (newHitMass law hit (pre ++ middle) i : Int) - newHitMass law hit (pre ++ middle) j := by
  have part (a : T) := congrArg (weighted law) (funext
    (fun x => inserted_test_partition (hit x) pre middle a))
  have hi := part i
  have hj := part j
  simp only [weighted_add] at hi hj
  unfold survivalMass newHitMass
  omega

/-- Exact finite-population identity, including the fallback on no-hit inputs. -/
theorem populationCost_eq_prefix_survivals (law : List (X × Nat))
    (hit : X → T → Bool) (fallback : Nat) (order : List T) :
    populationCost law hit fallback order =
      total (properPrefixes order) (survivalMass law hit) +
      fallback * survivalMass law hit order := by
  unfold populationCost survivalMass
  simp only [scan_eq_prefix_survivals, weighted_add, weighted_total, weighted_mul]

/-- Saving from exchanging j,i for i,j equals the difference in their
new-hit masses after exactly the same prefix. Arbitrary suffix and fallback. -/
theorem population_adjacent_exchange (law : List (X × Nat)) (hit : X → T → Bool)
    (fallback : Nat) (pre suf : List T) (i j : T) :
    (populationCost law hit fallback (pre ++ j :: i :: suf) : Int) -
      populationCost law hit fallback (pre ++ i :: j :: suf) =
      (newHitMass law hit pre i : Int) - newHitMass law hit pre j := by
  have balance := congrArg (weighted law) (funext
    (fun x => swap_balance (hit x) fallback pre suf i j))
  simp only [weighted_add] at balance
  change populationCost law hit fallback (pre ++ i :: j :: suf) + newHitMass law hit pre i =
    populationCost law hit fallback (pre ++ j :: i :: suf) + newHitMass law hit pre j at balance
  omega

/-- A comparison of the two hazards is necessary and sufficient for the
corresponding strict local improvement. -/
theorem adjacent_strict_iff (law : List (X × Nat)) (hit : X → T → Bool)
    (fallback : Nat) (pre suf : List T) (i j : T) :
    populationCost law hit fallback (pre ++ i :: j :: suf) <
      populationCost law hit fallback (pre ++ j :: i :: suf) ↔
      newHitMass law hit pre j < newHitMass law hit pre i := by
  have h := population_adjacent_exchange law hit fallback pre suf i j
  omega

section ArbitraryWeights

/-! These additive identities also apply to finite laws with irrational
weights. Only addition of weights and multiplication by a natural count are
needed. The instances below are the standard commutative-monoid identities. -/

variable {M : Type} [Add M] [Zero M]
  [Std.Associative (fun a b : M => a + b)]
  [Std.Commutative (fun a b : M => a + b)]
  [Std.LawfulIdentity (fun a b : M => a + b) 0]

def copies (v : M) : Nat → M
  | 0 => 0
  | n + 1 => v + copies v n

def massIntegral (law : List (X × M)) (f : X → Nat) : M :=
  (law.map (fun a => copies a.2 (f a.1))).sum

omit [Std.Commutative (fun a b : M => a + b)] in
private theorem copies_add (v : M) (n k : Nat) :
    copies v (n + k) = copies v n + copies v k := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, copies]
    exact (Std.LawfulLeftIdentity.left_id (op := fun a b : M => a + b) _).symm
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [copies, ih]
    exact (Std.Associative.assoc (op := fun a b : M => a + b) _ _ _).symm

private theorem integral_add (law : List (X × M)) (f g : X → Nat) :
    massIntegral law (fun x => f x + g x) = massIntegral law f + massIntegral law g := by
  induction law with
  | nil =>
    exact (Std.LawfulLeftIdentity.left_id (op := fun a b : M => a + b) 0).symm
  | cons a law ih =>
    change copies a.2 (f a.1 + g a.1) + massIntegral law (fun x => f x + g x) =
      (copies a.2 (f a.1) + massIntegral law f) + (copies a.2 (g a.1) + massIntegral law g)
    rw [copies_add, ih]
    ac_rfl

omit [Std.Associative (fun a b : M => a + b)] [Std.Commutative (fun a b : M => a + b)] in
private theorem integral_zero (law : List (X × M)) :
    massIntegral law (fun _ => 0) = 0 := by
  induction law with
  | nil => rfl
  | cons a law ih =>
    change 0 + massIntegral law (fun _ => 0) = 0
    rw [ih]
    exact Std.LawfulLeftIdentity.left_id (op := fun a b : M => a + b) 0

private theorem integral_scale (law : List (X × M)) (f : X → Nat) (k : Nat) :
    massIntegral law (fun x => k * f x) = copies (massIntegral law f) k := by
  induction k with
  | zero => simpa only [Nat.zero_mul, copies] using integral_zero law
  | succ k ih =>
    simp only [Nat.succ_mul, integral_add, copies, ih]
    exact Std.Commutative.comm (op := fun a b : M => a + b) _ _

private theorem integral_total (law : List (X × M)) (xs : List A) (f : X → A → Nat) :
    massIntegral law (fun x => total xs (f x)) =
      (xs.map (fun i => massIntegral law (fun x => f x i))).sum := by
  induction xs with
  | nil => exact integral_zero law
  | cons i xs ih => simp only [total_cons, integral_add, List.map_cons, List.sum_cons, ih]

theorem any_weights_prefix_cost (law : List (X × M)) (hit : X → T → Bool)
    (fallback : Nat) (order : List T) :
    massIntegral law (fun x => scan (hit x) fallback order) =
      ((properPrefixes order).map (fun pre =>
        massIntegral law (fun x => (survives (hit x) pre).toNat))).sum +
      copies (massIntegral law (fun x => (survives (hit x) order).toNat)) fallback := by
  simp only [scan_eq_prefix_survivals, integral_add, integral_total, integral_scale]

theorem any_weights_adjacent_exchange (law : List (X × M)) (hit : X → T → Bool)
    (fallback : Nat) (pre suf : List T) (i j : T) :
    massIntegral law (fun x => scan (hit x) fallback (pre ++ i :: j :: suf)) +
      massIntegral law (fun x => newHit (hit x) pre i) =
    massIntegral law (fun x => scan (hit x) fallback (pre ++ j :: i :: suf)) +
      massIntegral law (fun x => newHit (hit x) pre j) := by
  have balance := congrArg (massIntegral law) (funext
    (fun x => swap_balance (hit x) fallback pre suf i j))
  simpa only [integral_add] using balance

end ArbitraryWeights

end Screening.ScreeningCost

/- Source module: Screening.PacketArithmetic -/

/-! Reciprocal reduction and the packed unsigned divisibility test. -/
namespace Screening.PacketArithmetic

def quotient (B v n : Nat) : Nat := n*v/B

def residue (B M v n : Nat) : Nat := n - quotient B v n * M

/-- Both floor(B/M) and floor((B−1)/M) are valid reciprocals. The
second is exactly the reciprocal computed from UINT64_MAX in packet.hpp. -/
def ValidReciprocal (B M v : Nat) : Prop :=
  v*M ≤ B ∧ B ≤ v*M + M

theorem floor_reciprocal {B M : Nat} (hm : 0 < M) : ValidReciprocal B M (B/M) := by
  constructor
  · exact Nat.div_mul_le_self _ _
  · have h := Nat.div_add_mod B M
    have hmod := Nat.mod_lt B hm
    rw [Nat.mul_comm M] at h
    omega

theorem maxword_reciprocal {B M : Nat} (hB : 0 < B) (hm : 0 < M) :
    ValidReciprocal B M ((B-1)/M) := by
  constructor
  · exact Nat.le_trans (Nat.div_mul_le_self _ _) (Nat.sub_le _ _)
  · have h := Nat.div_add_mod (B-1) M
    have hmod := Nat.mod_lt (B-1) hm
    rw [Nat.mul_comm M] at h
    omega

/-- The estimated product never exceeds n, and one more correction
beyond the next multiple of M exceeds n strictly. -/
theorem bracket {B M v n : Nat} (hm : 0 < M) (hn : n < B)
    (hv : ValidReciprocal B M v) :
    quotient B v n * M ≤ n ∧ n < (quotient B v n + 2)*M := by
  have hB : 0 < B := by omega
  obtain ⟨hvlo,hvhi⟩ := hv
  let q := quotient B v n
  have hlo : q*B ≤ n*v := Nat.div_mul_le_self _ _
  have hhi : n*v < (q+1)*B :=
    (Nat.div_lt_iff_lt_mul hB).mp (Nat.lt_succ_self q)
  constructor
  · apply Nat.le_of_mul_le_mul_left (c := B) _ hB
    calc B*(q*M) = (q*B)*M := by ac_rfl
         _ ≤ (n*v)*M := Nat.mul_le_mul_right M hlo
         _ = n*(v*M) := Nat.mul_assoc _ _ _
         _ ≤ n*B := Nat.mul_le_mul_left n hvlo
         _ = B*n := Nat.mul_comm _ _
  · apply Nat.lt_of_mul_lt_mul_left (a := B)
    calc B*n = n*B := Nat.mul_comm _ _
         _ ≤ n*(v*M+M) := Nat.mul_le_mul_left n hvhi
         _ = (n*v)*M+n*M := by rw [Nat.mul_add, Nat.mul_assoc]
         _ < ((q+1)*B)*M+B*M :=
           Nat.add_lt_add (Nat.mul_lt_mul_of_pos_right hhi hm)
             (Nat.mul_lt_mul_of_pos_right hn hm)
         _ = B*((q+2)*M) := by
           simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, Nat.two_mul,
             Nat.mul_two]
           ac_rfl

theorem quotient_exact_or_one_low {B M v n : Nat} (hm : 0 < M) (hn : n < B)
    (hv : ValidReciprocal B M v) :
    n/M = quotient B v n ∨ n/M = quotient B v n + 1 := by
  obtain ⟨hl,hu⟩ := bracket hm hn hv
  have hlo := (Nat.le_div_iff_mul_le hm).mpr hl
  have hhi := (Nat.div_lt_iff_lt_mul hm).mpr hu
  omega

theorem residue_lt_twice {B M v n : Nat} (hm : 0 < M) (hn : n < B)
    (hv : ValidReciprocal B M v) : residue B M v n < 2*M := by
  obtain ⟨hl,hu⟩ := bracket hm hn hv
  rw [Nat.add_mul] at hu
  unfold residue
  omega

theorem residue_dvd_iff {B M v n p : Nat} (hm : 0 < M) (hn : n < B)
    (hv : ValidReciprocal B M v) (hp : p ∣ M) :
    p ∣ residue B M v n ↔ p ∣ n := by
  have hprod := Nat.dvd_trans hp (Nat.dvd_mul_left M (quotient B v n))
  have heq : residue B M v n + quotient B v n*M = n :=
    Nat.sub_add_cancel (bracket hm hn hv).1
  constructor
  · intro hr
    rw [← heq]
    exact Nat.dvd_add hr hprod
  · intro h
    exact Nat.dvd_sub h hprod

/-- A 32-bit machine subtraction can use only the low input and quotient:
they recover the *entire* mathematical remainder, since it fits in one lane. -/
private theorem ofNat_mul (width a b : Nat) :
    BitVec.ofNat width a * BitVec.ofNat width b = BitVec.ofNat width (a*b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mul_mod, Nat.mul_mod_mod]

theorem low_lane_reduction {width n q M : Nat} (hl : q*M ≤ n)
    (hfits : n-q*M < 2^width) :
    (BitVec.ofNat width n - BitVec.ofNat width q * BitVec.ofNat width M).toNat = n-q*M := by
  have heq : BitVec.ofNat width n - BitVec.ofNat width q * BitVec.ofNat width M =
      BitVec.ofNat width (n-q*M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    rw [ofNat_mul, ← BitVec.ofNat_add, Nat.sub_add_cancel hl]
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfits]

theorem packet64 {n M : Nat} (hn : n < 2^64) (hm : 0 < M) (hsize : M < 2^31) :
    let v := (2^64-1)/M
    let q := quotient (2^64) v n
    let r := residue (2^64) M v n
    (n/M = q ∨ n/M = q+1) ∧ r < 2*M ∧ r < 2^32 ∧
    (BitVec.ofNat 32 n - BitVec.ofNat 32 q * BitVec.ofNat 32 M).toNat = r ∧
    (∀ p, p ∣ M → (p ∣ r ↔ p ∣ n)) := by
  dsimp only
  have hv := maxword_reciprocal (B := 2^64) (by decide) hm
  have hr := residue_lt_twice hm hn hv
  have h32 : residue (2^64) M ((2^64-1)/M) n < 2^32 := by omega
  exact ⟨quotient_exact_or_one_low hm hn hv,hr,h32,
    low_lane_reduction (bracket hm hn hv).1 h32, fun _ hp => residue_dvd_iff hm hn hv hp⟩

/-- Multiplication by a modular inverse turns divisibility into one unsigned
comparison. The inverse identity is a precondition on the supplied table. -/
theorem inverse_cutoff {W p a r : Nat} (hp : 0 < p) (hr : r < W)
    (hinv : (p*a)%W = 1) :
    (r*a)%W ≤ (W-1)/p ↔ p ∣ r := by
  have cancel (k : Nat) : k*(p*a)%W = k%W := by
    rw [← Nat.mul_mod_mod k (p*a) W, hinv, Nat.mul_one]
  constructor
  · intro h
    let k := (r*a)%W
    have hkp : k*p ≤ W-1 := (Nat.le_div_iff_mul_le hp).mp h
    have hk : k*p < W := by omega
    have heq : k*p = r := calc
      k*p = k*p%W := (Nat.mod_eq_of_lt hk).symm
      _ = (r*a)*p%W := Nat.mod_mul_mod (r*a) p W
      _ = r*(p*a)%W := by ac_rfl
      _ = r%W := cancel r
      _ = r := Nat.mod_eq_of_lt hr
    exact ⟨k, by rw [← heq, Nat.mul_comm]⟩
  · rintro ⟨k,rfl⟩
    have hk : k < W :=
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left k hp) hr
    have heq : (p*k)*a%W = k := calc
      _ = k*(p*a)%W := by ac_rfl
      _ = k%W := cancel k
      _ = k := Nat.mod_eq_of_lt hk
    rw [heq]
    apply (Nat.le_div_iff_mul_le hp).mpr
    rw [Nat.mul_comm]
    omega

/-- Truncating a full-word inverse to a lane preserves the inverse identity. -/
theorem low32_inverse {p a : Nat} (hinv : (p*a)%(2^64) = 1) :
    (p*(a%(2^32)))%(2^32) = 1 := by
  rw [Nat.mul_mod_mod, ← Nat.mod_mod_of_dvd (p*a) (show 2^32 ∣ 2^64 by decide), hinv]

/-- Complete single-slot predicate of the 32-bit SIMD screen, from the high
product quotient through the wrapped lane product and unsigned comparison. -/
theorem packed_test64 {n M p a : Nat} (hn : n < 2^64) (hm : 0 < M)
    (hsize : M < 2^31) (hp : 0 < p) (hpm : p ∣ M)
    (hinv : (p*a)%(2^64) = 1) :
    let q := quotient (2^64) ((2^64-1)/M) n
    let lane := BitVec.ofNat 32 n - BitVec.ofNat 32 q * BitVec.ofNat 32 M
    (lane * BitVec.ofNat 32 a).toNat ≤ (2^32-1)/p ↔ p ∣ n := by
  dsimp only
  obtain ⟨_,_,hfits,hlane,hdiv⟩ := packet64 hn hm hsize
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hlane]
  exact (inverse_cutoff hp hfits (low32_inverse hinv)).trans (hdiv p hpm)

end Screening.PacketArithmetic

/- Source module: Screening.IntervalCounts -/

/-! Counting literal divisible words among L consecutive odd integers. -/
namespace Screening.IntervalCounts

def word (a k : Nat) := 2*(a+k)+1

def hitCount (a q L : Nat) : Nat :=
  (List.range L).countP (fun k => decide (q ∣ word a k))

/-- The literal congruence is a single residue class of the odd-word index;
the shift q/2+1 is determined by q. -/
theorem odd_index_congruence {q : Nat} (hodd : q%2 = 1) (u : Nat) :
    q ∣ 2*u+1 ↔ q ∣ u+q/2+1 := by
  have hg : q.gcd 2 = 1 := by rw [Nat.gcd_comm q 2, Nat.gcd_rec, hodd]; decide
  have heq : 2*(u+q/2+1) = (2*u+1)+q := by omega
  calc q ∣ 2*u+1 ↔ q ∣ (2*u+1)+q := Nat.dvd_add_iff_left (Nat.dvd_refl q)
       _ ↔ q ∣ 2*(u+q/2+1) := by rw [heq]
       _ ↔ q ∣ u+q/2+1 := by
          simpa [hg] using (Nat.dvd_gcd_mul_iff_dvd_mul (k:=q) (n:=2) (m:=u+q/2+1)).symm

/-- Exact prefix difference in a form that avoids truncated subtraction. -/
theorem prefix_identity {q : Nat} (hodd : q%2 = 1) (a L : Nat) :
    (a+q/2)/q + hitCount a q L = (a+q/2+L)/q := by
  induction L with
  | zero => simp [hitCount]
  | succ L ih =>
    have step : hitCount a q (L+1) =
        hitCount a q L + (if q ∣ a+q/2+L+1 then 1 else 0) := by
      simp only [hitCount, List.range_succ, List.countP_append, List.countP_singleton,
        decide_eq_true_eq]
      have h := odd_index_congruence hodd (a+L)
      simp only [word, Nat.add_right_comm a L (q/2), h]
    rw [step, ← Nat.add_assoc, ih]
    simpa only [Nat.add_assoc] using (Nat.succ_div (a:=a+q/2+L) (b:=q)).symm

theorem exact_hit_count {q : Nat} (hodd : q%2 = 1) (a L : Nat) :
    hitCount a q L = (a+q/2+L)/q - (a+q/2)/q := by
  have := prefix_identity hodd a L
  omega

/-- Ceiling of L/q for positive q, including the exact multiple case. -/
def ceilingQuotient (L q : Nat) := L/q + if L%q = 0 then 0 else 1

theorem floor_or_ceiling {q : Nat} (hodd : q%2 = 1) (a L : Nat) :
    hitCount a q L = L/q ∨ hitCount a q L = ceilingQuotient L q := by
  have hq : 0 < q := by omega
  have h := prefix_identity hodd a L
  rw [Nat.add_div (a:=a+q/2) (b:=L) hq] at h
  have hmod := Nat.mod_lt (a+q/2) hq
  unfold ceilingQuotient
  split at h <;> split <;> omega

/-- Fractions need not be in lowest terms. At positive denominators these
are the ordinary absolute difference and strict comparison of fractions. -/
structure Fraction where
  num : Nat
  den : Nat

def Fraction.absDifference (x y : Fraction) : Fraction :=
  ⟨max (x.num*y.den - y.num*x.den) (y.num*x.den - x.num*y.den), x.den*y.den⟩

def Fraction.less (x y : Fraction) := x.num*y.den < y.num*x.den

theorem count_error {q : Nat} (hodd : q%2 = 1) (a L : Nat) :
    max (hitCount a q L*q-L) (L-hitCount a q L*q) < q := by
  have hq : 0 < q := by omega
  have remainder := Nat.div_add_mod L q
  rw [Nat.mul_comm q] at remainder
  have small := Nat.mod_lt L hq
  rcases floor_or_ceiling hodd a L with h|h
  · rw [h]; omega
  · rw [h]; unfold ceilingQuotient
    split <;> simp only [Nat.add_zero, Nat.add_mul, Nat.one_mul] <;> omega

/-- For L>0 this is |hitCount/L − 1/q| < 1/L, using cross multiplication
over natural numbers, with positive denominators. -/
theorem normalized_probability_error {q L : Nat} (hodd : q%2 = 1) (hL : 0 < L) (a : Nat) :
    (Fraction.absDifference ⟨hitCount a q L,L⟩ ⟨1,q⟩).less ⟨1,L⟩ := by
  have result := Nat.mul_lt_mul_of_pos_right (count_error hodd a L) hL
  simpa only [Fraction.less, Fraction.absDifference, Nat.one_mul, Nat.mul_comm q L] using result

def product : List Nat → Nat
  | [] => 1
  | p :: ps => p * product ps

/-- Elementary divisor definition of primality, using only the standard library. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

private theorem prime_gcd {p r : Nat} (hp : IsPrime p) (hr : IsPrime r) (hne : p ≠ r) :
    p.gcd r = 1 := by
  rcases hp.2 _ (Nat.gcd_dvd_left p r) with done | heq
  · exact done
  · have hpr := Nat.gcd_dvd_right p r
    rw [heq] at hpr
    rcases hr.2 p hpr with h | h
    · have := hp.1; omega
    · exact False.elim (hne h)

private theorem coprime_product (p : Nat) (ps : List Nat)
    (h : ∀ q ∈ ps, p.gcd q = 1) : p.gcd (product ps) = 1 := by
  induction ps with
  | nil => simp [product]
  | cons q qs ih =>
    have hq := h q (by simp)
    have hrest := ih (fun r hr => h r (by simp [hr]))
    apply Nat.eq_one_of_dvd_one
    simpa only [product, hq, hrest, Nat.one_mul] using
      (Nat.gcd_mul_dvd_mul_gcd p q (product qs))

theorem product_dvd_iff (ps : List Nat) (hd : ps.Nodup) (hp : ∀ p ∈ ps, IsPrime p) (n : Nat) :
    product ps ∣ n ↔ ∀ p ∈ ps, p ∣ n := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hd
    have htail := fun q (hq : q ∈ ps) => hp q (by simp [hq])
    have hcop := coprime_product p ps (fun q hq =>
      prime_gcd (hp p (by simp)) (htail q hq) (fun heq => hnot (heq ▸ hq)))
    have hlcm := Nat.gcd_mul_lcm p (product ps)
    rw [hcop,Nat.one_mul] at hlcm
    constructor
    · intro h q hq
      rcases List.mem_cons.mp hq with e | hmem
      · subst q; exact Nat.dvd_trans (Nat.dvd_mul_right p (product ps)) h
      · exact (ih hnodup htail).mp (Nat.dvd_trans (Nat.dvd_mul_left (product ps) p) h) q hmem
    · intro h
      change p * product ps ∣ n
      rw [← hlcm]
      exact Nat.lcm_dvd (h p (by simp)) ((ih hnodup htail).mpr (fun q hq => h q (by simp [hq])))

theorem odd_product (ps : List Nat) (ho : ∀ p ∈ ps, p%2 = 1) : product ps % 2 = 1 := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    rw [product, Nat.mul_mod, ho p (by simp), ih (fun q hq => ho q (by simp [hq]))]

/-- Literal containment count from testing every selected prime separately. -/
def containmentCount (a L : Nat) (ps : List Nat) : Nat :=
  (List.range L).countP (fun k => ps.all (fun p => decide (p ∣ word a k)))

theorem containment_eq (a L : Nat) (ps : List Nat) (hd : ps.Nodup)
    (hp : ∀ p ∈ ps, IsPrime p) : containmentCount a L ps = hitCount a (product ps) L := by
  apply List.countP_congr
  intro k _
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact (product_dvd_iff ps hd hp _).symm

theorem uniform_containment_error {L : Nat} (hL : 0 < L) (a : Nat)
    (ps : List Nat) (hd : ps.Nodup) (hp : ∀ p ∈ ps, IsPrime p) (ho : ∀ p ∈ ps, p%2 = 1) :
    (Fraction.absDifference ⟨containmentCount a L ps,L⟩ ⟨1,product ps⟩).less ⟨1,L⟩ := by
  rw [containment_eq a L ps hd hp]
  exact normalized_probability_error (odd_product ps ho) hL a

private theorem power_le_product (P : Nat) (ps : List Nat) (h : ∀ p ∈ ps, P ≤ p) :
    P^ps.length ≤ product ps := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    have ht := ih (fun q hq => h q (by simp [hq]))
    simp only [List.length_cons, Nat.pow_succ, product, Nat.mul_comm p (product ps)]
    exact Nat.mul_le_mul ht (h p (by simp))

/-- The actual number of hits among distinct menu primes cannot exceed h on
the paper's interval [2L,4L) when 4L < P^(h+1). -/
theorem natural_window_hit_cap {L P h k : Nat} (hk : k < L) (hP : 0 < P)
    (hwindow : 4*L < P^(h+1)) (ps : List Nat) (hd : ps.Nodup)
    (hp : ∀ p ∈ ps, IsPrime p) (hlo : ∀ p ∈ ps, P ≤ p) :
    (ps.filter (fun p => decide (p ∣ word L k))).length ≤ h := by
  let selected := ps.filter (fun p => decide (p ∣ word L k))
  have hm {p} (hs : p ∈ selected) : p ∈ ps ∧ p ∣ word L k := by
    simpa [selected] using hs
  have hprod := (product_dvd_iff selected (List.Pairwise.filter _ hd)
    (fun p hs => hp p (hm hs).1) (word L k)).mpr (fun _ hs => (hm hs).2)
  have hpositive : 0 < word L k := by simp [word]
  have word_lt : word L k < 4*L := by unfold word; omega
  have product_bound := Nat.le_of_dvd hpositive hprod
  have power_bound := power_le_product P selected (fun p hs => hlo p (hm hs).1)
  change selected.length ≤ h
  apply Nat.le_of_not_gt
  intro hmuch
  have hfinal := Nat.pow_le_pow_right hP (show h+1 ≤ selected.length by omega)
  omega

end Screening.IntervalCounts

/- Source module: Screening.MomentCube -/

/-! Signed perturbation of the exact hit cells on a finite edge. Here a set
is listed in the order inherited from the edge; queries can use any order.
The moment is a sum over enumerated cells, independent of any observation map. -/

namespace Screening.MomentCube

/-- Enumerate all subsets, excluding and including the first vertex in turn. -/
def cells : List V → List (List V)
  | [] => [[]]
  | v :: rest => cells rest ++ (cells rest).map (v :: ·)

theorem mem_cells {cell edge : List V} : cell ∈ cells edge ↔ cell.Sublist edge := by
  induction edge generalizing cell with
  | nil => simp [cells]
  | cons v rest ih =>
    rw [cells, List.mem_append, List.sublist_cons_iff]
    simp only [List.mem_map, ih]
    constructor
    · rintro (h | ⟨t, ht, he⟩)
      · exact Or.inl h
      · exact Or.inr ⟨t, he.symm, ht⟩
    · rintro (h | ⟨t, he, ht⟩)
      · exact Or.inl h
      · exact Or.inr ⟨t, ht, he.symm⟩

/-- Distinct vertices give distinct cells, each listed exactly once. -/
theorem cells_nodup {edge : List V} (hd : edge.Nodup) : (cells edge).Nodup := by
  induction edge with
  | nil => simp [cells]
  | cons v rest ih =>
    obtain ⟨hv, hr⟩ := List.nodup_cons.mp hd
    have hn := ih hr
    change List.Pairwise (· ≠ ·) (cells rest ++ (cells rest).map (v :: ·))
    apply List.pairwise_append.mpr
    refine ⟨hn, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      exact hn.imp (fun h he => h (List.cons.inj he).2)
    · intro a ha b hb he
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
      subst a
      exact hv ((mem_cells.mp ha).subset (by simp))

def sumOn (xs : List A) (f : A → Int) : Int := (xs.map f).sum

private theorem sum_append (xs ys : List A) (f : A → Int) :
    sumOn (xs ++ ys) f = sumOn xs f + sumOn ys f := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    change f a + sumOn (xs ++ ys) f = (f a + sumOn xs f) + sumOn ys f
    rw [ih, Int.add_assoc]

private theorem sum_negative (xs : List A) (f : A → Int) :
    sumOn xs (fun x => -f x) = -sumOn xs f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change -f a + sumOn xs (fun x => -f x) = -(f a + sumOn xs f)
    rw [ih, Int.neg_add]

private theorem sum_congr_on (xs : List A) {f g : A → Int}
    (h : ∀ x ∈ xs, f x = g x) : sumOn xs f = sumOn xs g :=
  congrArg List.sum (List.map_congr_left h)

private theorem sum_zero (xs : List A) : sumOn xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change 0 + sumOn xs (fun _ => 0) = 0; omega

/-- Integral of a statistic against the actual cube, with mass
`(-1)^cell.length` on every subset of the specified edge. -/
def alternating (edge : List V) (f : List V → Int) : Int :=
  sumOn (cells edge) (fun cell => (-1 : Int) ^ cell.length * f cell)

private theorem alternating_cons (v : V) (edge : List V) (f : List V → Int) :
    alternating (v :: edge) f = alternating edge f - alternating edge (fun t => f (v :: t)) := by
  unfold alternating
  rw [cells, sum_append]
  have m : sumOn ((cells edge).map (v :: ·)) (fun cell => (-1 : Int)^cell.length * f cell) =
      sumOn (cells edge) (fun t => -((-1 : Int)^t.length * f (v :: t))) := by
    simp [sumOn, List.map_map, Function.comp_def, Int.pow_succ, Int.neg_mul]
  rw [m, sum_negative, Int.sub_eq_add_neg]

/-- Invariance under inserting a given edge vertex anywhere forces
the alternating sum to vanish, by cancellation in the explicit power set. -/
theorem free_vertex_cancel (edge : List V) (v : V) (hv : v ∈ edge)
    (f : List V → Int)
    (free : ∀ left right : List V, f (left ++ v :: right) = f (left ++ right)) :
    alternating edge f = 0 := by
  induction edge generalizing f with
  | nil => simp at hv
  | cons u rest ih =>
    rw [alternating_cons]
    rcases List.mem_cons.mp hv with he | hrest
    · subst u
      have h : (fun t => f (v :: t)) = f := funext (fun t => free [] t)
      rw [h, Int.sub_self]
    · rw [ih hrest f free]
      have h : alternating rest (fun t => f (u :: t)) = 0 :=
        ih hrest _ (fun left right => free (u :: left) right)
      rw [h]; rfl

/-- The containment moment for query Q integrates its indicator, Q ⊆ cell. -/
def moment [DecidableEq V] (edge query : List V) : Int :=
  alternating edge (fun cell => if query ⊆ cell then 1 else 0)

theorem missing_edge_vertex [DecidableEq V] (edge query : List V) (v : V)
    (inEdge : v ∈ edge) (notQueried : v ∉ query) : moment edge query = 0 := by
  apply free_vertex_cancel edge v inEdge
  intro left right
  have h : query ⊆ left ++ v :: right ↔ query ⊆ left ++ right := by
    constructor
    · intro hs i hi
      have he := hs hi
      rcases List.mem_append.mp he with hL | hR
      · exact List.mem_append.mpr (Or.inl hL)
      · rcases List.mem_cons.mp hR with eq | hr
        · exact False.elim (notQueried (eq ▸ hi))
        · exact List.mem_append.mpr (Or.inr hr)
    · intro hs i hi
      rcases List.mem_append.mp (hs hi) with hl | hr
      · exact List.mem_append.mpr (Or.inl hl)
      · exact List.mem_append.mpr (Or.inr (by simp [hr]))
  simp [h]

theorem query_outside [DecidableEq V] (edge query : List V) (v : V)
    (inQuery : v ∈ query) (notInEdge : v ∉ edge) : moment edge query = 0 := by
  unfold moment alternating
  apply Eq.trans _ (sum_zero (cells edge))
  apply sum_congr_on
  intro c hc
  have h : ¬ query ⊆ c := fun h => notInEdge ((mem_cells.mp hc).subset (h inQuery))
  simp [h]

private theorem nodup_length_le_of_subset [DecidableEq V] {xs ys : List V}
    (hd : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, tail⟩ := List.nodup_cons.mp hd
    have inYs : x ∈ ys := hs (by simp)
    obtain ⟨left, right, rfl⟩ := List.append_of_mem inYs
    have sub : xs ⊆ left ++ right := by
      intro z hz
      have hzx : z ≠ x := fun h => hx (h ▸ hz)
      have hz' : z ∈ left ++ x :: right := hs (by simp [hz])
      simpa [List.mem_append, hzx] using hz'
    have bound := ih tail sub
    simp only [List.length_append, List.length_cons] at bound ⊢
    omega

private theorem witness_not_subset [DecidableEq V] (xs ys : List V) (h : ¬ xs ⊆ ys) :
    ∃ v, v ∈ xs ∧ v ∉ ys := by
  induction xs with
  | nil => exact False.elim (h (by simp))
  | cons v xs ih =>
    by_cases hv : v ∈ ys
    · have noTail : ¬ xs ⊆ ys := by
        intro sub
        apply h
        intro z hz
        rcases List.mem_cons.mp hz with h | h
        · exact h ▸ hv
        · exact sub h
      obtain ⟨z, hz, outside⟩ := ih noTail
      exact ⟨z, by simp [hz], outside⟩
    · exact ⟨v, by simp, hv⟩

private theorem sum_one_cell [DecidableEq A] (xs : List A) (target : A) (d : Int)
    (hd : xs.Nodup) (present : target ∈ xs) :
    sumOn xs (fun x => if x = target then d else 0) = d := by
  induction xs with
  | nil => simp at present
  | cons x xs ih =>
    obtain ⟨hx, tail⟩ := List.nodup_cons.mp hd
    change (if x = target then d else 0) +
      sumOn xs (fun x => if x = target then d else 0) = d
    by_cases he : x = target
    · subst x
      have h : sumOn xs (fun x => if x = target then d else 0) = 0 := by
        apply Eq.trans _ (sum_zero xs)
        apply sum_congr_on
        intro z hz
        have ne : z ≠ target := fun h => hx (h ▸ hz)
        simp [ne]
      simp [h]
    · have h := ih tail ((List.mem_cons.mp present).resolve_left (Ne.symm he))
      simp [he, h]

theorem full_edge [DecidableEq V] (edge : List V) (hd : edge.Nodup) :
    moment edge edge = (-1 : Int)^edge.length := by
  unfold moment alternating
  calc
    _ = sumOn (cells edge) (fun c => if c = edge then (-1 : Int)^edge.length else 0) := by
      apply sum_congr_on
      intro c hc
      by_cases he : c = edge
      · subst c; simp
      · have h : ¬ edge ⊆ c := fun hs =>
          he ((mem_cells.mp hc).eq_of_length_le (nodup_length_le_of_subset hd hs))
        simp [he, h]
    _ = _ := sum_one_cell _ edge _ (cells_nodup hd) (mem_cells.mpr (List.Sublist.refl _))

/-- Closed form for every query, including differently ordered or repeated tags. -/
theorem containment_identity [DecidableEq V] (edge query : List V) (hd : edge.Nodup) :
    moment edge query =
      if edge ⊆ query ∧ query ⊆ edge then (-1 : Int)^edge.length else 0 := by
  by_cases left : edge ⊆ query
  · by_cases right : query ⊆ edge
    · have same (c : List V) : (query ⊆ c) ↔ edge ⊆ c :=
        ⟨fun h => List.Subset.trans left h, fun h => List.Subset.trans right h⟩
      rw [if_pos ⟨left, right⟩]
      simpa only [moment, same] using full_edge edge hd
    · obtain ⟨v, hq, he⟩ := witness_not_subset query edge right
      simp [right, query_outside edge query v hq he]
  · obtain ⟨v, he, hq⟩ := witness_not_subset edge query left
    simp [left, missing_edge_vertex edge query v he hq]

theorem lower_degree [DecidableEq V] (edge query : List V) (hd : edge.Nodup)
    (smaller : query.length < edge.length) : moment edge query = 0 := by
  have h : ¬ edge ⊆ query := fun sub => (Nat.not_le_of_gt smaller) (nodup_length_le_of_subset hd sub)
  simp [containment_identity edge query hd, h]

theorem total_mass_zero [DecidableEq V] (edge : List V) (hd : edge.Nodup)
    (nonempty : 0 < edge.length) : moment edge [] = 0 :=
  lower_degree edge [] hd nonempty

/-- An atom table may contain repeated cells; their signed masses add.
This is also a convenient representation of a base law plus perturbations. -/
def histogramMoment [DecidableEq V] (atoms : List (List V × Int)) (query : List V) : Int :=
  sumOn atoms (fun atom => if query ⊆ atom.1 then atom.2 else 0)

def cubeAtoms (edge : List V) (d : Int) : List (List V × Int) :=
  (cells edge).map (fun c => (c, d * (-1 : Int)^c.length))

private theorem sum_scale (xs : List A) (d : Int) (f : A → Int) :
    sumOn xs (fun x => d * f x) = d * sumOn xs f := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    change d * f a + sumOn xs (fun x => d * f x) = d * (f a + sumOn xs f)
    rw [ih, Int.mul_add]

theorem histogram_cube [DecidableEq V] (edge query : List V) (d : Int) :
    histogramMoment (cubeAtoms edge d) query = d * moment edge query := by
  unfold histogramMoment cubeAtoms moment alternating
  rw [← sum_scale]
  change (((cells edge).map _).map _).sum = _
  simp only [List.map_map, Function.comp_def]
  apply sum_congr_on (cells edge)
  intro c _
  by_cases h : query ⊆ c <;> simp [h]

def addCubes (base : List (List V × Int)) : List (List V × Int) → List (List V × Int)
  | [] => base
  | (edge, d) :: rest => cubeAtoms edge d ++ addCubes base rest

/-- Exact action of an arbitrary finite superposition on every containment
moment. Only cubes whose full vertex set equals the query contribute. -/
theorem histogram_superposition [DecidableEq V] (base specs : List (List V × Int))
    (query : List V) (hd : ∀ s ∈ specs, s.1.Nodup) :
    histogramMoment (addCubes base specs) query =
      histogramMoment base query + sumOn specs (fun s =>
        if s.1 ⊆ query ∧ query ⊆ s.1 then s.2 * (-1 : Int)^s.1.length else 0) := by
  induction specs with
  | nil => simp [addCubes, sumOn]
  | cons s rest ih =>
    obtain ⟨edge,d⟩ := s
    have hr := ih (fun s hs => hd s (by simp [hs]))
    have he : edge.Nodup := hd (edge,d) (by simp)
    change sumOn (cubeAtoms edge d ++ addCubes base rest) _ =
      histogramMoment base query + (_ + sumOn rest _)
    rw [sum_append]
    change histogramMoment (cubeAtoms edge d) query + histogramMoment (addCubes base rest) query = _
    rw [histogram_cube, containment_identity edge query he, hr]
    by_cases h : edge ⊆ query ∧ query ⊆ edge <;> simp [h] <;> omega

theorem superposition_preserves_lower [DecidableEq V] (base specs : List (List V × Int))
    (query : List V) (hd : ∀ s ∈ specs, s.1.Nodup)
    (lower : ∀ s ∈ specs, query.length < s.1.length) :
    histogramMoment (addCubes base specs) query = histogramMoment base query := by
  rw [histogram_superposition base specs query hd]
  have z : sumOn specs (fun s =>
      if s.1 ⊆ query ∧ query ⊆ s.1 then s.2 * (-1 : Int)^s.1.length else 0) = 0 := by
    apply Eq.trans _ (sum_zero specs)
    apply sum_congr_on
    intro s hs
    have h : ¬ s.1 ⊆ query := fun sub =>
      (Nat.not_le_of_gt (lower s hs)) (nodup_length_le_of_subset (hd s hs) sub)
    simp [h]
  rw [z, Int.add_zero]

end Screening.MomentCube

/- Source module: Screening.CellLift -/

/-! Uniform lifting of finite rational cell masses onto actual words.
If c has n words and assigned probability a(c)/D, each of those words
gets numerator a(c)*(K/n) over the common denominator D*K. The file
constructs a suitable positive common multiple K, and separates assumptions
on the prescribed cell masses from the derived bounds on individual words.
A list of distinct words represents a physical support; all identities also
hold for an enumerated population with repeated positions. -/

namespace Screening.CellLift

def sumNat (xs : List A) (f : A → Nat) : Nat := (xs.map f).sum

def fiberSize [DecidableEq C] (words : List W) (tag : W → C) (c : C) : Nat :=
  (words.filter (fun w => decide (tag w = c))).length

def cellMass [DecidableEq C] (words : List W) (tag : W → C)
    (weight : W → Nat) (c : C) : Nat :=
  sumNat words (fun w => if tag w = c then weight w else 0)

def liftNumerator [DecidableEq C] (words : List W) (tag : W → C)
    (a : C → Nat) (K : Nat) (w : W) : Nat :=
  a (tag w) * (K / fiberSize words tag (tag w))

def commonScale (size : C → Nat) : List C → Nat
  | [] => 1
  | c :: rest => size c * commonScale size rest

theorem scale_positive (size : C → Nat) (labels : List C)
    (occupied : ∀ c ∈ labels, 0 < size c) : 0 < commonScale size labels := by
  induction labels with
  | nil => exact Nat.zero_lt_one
  | cons c rest ih =>
    exact Nat.mul_pos (occupied c (by simp)) (ih (fun z hz => occupied z (by simp [hz])))

theorem size_divides_scale (size : C → Nat) (labels : List C) (c : C) (hc : c ∈ labels) :
    size c ∣ commonScale size labels := by
  induction labels with
  | nil => simp at hc
  | cons x rest ih =>
    rcases List.mem_cons.mp hc with h | h
    · subst x; exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (ih h) (Nat.dvd_mul_left _ _)

private theorem constant_fiber_mass [DecidableEq C] (words : List W) (tag : W → C)
    (g : C → Nat) (c : C) :
    cellMass words tag (fun w => g (tag w)) c = fiberSize words tag c * g c := by
  induction words with
  | nil => simp [fiberSize, cellMass, sumNat]
  | cons w ws ih =>
    by_cases h : tag w = c <;>
      simp [fiberSize, List.filter_cons, cellMass, sumNat, h, Nat.succ_mul] at ih ⊢ <;> omega

/-- The exact total prescribed for one cell, as a numerator at scale D*K. -/
theorem recover_cell [DecidableEq C] (words : List W) (tag : W → C)
    (a : C → Nat) (K : Nat) (c : C) (divides : fiberSize words tag c ∣ K) :
    cellMass words tag (liftNumerator words tag a K) c = K * a c := by
  unfold liftNumerator
  rw [constant_fiber_mass words tag (fun s => a s * (K / fiberSize words tag s)) c]
  calc
    _ = ((K / fiberSize words tag c) * fiberSize words tag c) * a c := by ac_rfl
    _ = K * a c := by rw [Nat.div_mul_cancel divides]

theorem uniform_within_cell [DecidableEq C] (words : List W) (tag : W → C)
    (a : C → Nat) (K : Nat) (x y : W) (same : tag x = tag y) :
    liftNumerator words tag a K x = liftNumerator words tag a K y := by
  simp [liftNumerator, same]

private theorem sum_add (xs : List A) (f g : A → Nat) :
    sumNat xs (fun x => f x + g x) = sumNat xs f + sumNat xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x + g x + sumNat xs (fun x => f x + g x) =
      (f x + sumNat xs f) + (g x + sumNat xs g)
    omega

private theorem sum_empty_terms (xs : List A) : sumNat xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change 0 + sumNat xs (fun _ => 0) = 0; omega

private theorem sum_congr (xs : List A) {f g : A → Nat} (h : ∀ x ∈ xs, f x = g x) :
    sumNat xs f = sumNat xs g := congrArg List.sum (List.map_congr_left h)

private theorem sum_point [DecidableEq C] (labels : List C) (c : C) (d : Nat)
    (hd : labels.Nodup) (inLabels : c ∈ labels) :
    sumNat labels (fun z => if c = z then d else 0) = d := by
  induction labels with
  | nil => simp at inLabels
  | cons v rest ih =>
    obtain ⟨hv, hrest⟩ := List.nodup_cons.mp hd
    change (if c = v then d else 0) + sumNat rest (fun z => if c = z then d else 0) = d
    by_cases h : c = v
    · subst v
      have z : sumNat rest (fun z => if c = z then d else 0) = 0 := by
        apply Eq.trans _ (sum_empty_terms rest)
        apply sum_congr
        intro z hz
        have ne : c ≠ z := fun he => hv (he ▸ hz)
        simp [ne]
      simp [z]
    · simp [h, ih hrest ((List.mem_cons.mp inLabels).resolve_left h)]

/-- Every enumerated word contributes to exactly one of the listed fibers. -/
theorem partition_total [DecidableEq C] (words : List W) (labels : List C)
    (tag : W → C) (weight : W → Nat) (unique : labels.Nodup)
    (complete : ∀ w ∈ words, tag w ∈ labels) :
    sumNat labels (cellMass words tag weight) = sumNat words weight := by
  induction words with
  | nil =>
    change sumNat labels (fun _ => 0) = 0
    exact sum_empty_terms labels
  | cons w ws ih =>
    change sumNat labels (fun c => (if tag w = c then weight w else 0) +
      cellMass ws tag weight c) = weight w + sumNat ws weight
    rw [sum_add, sum_point labels (tag w) (weight w) unique (complete w (by simp))]
    rw [ih (fun x hx => complete x (by simp [hx]))]

private theorem sum_scale (xs : List A) (c : Nat) (g : A → Nat) :
    sumNat xs (fun x => c * g x) = c * sumNat xs g := by
  induction xs with
  | nil => simp [sumNat]
  | cons x xs ih =>
    change c * g x + sumNat xs (fun x => c * g x) = c * (g x + sumNat xs g)
    rw [ih, Nat.mul_add]

/-- If prescribed numerators sum to D, the word numerators sum to K*D. -/
theorem lift_normalized [DecidableEq C] (words : List W) (labels : List C)
    (tag : W → C) (a : C → Nat) (K D : Nat) (unique : labels.Nodup)
    (complete : ∀ w ∈ words, tag w ∈ labels)
    (divides : ∀ c ∈ labels, fiberSize words tag c ∣ K)
    (normalized : sumNat labels a = D) :
    sumNat words (liftNumerator words tag a K) = K * D := by
  rw [← partition_total words labels tag _ unique complete]
  calc
    _ = sumNat labels (fun c => K * a c) := by
      apply sum_congr
      exact fun c hc => recover_cell words tag a K c (divides c hc)
    _ = _ := by rw [sum_scale, normalized]

/-- Density relative to uniform on the L listed words. With n words in
cell c, the assumed bounds express lo/b ≤ (a(c)/D)/(n/L) ≤ hi/b.
The conclusions express the same bounds for its individual words with
probability liftNumerator/(D*K). Cross-multiplication is exact; probability
interpretation uses positive denominators b, D, K and a nonempty population. -/
theorem transfer_density [DecidableEq C] (words : List W) (tag : W → C)
    (a : C → Nat) (K D b lo hi : Nat) (w : W)
    (divides : fiberSize words tag (tag w) ∣ K)
    (lower : lo * D * fiberSize words tag (tag w) ≤ b * words.length * a (tag w))
    (upper : b * words.length * a (tag w) ≤ hi * D * fiberSize words tag (tag w)) :
    lo * (D * K) ≤ b * words.length * liftNumerator words tag a K w ∧
    b * words.length * liftNumerator words tag a K w ≤ hi * (D * K) := by
  let n := fiberSize words tag (tag w)
  have eqK : (K / n) * n = K := Nat.div_mul_cancel divides
  have rescale (k : Nat) : (k * D * n) * (K/n) = k * (D*K) := by
    calc
      _ = k * (D * ((K/n)*n)) := by ac_rfl
      _ = _ := by rw [eqK]
  change lo * (D*K) ≤ b * words.length * (a (tag w) * (K/n)) ∧
    b * words.length * (a (tag w) * (K/n)) ≤ hi * (D*K)
  rw [← rescale lo, ← rescale hi, ← Nat.mul_assoc (b * words.length)]
  exact ⟨Nat.mul_le_mul_right (K/n) lower, Nat.mul_le_mul_right (K/n) upper⟩

/-- Construct a physical law with all prescribed rational cell probabilities,
unit total mass, and both density bounds. For a relative perturbation u/v,
take b=v, lo=v-u, hi=v+u. The coarse density estimates are hypotheses. -/
theorem lift_rational_cell_law [DecidableEq C] (words : List W) (labels : List C)
    (tag : W → C) (a : C → Nat) (D b lo hi : Nat)
    (positiveD : 0 < D) (positiveB : 0 < b) (unique : labels.Nodup)
    (complete : ∀ w ∈ words, tag w ∈ labels)
    (occupied : ∀ c ∈ labels, 0 < fiberSize words tag c)
    (normalized : sumNat labels a = D)
    (bounds : ∀ c ∈ labels,
      lo * D * fiberSize words tag c ≤ b * words.length * a c ∧
      b * words.length * a c ≤ hi * D * fiberSize words tag c) :
    ∃ K : Nat, ∃ weight : W → Nat,
      0 < K ∧ 0 < b * (D*K) ∧ sumNat words weight = D*K ∧
      (∀ c ∈ labels, cellMass words tag weight c = K * a c) ∧
      (∀ x y, tag x = tag y → weight x = weight y) ∧
      (∀ w ∈ words, lo * (D*K) ≤ b * words.length * weight w ∧
        b * words.length * weight w ≤ hi * (D*K)) := by
  let K := commonScale (fiberSize words tag) labels
  have positiveK : 0 < K := scale_positive _ _ occupied
  have divides : ∀ c ∈ labels, fiberSize words tag c ∣ K :=
    fun c hc => size_divides_scale _ labels c hc
  refine ⟨K, liftNumerator words tag a K, positiveK,
    Nat.mul_pos positiveB (Nat.mul_pos positiveD positiveK), ?_, ?_, ?_, ?_⟩
  · exact (lift_normalized words labels tag a K D unique complete divides normalized).trans
      (Nat.mul_comm K D)
  · exact fun c hc => recover_cell words tag a K c (divides c hc)
  · exact fun x y => uniform_within_cell words tag a K x y
  · intro w hw
    have inLabels := complete w hw
    obtain ⟨hlo, hhi⟩ := bounds (tag w) inLabels
    exact transfer_density words tag a K D b lo hi w (divides (tag w) inLabels) hlo hhi

end Screening.CellLift

/- Source module: Screening.CostMoments -/

/-! Operational first-hit cost and its finite signed containment expansion. -/

namespace Screening.CostMoments

open Screening.LargestHits (maxRank MomentRow weightedCentered)
open Screening.ScreeningCost (scan survives properPrefixes)

private def total (xs : List α) (term : α → Int) : Int :=
  (xs.map term).sum

@[simp] private theorem total_nil (f : α → Int) : total [] f = 0 := rfl

@[simp] private theorem total_cons (x : α) (xs : List α) (f : α → Int) :
    total (x :: xs) f = f x + total xs f := rfl

private theorem total_map (xs : List α) (g : α → β) (f : β → Int) :
    total (xs.map g) f = total xs (fun x => f (g x)) := by
  rw [total, List.map_map]
  rfl

private theorem total_append (xs ys : List α) (f : α → Int) :
    total (xs ++ ys) f = total xs f + total ys f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, total_cons, ih, Int.add_assoc]

private theorem total_zero (xs : List α) : total xs (fun _ => 0) = 0 := by
  induction xs <;> simp_all

private theorem total_congr (xs : List α) (f g : α → Int) (eq : ∀ x ∈ xs, f x = g x) :
    total xs f = total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [total_cons, total_cons, eq x (by simp)]
    rw [ih (fun y inside => eq y (by simp [inside]))]

private theorem total_add (xs : List α) (f g : α → Int) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [total_cons, ih]
    omega

private theorem total_sub (xs : List α) (f g : α → Int) :
    total xs (fun x => f x - g x) = total xs f - total xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [total_cons, ih]
    omega

private theorem total_neg (xs : List α) (f : α → Int) :
    total xs (fun x => -f x) = -total xs f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [total_cons, ih]
    omega

private theorem total_mul_left (xs : List α) (c : Int) (f : α → Int) :
    total xs (fun x => c * f x) = c * total xs f := by
  induction xs <;> simp_all [Int.mul_add]

private theorem total_mul_right (xs : List α) (c : Int) (f : α → Int) :
    total xs (fun x => f x * c) = total xs f * c := by
  induction xs <;> simp_all [Int.add_mul]

private theorem total_commute (xs : List α) (ys : List β) (f : α → β → Int) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [total_zero]
  | cons x xs ih => simp only [total_cons, total_add, ih]

private def indicator (b : Bool) : Int := if b then 1 else 0

/-- All subsequences with the alternating inclusion–exclusion sign. With a
duplicate-free menu, every subset is represented once in menu order. -/
def subsetTerms : List Nat → List (List Nat × Int)
  | [] => [([], 1)]
  | i :: rest => subsetTerms rest ++ (subsetTerms rest).map (fun term => (i :: term.1, -term.2))

theorem subset_term_sublist {menu : List Nat} {term : List Nat × Int}
    (member : term ∈ subsetTerms menu) : term.1.Sublist menu := by
  induction menu generalizing term with
  | nil =>
    simp [subsetTerms] at member
    subst term
    exact .slnil
  | cons j rest ih =>
    rw [subsetTerms, List.mem_append] at member
    rcases member with kept | extended
    · exact .cons j (ih kept)
    · obtain ⟨earlier, member, equal⟩ := List.mem_map.mp extended
      subst term
      exact .cons₂ j (ih member)

theorem sublist_has_subset_term {hits menu : List Nat} (part : hits.Sublist menu) :
    ∃ sign : Int, (hits, sign) ∈ subsetTerms menu := by
  induction part with
  | slnil => exact ⟨1, by simp [subsetTerms]⟩
  | cons i part ih =>
    obtain ⟨sign, included⟩ := ih
    exact ⟨sign, by simp [subsetTerms, included]⟩
  | cons₂ i part ih =>
    obtain ⟨sign, included⟩ := ih
    exact ⟨-sign, by
      rw [subsetTerms, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨(_, sign), included, rfl⟩)⟩

private theorem term_subset {menu : List Nat} {term : List Nat × Int}
    (member : term ∈ subsetTerms menu) {i : Nat} (part : i ∈ term.1) : i ∈ menu :=
  (subset_term_sublist member).subset part

theorem subset_terms_unique {menu : List Nat} (unique : menu.Nodup) :
    ((subsetTerms menu).map Prod.fst).Nodup := by
  induction menu with
  | nil => simp [subsetTerms]
  | cons i rest ih =>
    obtain ⟨notInTail, tailUnique⟩ := List.nodup_cons.mp unique
    have tail := ih tailUnique
    have decompose :
        ((subsetTerms (i :: rest)).map Prod.fst) =
          ((subsetTerms rest).map Prod.fst) ++ (((subsetTerms rest).map Prod.fst).map (i :: ·)) := by
      simp [subsetTerms, List.map_map, Function.comp_def]
    rw [decompose]
    unfold List.Nodup
    rw [List.pairwise_append]
    refine ⟨tail, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      exact tail.imp (fun different equal => different (List.cons.inj equal).2)
    · intro a absent b included equal
      obtain ⟨term, present, rfl⟩ := List.mem_map.mp absent
      obtain ⟨ys, _, rfl⟩ := List.mem_map.mp included
      have hit : i ∈ term.1 := by rw [equal]; simp
      exact notInTail (term_subset present hit)

theorem subset_term_sign {menu : List Nat} {term : List Nat × Int}
    (member : term ∈ subsetTerms menu) : term.2 = (-1 : Int) ^ term.1.length := by
  induction menu generalizing term with
  | nil => simp [subsetTerms] at member; subst term; simp
  | cons i rest ih =>
    rw [subsetTerms, List.mem_append] at member
    rcases member with kept | extended
    · exact ih kept
    · obtain ⟨earlier, before, equal⟩ := List.mem_map.mp extended
      subst term
      simpa [Int.pow_succ] using congrArg (fun k : Int => -k) (ih before)

private theorem inclusion_exclusion (menu : List Nat) (hit : Nat → Bool) :
    total (subsetTerms menu) (fun term => term.2 * indicator (term.1.all hit)) =
      indicator (!(menu.any hit)) := by
  induction menu with
  | nil => simp [subsetTerms, indicator]
  | cons i rest ih =>
    rw [subsetTerms, total_append, total_map]
    cases hi : hit i
    · simp [hi, indicator, total_zero]
      simpa [indicator] using ih
    · simp only [List.all_cons, hi, Bool.true_and, Int.neg_mul, total_neg, List.any_cons,
        Bool.true_or, Bool.not_true, indicator, Bool.false_eq_true, if_false]
      omega

/-- The actual one-based position of a label, or length plus one when absent. -/
def probeRank (order : List Nat) (i : Nat) : Nat := order.idxOf i + 1

/-- Extend the true ranks by the identity off the finite menu. -/
def extendedProbeRank (order : List Nat) (i : Nat) : Nat :=
  if i ∈ order then probeRank order i else i

theorem extendedProbeRank_of_mem {order : List Nat} {i : Nat} (inside : i ∈ order) :
    extendedProbeRank order i = probeRank order i := by
  simp [extendedProbeRank, inside]

theorem extendedProbeRank_displacement (order : List Nat) (w : Nat)
    (band : ∀ i ∈ order, i ≤ probeRank order i + w ∧ probeRank order i ≤ i + w) :
    Screening.LargestHits.Displacement (extendedProbeRank order) w := by
  intro i
  by_cases inside : i ∈ order
  · simpa [extendedProbeRank, inside] using band i inside
  · simp [extendedProbeRank, inside]

theorem mem_take_iff_probeRank {order : List Nat} {i t : Nat} (within : t ≤ order.length) :
    i ∈ order.take t ↔ probeRank order i ≤ t := by
  induction order generalizing t with
  | nil =>
    have zero : t = 0 := by simpa using within
    simp [zero, probeRank]
  | cons j rest ih =>
    cases t with
    | zero => simp [probeRank]
    | succ t =>
      by_cases equal : i = j
      · subst i
        simp [probeRank]
      · have smaller : t ≤ rest.length := by simp at within; omega
        have notEq : j ≠ i := Ne.symm equal
        have different : (j == i) = false := by simp [notEq]
        simpa [probeRank, List.idxOf_cons, equal, different, Nat.add_assoc] using ih smaller

private theorem maxRank_le_iff (rank : Nat → Nat) (hits : List Nat) (time : Nat) :
    maxRank rank hits ≤ time ↔ ∀ i ∈ hits, rank i ≤ time := by
  induction hits with
  | nil => simp [maxRank]
  | cons i rest ih => simp [maxRank, Nat.max_le, ih]

private theorem all_prefix_hits (hit : Nat → Bool) (rank : Nat → Nat)
    (hits : List Nat) (time : Nat) :
    hits.all (fun i => hit i && decide (rank i ≤ time)) =
      (hits.all hit && decide (maxRank rank hits ≤ time)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, maxRank_le_iff]
  exact ⟨fun all => ⟨fun i m => (all i m).1, fun i m => (all i m).2⟩,
    fun both i m => ⟨both.1 i m, both.2 i m⟩⟩

private theorem survives_eq_not_any (hit : Nat → Bool) (order : List Nat) :
    survives hit order = !(order.any hit) := by
  induction order with
  | nil => rfl
  | cons i rest ih =>
    cases hi : hit i <;> simp [survives, hi] at ih ⊢ <;> assumption

private theorem any_prefix_hits {menu order : List Nat} (complete : order.Perm menu)
    (hit : Nat → Bool) {time : Nat} (within : time ≤ order.length) :
    menu.any (fun i => hit i && decide (probeRank order i ≤ time)) =
      (order.take time).any hit := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, _, hits, rank⟩
    exact ⟨i, (mem_take_iff_probeRank within).mpr rank, hits⟩
  · rintro ⟨i, inside, hits⟩
    exact ⟨i, complete.mem_iff.mp (List.mem_of_mem_take inside), hits,
      (mem_take_iff_probeRank within).mp inside⟩

private theorem indicator_and (a b : Bool) : indicator (a && b) = indicator a * indicator b := by
  cases a <;> cases b <;> decide

private theorem indicator_nat (b : Bool) : ((b.toNat : Nat) : Int) = indicator b := by
  cases b <;> rfl

private theorem prefix_expansion {menu order : List Nat} (complete : order.Perm menu)
    (hit : Nat → Bool) {time : Nat} (within : time ≤ order.length) :
    indicator (survives hit (order.take time)) =
      total (subsetTerms menu) (fun term => term.2 * indicator (term.1.all hit) *
        indicator (decide (maxRank (probeRank order) term.1 ≤ time))) := by
  rw [survives_eq_not_any, ← any_prefix_hits complete hit within, ← inclusion_exclusion]
  apply total_congr
  intro term _
  rw [all_prefix_hits, indicator_and, Int.mul_assoc]

private theorem indicator_count (n k : Nat) :
    total (List.range n) (fun t => indicator (decide (k ≤ t))) = ((n - k : Nat) : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, total_append, ih, total_cons, total_nil, Int.add_zero]
    by_cases passed : k ≤ n
    · simp [indicator, passed]
      omega
    · simp [indicator, passed]
      omega

private theorem coe_nat_total (xs : List α) (f : α → Nat) :
    (Screening.ScreeningCost.total xs f : Int) = total xs (fun x => (f x : Int)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ((f x + Screening.ScreeningCost.total xs f : Nat) : Int) =
      (f x : Int) + total xs (fun y => (f y : Int))
    rw [Int.ofNat_add, ih]

/-- The unit-cost scan of one outcome equals its signed completion-time sum. -/
theorem scan_eq_completed_subsets {menu order : List Nat} (complete : order.Perm menu)
    (hit : Nat → Bool) :
    (scan hit 0 order : Int) =
      total (subsetTerms menu) (fun term => term.2 * indicator (term.1.all hit) *
        ((order.length - maxRank (probeRank order) term.1 : Nat) : Int)) := by
  rw [Screening.ScreeningCost.scan_eq_prefix_survivals]
  simp only [Nat.zero_mul, Nat.add_zero, coe_nat_total, properPrefixes, total_map, indicator_nat]
  apply Eq.trans (b := total (List.range order.length) (fun time =>
    total (subsetTerms menu) (fun term => term.2 * indicator (term.1.all hit) *
      indicator (decide (maxRank (probeRank order) term.1 ≤ time)))))
  · apply total_congr
    intro time inside
    exact prefix_expansion complete hit (Nat.le_of_lt (List.mem_range.mp inside))
  · rw [total_commute]
    apply total_congr
    intro term _
    rw [total_mul_left, indicator_count]

/-- The total scan cost of a finite list of weighted outcomes. Integer masses
allow both scaled probability laws and signed differences between laws. -/
def finiteCost (law : List (X × Int)) (hit : X → Nat → Bool)
    (fallback : Nat) (order : List Nat) : Int :=
  total law (fun x => x.2 * (scan (hit x.1) fallback order : Int))

/-- The total weight of outcomes containing each hit in the requested subset. -/
def containmentMass (law : List (X × Int)) (hit : X → Nat → Bool)
    (hits : List Nat) : Int :=
  total law (fun x => x.2 * indicator (hits.all (hit x.1)))

/-- The finite weighted cost at zero fallback is the signed sum of the
containment masses times the number of prefixes completing each subset. -/
theorem finite_cost_eq_completed_subsets {menu order : List Nat} (complete : order.Perm menu)
    (law : List (X × Int)) (hit : X → Nat → Bool) :
    finiteCost law hit 0 order =
      total (subsetTerms menu) (fun term => term.2 * containmentMass law hit term.1 *
        ((order.length - maxRank (probeRank order) term.1 : Nat) : Int)) := by
  unfold finiteCost
  apply Eq.trans (b := total law (fun atom => total (subsetTerms menu) (fun term =>
    term.2 * (atom.2 * indicator (term.1.all (hit atom.1))) *
      ((order.length - maxRank (probeRank order) term.1 : Nat) : Int))))
  · apply total_congr
    intro atom _
    rw [scan_eq_completed_subsets complete, ← total_mul_left]
    apply total_congr
    intro term _
    ac_rfl
  · rw [total_commute]
    apply total_congr
    intro term _
    rw [total_mul_right, total_mul_left]
    rfl

private theorem survives_perm {order menu : List Nat} (complete : order.Perm menu)
    (hit : Nat → Bool) : survives hit order = survives hit menu := by
  apply Bool.eq_iff_iff.mpr
  unfold survives
  simp only [List.all_eq_true]
  exact ⟨fun all i inside => all i (complete.mem_iff.mpr inside),
    fun all i inside => all i (complete.mem_iff.mp inside)⟩

private theorem finite_cost_fallback {menu order : List Nat} (complete : order.Perm menu)
    (law : List (X × Int)) (hit : X → Nat → Bool) (fallback : Nat) :
    finiteCost law hit fallback order = finiteCost law hit 0 order +
      total law (fun atom => atom.2 * ((fallback * (survives (hit atom.1) menu).toNat : Nat) : Int)) := by
  unfold finiteCost
  rw [← total_add]
  apply total_congr
  intro atom _
  rw [Screening.ScreeningCost.scan_eq_prefix_survivals (hit atom.1) fallback order,
    Screening.ScreeningCost.scan_eq_prefix_survivals (hit atom.1) 0 order]
  simp only [Nat.zero_mul, Nat.add_zero, Int.ofNat_add, Int.mul_add,
    survives_perm complete (hit atom.1)]

private theorem subset_completion_le {menu order : List Nat} (complete : order.Perm menu)
    {term : List Nat × Int} (included : term ∈ subsetTerms menu) :
    maxRank (probeRank order) term.1 ≤ order.length := by
  apply (maxRank_le_iff _ _ _).mpr
  intro i member
  have inside := complete.mem_iff.mpr (term_subset included member)
  have index := List.idxOf_lt_length inside
  unfold probeRank
  omega

/-- A centered operational cost difference uses ((-1)^{|S|+1}) times
containment mass, multiplied by the change in maximum rank. Fallback cancels
because both orders test the same menu. -/
theorem finite_cost_centered {menu order base : List Nat}
    (complete : order.Perm menu) (baseComplete : base.Perm menu)
    (law : List (X × Int)) (hit : X → Nat → Bool) (fallback : Nat) :
    finiteCost law hit fallback order - finiteCost law hit fallback base =
      total (subsetTerms menu) (fun term => (-term.2 * containmentMass law hit term.1) *
        ((maxRank (probeRank order) term.1 : Int) - (maxRank (probeRank base) term.1 : Int))) := by
  rw [finite_cost_fallback complete, finite_cost_fallback baseComplete]
  have cancel (a b c : Int) : (a + c) - (b + c) = a - b := by omega
  rw [cancel]
  rw [finite_cost_eq_completed_subsets complete, finite_cost_eq_completed_subsets baseComplete,
    ← total_sub]
  apply total_congr
  intro term included
  rw [Int.ofNat_sub (subset_completion_le complete included),
    Int.ofNat_sub (subset_completion_le baseComplete included), complete.length_eq,
    baseComplete.length_eq, ← Int.mul_sub]
  have reverse (m r b : Int) : (m - r) - (m - b) = -(r - b) := by omega
  rw [reverse, Int.mul_neg, Int.neg_mul, Int.neg_mul]

private theorem probeRank_range' {start count i : Nat}
    (inside : i ∈ List.range' start count) :
    probeRank (List.range' start count) i = i - start + 1 := by
  induction count generalizing start with
  | zero => simp at inside
  | succ count ih =>
    rw [List.range'_succ] at inside ⊢
    by_cases equal : i = start
    · subst i
      simp [probeRank]
    · have tail : i ∈ List.range' (start + 1) count := by simpa [equal] using inside
      have later : start + 1 ≤ i := by
        obtain ⟨offset, _, eq⟩ := List.mem_range'.mp tail
        omega
      have tailRank := ih tail
      have different : (start == i) = false := by simp [Ne.symm equal]
      simp only [probeRank, List.idxOf_cons, different, Bool.cond_false] at tailRank ⊢
      omega

/-- The increasing menu on labels 1 through `m` realizes the identity rank. -/
theorem natural_probeRank {m i : Nat} (inside : i ∈ List.range' 1 m) :
    probeRank (List.range' 1 m) i = i := by
  have position := probeRank_range' inside
  obtain ⟨offset, _, equal⟩ := List.mem_range'.mp inside
  omega

private theorem maxRank_congr (hits : List Nat) (r s : Nat → Nat)
    (same : ∀ i ∈ hits, r i = s i) : maxRank r hits = maxRank s hits := by
  induction hits with
  | nil => rfl
  | cons i rest ih =>
    simp only [maxRank]
    rw [same i (by simp), ih (fun j inside => same j (by simp [inside]))]

/-- Assign each menu subset its signed containment moment deviation. -/
def deviationRows (menu : List Nat) (deviation : List Nat → Int) : List MomentRow :=
  (subsetTerms menu).map (fun term => ⟨term.1, -term.2 * deviation term.1⟩)

/-- Relative to any reference law, the difference of centered operational
costs equals the weighted centered rank expression used in the surrogate proof. -/
theorem centered_cost_deviation_eq_rows {menu order : List Nat} {m : Nat}
    (complete : order.Perm menu) (baseComplete : (List.range' 1 m).Perm menu)
    (law : List (X × Int)) (hit : X → Nat → Bool)
    (reference : List (Y × Int)) (refHit : Y → Nat → Bool) (fallback : Nat) :
    ((finiteCost law hit fallback order - finiteCost law hit fallback (List.range' 1 m)) -
        (finiteCost reference refHit fallback order -
          finiteCost reference refHit fallback (List.range' 1 m))) =
      ((deviationRows menu (fun s => containmentMass law hit s -
        containmentMass reference refHit s)).map (weightedCentered (maxRank (probeRank order)))).sum := by
  rw [finite_cost_centered complete baseComplete, finite_cost_centered complete baseComplete,
    ← total_sub]
  change _ = total ((subsetTerms menu).map _) _
  rw [total_map]
  apply total_congr
  intro term included
  have baseRanks : maxRank (probeRank (List.range' 1 m)) term.1 = maxRank id term.1 := by
    apply maxRank_congr
    intro i inside
    exact natural_probeRank (baseComplete.mem_iff.mpr (term_subset included inside))
  simp only [weightedCentered, baseRanks]
  rw [← Int.sub_mul, ← Int.mul_sub]

/-- A finite weighted input law has at most `h` hits at each listed outcome. -/
def HasHitCap (menu : List Nat) (h : Nat) (law : List (X × Int))
    (hit : X → Nat → Bool) : Prop :=
  ∀ atom ∈ law, (menu.filter (hit atom.1)).length ≤ h

theorem containmentMass_zero_of_hitCap {menu hits : List Nat} {h : Nat}
    {law : List (X × Int)} {hit : X → Nat → Bool} (cap : HasHitCap menu h law hit)
    (part : hits.Sublist menu) (large : h < hits.length) :
    containmentMass law hit hits = 0 := by
  unfold containmentMass
  rw [← total_zero law]
  apply total_congr
  intro atom member
  cases allHit : hits.all (hit atom.1) with
  | false => simp [allHit, indicator]
  | true =>
    have keeps : hits.filter (hit atom.1) = hits :=
      List.filter_eq_self.mpr (List.all_eq_true.mp allHit)
    have length := (part.filter (hit atom.1)).length_le
    rw [keeps] at length
    have limit := cap atom member
    omega

/-- The alternating-sign score relative to increasing order for specified
reference containment moments. -/
def centeredMomentScore (menu : List Nat) (moments : List Nat → Int)
    (rank : Nat → Nat) : Int :=
  ((deviationRows menu moments).map (weightedCentered (maxRank rank))).sum

/-- Degree exactly `h` rows of the deviation from reference moments. -/
def topDeviationRows (menu : List Nat) (h : Nat) (deviation : List Nat → Int) : List MomentRow :=
  (deviationRows menu deviation).filter (fun row => row.hits.length == h)

/-- Positive-degree rows below `h` of the deviation from reference moments. -/
def lowDeviationRows (menu : List Nat) (h : Nat) (deviation : List Nat → Int) : List MomentRow :=
  (deviationRows menu deviation).filter (fun row => decide (0 < row.hits.length ∧ row.hits.length < h))

private theorem deviation_row_sublist {menu : List Nat} {deviation : List Nat → Int} {row : MomentRow}
    (member : row ∈ deviationRows menu deviation) : row.hits.Sublist menu := by
  obtain ⟨term, present, rfl⟩ := List.mem_map.mp member
  exact subset_term_sublist present

theorem top_deviation_rows_unique {menu : List Nat} {h : Nat} {deviation : List Nat → Int}
    (unique : menu.Nodup) : ((topDeviationRows menu h deviation).map MomentRow.hits).Nodup := by
  have unfiltered : ((deviationRows menu deviation).map MomentRow.hits).Nodup := by
    simpa [deviationRows, List.map_map, Function.comp_def] using subset_terms_unique unique
  unfold topDeviationRows
  exact unfiltered.sublist (List.filter_sublist.map MomentRow.hits)

private theorem weighted_sum_rank_congr {menu : List Nat} {rows : List MomentRow}
    (complete : ∀ row ∈ rows, row.hits.Sublist menu) {r s : Nat → Nat}
    (agree : ∀ i ∈ menu, r i = s i) :
    (rows.map (weightedCentered (maxRank r))).sum =
      (rows.map (weightedCentered (maxRank s))).sum := by
  apply total_congr
  intro row member
  unfold weightedCentered
  rw [maxRank_congr _ _ _ (fun i inside => agree i ((complete row member).subset inside))]

private theorem total_filter (rows : List α) (keep : α → Bool) (f : α → Int) :
    total (rows.filter keep) f = total rows (fun row => if keep row then f row else 0) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    cases mark : keep row <;> simp [List.filter_cons, mark, ih]

private theorem centeredMomentScore_add (menu : List Nat) (a b : List Nat → Int)
    (rank : Nat → Nat) :
    centeredMomentScore menu (fun s => a s + b s) rank =
      centeredMomentScore menu a rank + centeredMomentScore menu b rank := by
  unfold centeredMomentScore deviationRows
  change total ((subsetTerms menu).map _) _ = total ((subsetTerms menu).map _) _ +
    total ((subsetTerms menu).map _) _
  rw [total_map, total_map, total_map, ← total_add]
  apply total_congr
  intro term _
  simp [weightedCentered, Int.mul_add, Int.add_mul]

private theorem split_centeredMomentScore (menu : List Nat) (h : Nat)
    (deviation : List Nat → Int) (rank : Nat → Nat)
    (cap : ∀ s, s.Sublist menu → h < s.length → deviation s = 0) :
    centeredMomentScore menu deviation rank =
      ((topDeviationRows menu h deviation).map (weightedCentered (maxRank rank))).sum +
      ((lowDeviationRows menu h deviation).map (weightedCentered (maxRank rank))).sum := by
  unfold centeredMomentScore topDeviationRows lowDeviationRows
  change total (deviationRows menu deviation) _ = total ((deviationRows menu deviation).filter _) _ +
    total ((deviationRows menu deviation).filter _) _
  rw [total_filter, total_filter, ← total_add]
  apply total_congr
  intro row included
  obtain ⟨term, member, equal⟩ := List.mem_map.mp included
  subst row
  by_cases top : term.1.length = h
  · simp [top]
  · by_cases low : 0 < term.1.length ∧ term.1.length < h
    · simp [top, low]
    · have degenerate : term.1.length = 0 ∨ h < term.1.length := by omega
      rcases degenerate with empty | above
      · have emptyList := List.length_eq_zero_iff.mp empty
        simp [weightedCentered, maxRank, top, low, emptyList]
      · have zero := cap term.1 (subset_term_sublist member) above
        simp [weightedCentered, top, low, zero]

/-- Operational cost, centered at the increasing order, equals the exact
two-layer `trueScore` used in the surrogate lemma. The reference moments
can be specified directly and need only vanish above the hit cap. -/
theorem centered_cost_eq_trueScore {menu order : List Nat} {m h : Nat}
    (complete : order.Perm menu) (baseComplete : (List.range' 1 m).Perm menu)
    (law : List (X × Int)) (hit : X → Nat → Bool) (fallback : Nat)
    (lawCap : HasHitCap menu h law hit) (reference : List Nat → Int)
    (referenceCap : ∀ s, s.Sublist menu → h < s.length → reference s = 0) :
    finiteCost law hit fallback order - finiteCost law hit fallback (List.range' 1 m) =
      let deviation := fun s => containmentMass law hit s - reference s
      Screening.LargestHits.trueScore (centeredMomentScore menu reference)
        (topDeviationRows menu h deviation) (lowDeviationRows menu h deviation) (probeRank order) := by
  have centered := centered_cost_deviation_eq_rows complete baseComplete law hit
    ([] : List (X × Int)) hit fallback
  simp only [finiteCost, total_nil, Int.sub_zero, containmentMass] at centered
  change finiteCost law hit fallback order - finiteCost law hit fallback (List.range' 1 m) =
    centeredMomentScore menu (containmentMass law hit) (probeRank order) at centered
  rw [centered]
  have decompose : containmentMass law hit =
      fun s => reference s + (containmentMass law hit s - reference s) := by
    funext s
    omega
  conv => lhs; rw [decompose]
  rw [centeredMomentScore_add]
  unfold Screening.LargestHits.trueScore
  rw [split_centeredMomentScore menu h (fun s => containmentMass law hit s - reference s)]
  · exact (Int.add_assoc _ _ _).symm
  · intro s part large
    rw [containmentMass_zero_of_hitCap lawCap part large, referenceCap s part large]
    rfl

/-- The operational identity holds with the identity extension off the menu,
whose displacement is meaningful globally. -/
theorem centered_cost_eq_trueScore_extended {menu order : List Nat} {m h : Nat}
    (complete : order.Perm menu) (baseComplete : (List.range' 1 m).Perm menu)
    (law : List (X × Int)) (hit : X → Nat → Bool) (fallback : Nat)
    (lawCap : HasHitCap menu h law hit) (reference : List Nat → Int)
    (referenceCap : ∀ s, s.Sublist menu → h < s.length → reference s = 0) :
    finiteCost law hit fallback order - finiteCost law hit fallback (List.range' 1 m) =
      let deviation := fun s => containmentMass law hit s - reference s
      Screening.LargestHits.trueScore (centeredMomentScore menu reference)
        (topDeviationRows menu h deviation) (lowDeviationRows menu h deviation)
        (extendedProbeRank order) := by
  rw [centered_cost_eq_trueScore complete baseComplete law hit fallback lawCap reference referenceCap]
  dsimp only [Screening.LargestHits.trueScore, centeredMomentScore, topDeviationRows, lowDeviationRows]
  have agree : ∀ i ∈ menu, probeRank order i = extendedProbeRank order i := by
    intro i inside
    exact (extendedProbeRank_of_mem (complete.mem_iff.mpr inside)).symm
  rw [weighted_sum_rank_congr (fun _ m => deviation_row_sublist m) agree,
    weighted_sum_rank_congr (fun _ m => deviation_row_sublist (List.mem_filter.mp m).1) agree,
    weighted_sum_rank_congr (fun _ m => deviation_row_sublist (List.mem_filter.mp m).1) agree]

/-- Counted deterministic surrogate regret for actual unit-cost scans.
On-menu rank bands suffice. The reference and deviation rows are generated
from their containment moments, and the near-cluster count is bounded by
the size of the menu and the displacement. -/
theorem operational_counted_surrogate_regret {menu chosen oracle : List Nat}
    {m h w ℓ topBound lowBound : Nat}
    (menuSorted : Screening.LargestHits.Descending menu)
    (chosenComplete : chosen.Perm menu) (oracleComplete : oracle.Perm menu)
    (baseComplete : (List.range' 1 m).Perm menu)
    (chosenBand : ∀ i ∈ chosen, i ≤ probeRank chosen i + w ∧ probeRank chosen i ≤ i + w)
    (oracleBand : ∀ i ∈ oracle, i ≤ probeRank oracle i + w ∧ probeRank oracle i ≤ i + w)
    (positive : 0 < ℓ)
    (law : List (X × Int)) (hit : X → Nat → Bool) (fallback : Nat)
    (lawCap : HasHitCap menu h law hit) (reference : List Nat → Int)
    (referenceCap : ∀ s, s.Sublist menu → h < s.length → reference s = 0)
    (topWeights : ∀ row ∈ topDeviationRows menu h (fun s => containmentMass law hit s - reference s),
      row.weight.natAbs ≤ topBound)
    (lowWeights : ∀ row ∈ lowDeviationRows menu h (fun s => containmentMass law hit s - reference s),
      row.weight.natAbs ≤ lowBound)
    (preferred :
      let top := topDeviationRows menu h (fun s => containmentMass law hit s - reference s)
      Screening.LargestHits.surrogateScore (centeredMomentScore menu reference) ℓ top
          (extendedProbeRank chosen) ≤
        Screening.LargestHits.surrogateScore (centeredMomentScore menu reference) ℓ top
          (extendedProbeRank oracle)) :
    finiteCost law hit fallback chosen - finiteCost law hit fallback oracle ≤
      (2 * ((2 * w * topBound) * (menu.length * ((2 * w + 1)^ℓ * menu.length^(h - 1 - ℓ))) +
        (w * lowBound) *
          (lowDeviationRows menu h (fun s => containmentMass law hit s - reference s)).length) : Nat) := by
  let deviation := fun s => containmentMass law hit s - reference s
  let top := topDeviationRows menu h deviation
  have menuUnique : menu.Nodup := baseComplete.nodup List.nodup_range'
  have unique : (top.map MomentRow.hits).Nodup := top_deviation_rows_unique menuUnique
  have sizes : ∀ row ∈ top, row.hits.length = h := by
    intro row member
    exact beq_iff_eq.mp (List.mem_filter.mp member).2
  have part : ∀ row ∈ top, row.hits.Sublist menu := by
    intro row member
    exact deviation_row_sublist (List.mem_filter.mp member).1
  have bounded : ∀ row ∈ top, ∀ i ∈ row.hits, i ∈ menu :=
    fun row member => (part row member).subset
  have sorted : ∀ row ∈ top, Screening.LargestHits.Descending row.hits :=
    fun row member => List.Pairwise.sublist (part row member) menuSorted
  have comparison := Screening.ClusterCount.counted_surrogate_regret menu
    (extendedProbeRank_displacement chosen w chosenBand)
    (extendedProbeRank_displacement oracle w oracleBand)
    positive unique sizes bounded sorted topWeights lowWeights preferred
  have actualChosen := centered_cost_eq_trueScore_extended chosenComplete baseComplete law hit
    fallback lawCap reference referenceCap
  have actualOracle := centered_cost_eq_trueScore_extended oracleComplete baseComplete law hit
    fallback lawCap reference referenceCap
  dsimp only at actualChosen actualOracle
  dsimp only [top, deviation] at comparison
  omega

end Screening.CostMoments

/- Source module: Screening.SampleVariance -/

/-! Finite iid sampling on rational laws. A list of equiprobable signed
integer tickets represents a distribution, and repetitions represent mass. -/
namespace Screening.SampleVariance

def weightedSum (f : Int → Int) : List Int → Int
  | [] => 0
  | x :: xs => f x + weightedSum f xs

def energy : List Int → Nat
  | [] => 0
  | x :: xs => x.natAbs*x.natAbs + energy xs

private theorem energy_cast (xs : List Int) :
    (energy xs : Int) = weightedSum (fun x => x*x) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [energy, weightedSum, Int.natCast_add, Int.natAbs_mul_self, ih]

private theorem weighted_append (f : Int → Int) (xs ys : List Int) :
    weightedSum f (xs++ys) = weightedSum f xs + weightedSum f ys := by
  induction xs with
  | nil => simp [weightedSum]
  | cons x xs ih => simp only [List.cons_append,weightedSum,ih,Int.add_assoc]

private theorem weighted_add (f g : Int → Int) (xs : List Int) :
    weightedSum (fun x => f x+g x) xs = weightedSum f xs + weightedSum g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [weightedSum,ih]; ac_rfl

private theorem weighted_const (c : Int) (xs : List Int) :
    weightedSum (fun _ => c) xs = (xs.length : Int)*c := by
  induction xs with
  | nil => simp [weightedSum]
  | cons x xs ih =>
    simp only [weightedSum,ih,List.length_cons,Int.natCast_succ,Int.add_mul,Int.one_mul]
    ac_rfl

private theorem weighted_factor (c : Int) (f : Int → Int) (xs : List Int) :
    weightedSum (fun x => c*f x) xs = c*weightedSum f xs := by
  induction xs with
  | nil => simp [weightedSum]
  | cons x xs ih => simp [weightedSum,ih,Int.mul_add]

private theorem weighted_map (f g : Int → Int) (xs : List Int) :
    weightedSum f (xs.map g) = weightedSum (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,weightedSum,ih]

/-- Each pair of tickets is enumerated once. This includes multiplicities,
so indices of identical values remain independent choices. -/
def convolve (xs ys : List Int) : List Int := xs.flatMap (fun x => ys.map (x+·))

def sampleSums (law : List Int) : Nat → List Int
  | 0 => [0]
  | n+1 => convolve (sampleSums law n) law

private theorem convolve_length (xs ys : List Int) :
    (convolve xs ys).length = xs.length*ys.length := by
  induction xs with
  | nil => simp [convolve]
  | cons x xs ih =>
    change ((ys.map (x+·))++convolve xs ys).length = (xs.length+1)*ys.length
    simp [ih,Nat.add_mul,Nat.add_comm]

theorem sample_length (law : List Int) (n : Nat) :
    (sampleSums law n).length = law.length^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sampleSums,convolve_length,ih,Nat.pow_succ]

/-- Integer centering of any ticket law. Division by its positive length
recovers the usual centered observation x − E[X]. -/
def centered (law : List Int) : List Int :=
  law.map (fun x => (law.length : Int)*x - weightedSum id law)

theorem centered_mean_zero (law : List Int) : weightedSum id (centered law) = 0 := by
  have line : weightedSum (fun x => (law.length : Int)*x) law =
      (law.length : Int)*weightedSum id law := weighted_factor _ id _
  simp only [centered,weighted_map,id_eq,Int.sub_eq_add_neg]
  rw [weighted_add,weighted_const,line,Int.mul_neg,Int.add_right_neg]

private theorem convolve_centered_mean (xs law : List Int) (hc : weightedSum id law = 0) :
    weightedSum id (convolve xs law) = (law.length : Int)*weightedSum id xs := by
  induction xs with
  | nil => simp [convolve,weightedSum]
  | cons x xs ih =>
    change weightedSum id (law.map (x+·) ++ convolve xs law) = _
    have shift : weightedSum id (law.map (x+·)) = (law.length : Int)*x := by
      rw [weighted_map]
      change weightedSum (fun y => x + id y) law = _
      rw [weighted_add,weighted_const,hc,Int.add_zero]
    rw [weighted_append,shift,ih]
    simp only [weightedSum,id_eq,Int.mul_add]

theorem iid_mean_zero (law : List Int) (hc : weightedSum id law = 0) (n : Nat) :
    weightedSum id (sampleSums law n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sampleSums,convolve_centered_mean _ _ hc,ih,Int.mul_zero]

/-- The mixed terms in the square sum vanish because the next independent
ticket has mean zero. No zero-mean assumption on the existing partial sums. -/
private theorem shifted_square (s : Int) (law : List Int) (hc : weightedSum id law = 0) :
    weightedSum (fun x => x*x) (law.map (s+·)) =
      (law.length : Int)*(s*s) + weightedSum (fun x => x*x) law := by
  rw [weighted_map]
  have poly : (fun x : Int => (s+x)*(s+x)) =
      (fun x => ((s*s+s*x)+s*x)+x*x) := by
    funext x
    simp only [Int.add_mul,Int.mul_add]
    ac_rfl
  have cross : weightedSum (fun x => s*x) law = 0 := calc
    _ = s*weightedSum id law := weighted_factor s id law
    _ = 0 := by rw [hc,Int.mul_zero]
  rw [poly,weighted_add,weighted_add,weighted_add,weighted_const,cross]
  simp

private theorem convolve_square (xs law : List Int) (hc : weightedSum id law = 0) :
    weightedSum (fun x => x*x) (convolve xs law) =
      (law.length : Int)*weightedSum (fun x => x*x) xs +
      (xs.length : Int)*weightedSum (fun x => x*x) law := by
  induction xs with
  | nil => simp [convolve,weightedSum]
  | cons x xs ih =>
    change weightedSum _ (law.map (x+·) ++ convolve xs law) = _
    rw [weighted_append,shifted_square x law hc,ih]
    simp only [weightedSum,List.length_cons,Int.natCast_succ,Int.add_mul,Int.one_mul,Int.mul_add]
    ac_rfl

private theorem convolve_energy (xs law : List Int) (hc : weightedSum id law = 0) :
    energy (convolve xs law) = law.length*energy xs + xs.length*energy law := by
  have h := convolve_square xs law hc
  rw [← energy_cast, ← energy_cast, ← energy_cast] at h
  omega

/-- After dividing by the positive ticket counts, this gives
E[(X₁+...+Xₙ)²] = n E[X₁²] for a centered law. -/
theorem iid_variance (law : List Int) (hc : weightedSum id law = 0) (n : Nat) :
    law.length*energy (sampleSums law n) = n*(sampleSums law n).length*energy law := by
  induction n with
  | zero => simp [sampleSums,energy]
  | succ n ih =>
    rw [sampleSums,convolve_energy _ law hc,convolve_length]
    rw [Nat.mul_add,ih,Nat.add_mul,Nat.add_mul]
    simp only [Nat.one_mul]
    ac_rfl

/-- For rational threshold a/d, bad tickets are those with
|sum|/n > a/d. The event test below is division-free. -/
def badCount (xs : List Int) (t d : Nat) : Nat :=
  xs.countP (fun s => decide (t < d*s.natAbs))

def goodCount (xs : List Int) (t d : Nat) : Nat :=
  xs.countP (fun s => decide (d*s.natAbs ≤ t))

private theorem sum_square_markov (xs : List Int) (t d : Nat) :
    t*t*badCount xs t d ≤ d*d*energy xs := by
  induction xs with
  | nil => simp [badCount,energy]
  | cons x xs ih =>
    change t*t*(List.countP _ (x::xs)) ≤ d*d*(x.natAbs*x.natAbs+energy xs)
    rw [List.countP_cons, Nat.mul_add, Nat.mul_add]
    change t*t*badCount xs t d + _ ≤ _
    by_cases h : t < d*x.natAbs
    · have hsq := Nat.mul_le_mul (Nat.le_of_lt h) (Nat.le_of_lt h)
      have one : t*t ≤ d*d*(x.natAbs*x.natAbs) := by
        calc t*t ≤ (d*x.natAbs)*(d*x.natAbs) := hsq
             _ = d*d*(x.natAbs*x.natAbs) := by ac_rfl
      simp only [h,decide_true,if_true,Nat.mul_one]
      omega
    · simp only [h,decide_false,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero]
      omega

/-- Chebyshev for an arbitrary finite rational ticket law and N>0:
P(|sample mean|>a/d) ≤ d² E[X²]/(N a²), written by cross multiplication. -/
theorem chebyshev (law : List Int) (hc : weightedSum id law = 0)
    {n : Nat} (hn : 0 < n) (a d : Nat) :
    (law.length*n*a*a)*badCount (sampleSums law n) (n*a) d ≤
      (d*d*energy law)*(sampleSums law n).length := by
  let ys := sampleSums law n
  have hv := iid_variance law hc n
  change law.length*energy ys = n*ys.length*energy law at hv
  have raw := sum_square_markov ys (n*a) d
  apply Nat.le_of_mul_le_mul_left (c:=n) _ hn
  calc n*((law.length*n*a*a)*badCount ys (n*a) d)
        = law.length*((n*a)*(n*a)*badCount ys (n*a) d) := by ac_rfl
       _ ≤ law.length*(d*d*energy ys) := Nat.mul_le_mul_left law.length raw
       _ = d*d*(law.length*energy ys) := by ac_rfl
       _ = d*d*(n*ys.length*energy law) := by rw [hv]
       _ = n*((d*d*energy law)*ys.length) := by ac_rfl

private theorem count_partition (xs : List Int) (t d : Nat) :
    goodCount xs t d + badCount xs t d = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [goodCount,badCount,List.countP_cons,decide_eq_true_eq,List.length_cons] at ih ⊢
    split <;> split <;> omega

/-- Block success probability is at least 3/4 provided
n*(a/d)² ≥ 4 E[X²]. Both sides are exact ticket counts. -/
theorem block_three_quarters (law : List Int) (hc : weightedSum id law = 0)
    {n a d : Nat} (hK : 0 < law.length) (hn : 0 < n) (ha : 0 < a) (_hd : 0 < d)
    (hsize : 4*(d*d*energy law) ≤ law.length*n*a*a) :
    3*(sampleSums law n).length ≤ 4*goodCount (sampleSums law n) (n*a) d := by
  let ys := sampleSums law n
  let c := law.length*n*a*a
  have cpos : 0 < c := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hK hn) ha) ha
  have h := chebyshev law hc hn a d
  have bad : 4*badCount ys (n*a) d ≤ ys.length := by
    apply Nat.le_of_mul_le_mul_left (c:=c) _ cpos
    calc c*(4*badCount ys (n*a) d) = 4*(c*badCount ys (n*a) d) := by ac_rfl
         _ ≤ 4*((d*d*energy law)*ys.length) := Nat.mul_le_mul_left 4 h
         _ = (4*(d*d*energy law))*ys.length := by ac_rfl
         _ ≤ c*ys.length := Nat.mul_le_mul_right _ hsize
  have total := count_partition ys (n*a) d
  change 3*ys.length ≤ 4*goodCount ys (n*a) d
  omega

/-- Specialization to one fixed prefix and the tolerance u/(3m) in
Proposition active-one-hit. For nonintegral u, the generic theorem also
allows arbitrary positive rational threshold a/d. -/
theorem prefix_block (law : List Int) (hc : weightedSum id law = 0)
    {n m u : Nat} (hK : 0 < law.length) (hn : 0 < n) (hm : 0 < m) (hu : 0 < u)
    (hsize : 4*((3*m)*(3*m)*energy law) ≤ law.length*n*u*u) :
    3*(sampleSums law n).length ≤ 4*goodCount (sampleSums law n) (n*u) (3*m) :=
  block_three_quarters law hc hK hn hu (by omega) hsize

/-! Independent repetitions and a union over prefixes on the same data. -/

/-- Every possible ordered sample, retaining repeated tickets. There is no
assumption that different predicates on the same ticket are independent. -/
def iidTuples {α : Type} (law : List α) : Nat → List (List α)
  | 0 => [[]]
  | k+1 => law.flatMap (fun x => (iidTuples law k).map (x::·))

private def mass {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + mass f xs

private theorem mass_append {α : Type} (f : α → Nat) (xs ys : List α) :
    mass f (xs++ys) = mass f xs + mass f ys := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simp [mass,ih,Nat.add_assoc]

private theorem mass_map {α β : Type} (f : β → Nat) (g : α → β) (xs : List α) :
    mass f (xs.map g) = mass (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mass,ih]

private theorem mass_flatMap {α β : Type} (f : β → Nat) (g : α → List β) (xs : List α) :
    mass f (xs.flatMap g) = mass (fun x => mass f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mass,List.flatMap_cons,mass_append,ih]

private theorem mass_factor {α : Type} (f : α → Nat) (c : Nat) (xs : List α) :
    mass (fun x => c*f x) xs = c*mass f xs := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simp [mass,ih,Nat.mul_add]

private theorem mass_right {α : Type} (f : α → Nat) (c : Nat) (xs : List α) :
    mass (fun x => f x*c) xs = mass f xs*c := by
  simpa only [Nat.mul_comm c] using mass_factor f c xs

private def tupleWeight {α : Type} (f : α → Nat) : List α → Nat
  | [] => 1
  | x :: xs => f x * tupleWeight f xs

private theorem product_mass {α : Type} (f : α → Nat) (law : List α) (k : Nat) :
    mass (tupleWeight f) (iidTuples law k) = (mass f law)^k := by
  induction k with
  | zero => simp [iidTuples,mass,tupleWeight]
  | succ k ih =>
    rw [iidTuples,mass_flatMap]
    simp only [mass_map,tupleWeight,mass_factor,ih,mass_right,Nat.pow_succ]
    ac_rfl

private theorem mass_one {α : Type} (xs : List α) :
    mass (fun _ => 1) xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mass,ih,Nat.add_comm]

private theorem ones_tuple {α : Type} (xs : List α) :
    tupleWeight (fun _ => 1) xs = 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [tupleWeight,ih]

theorem iidTuples_length {α : Type} (law : List α) (k : Nat) :
    (iidTuples law k).length = law.length^k := by
  have h := product_mass (fun _ => 1) law k
  have f : tupleWeight (fun _ : α => 1) = fun _ => 1 := funext ones_tuple
  simpa only [f,mass_one] using h

private def tilt {α : Type} (bad : α → Bool) (x : α) := if bad x then 3 else 1

private theorem one_tilt {α : Type} (bad : α → Bool) (law : List α) :
    mass (tilt bad) law = law.length+2*law.countP bad := by
  induction law with
  | nil => rfl
  | cons x xs ih =>
    simp only [mass,tilt,List.countP_cons,List.length_cons,ih]
    cases bad x <;> simp <;> omega

private theorem tuple_tilt {α : Type} (bad : α → Bool) (xs : List α) :
    tupleWeight (tilt bad) xs = 3^(xs.countP bad) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [tupleWeight,tilt,List.countP_cons,ih]
    cases bad x <;> simp [Nat.pow_succ,Nat.mul_comm]

/-- Number of bad-block indicators in a tuple is at least t. -/
def atLeastBad {α : Type} (bad : α → Bool) (t : Nat) (xs : List α) : Bool :=
  decide (t ≤ xs.countP bad)

private theorem tilted_markov {α : Type} (bad : α → Bool) (t : Nat) (rows : List (List α)) :
    3^t*rows.countP (atLeastBad bad t) ≤ mass (tupleWeight (tilt bad)) rows := by
  induction rows with
  | nil => simp [mass]
  | cons x xs ih =>
    simp only [mass,List.countP_cons,atLeastBad,decide_eq_true_eq,Nat.mul_add] at *
    by_cases h : t ≤ x.countP bad
    · have hv := Nat.pow_le_pow_right (n:=3) (by decide) h
      simp only [h,if_true,Nat.mul_one,tuple_tilt]
      omega
    · simp only [h,if_false,Nat.mul_zero,Nat.add_zero]
      omega

/-- The generating function at 3, evaluated on the actual product
enumeration, gives an exponential failure bound. -/
theorem exponential_tail {α : Type} (law : List α) (bad : α → Bool)
    (hb : 4*law.countP bad ≤ law.length) (k t : Nat) :
    (2^k*3^t)*(iidTuples law k).countP (atLeastBad bad t) ≤
      3^k*(iidTuples law k).length := by
  have h := tilted_markov bad t (iidTuples law k)
  rw [product_mass,one_tilt] at h
  rw [iidTuples_length]
  calc (2^k*3^t)*(iidTuples law k).countP (atLeastBad bad t)
          = 2^k*(3^t*(iidTuples law k).countP (atLeastBad bad t)) := Nat.mul_assoc _ _ _
       _ ≤ 2^k*(law.length+2*law.countP bad)^k := Nat.mul_le_mul_left _ h
       _ = (2*(law.length+2*law.countP bad))^k := (Nat.mul_pow _ _ _).symm
       _ ≤ (3*law.length)^k := Nat.pow_le_pow_left (by omega) k
       _ = 3^k*law.length^k := Nat.mul_pow _ _ _

/-- For 2s+1 independent blocks, failure of a strict good majority has
probability at most (1/2)(3/4)^s. -/
theorem majority_amplification {α : Type} (law : List α) (bad : α → Bool)
    (hb : 4*law.countP bad ≤ law.length) (s : Nat) :
    (2*4^s)*(iidTuples law (2*s+1)).countP (atLeastBad bad (s+1)) ≤
      3^s*(iidTuples law (2*s+1)).length := by
  have h := exponential_tail law bad hb (2*s+1) (s+1)
  have h2 : 2^(2*s+1) = 2*4^s := by
    rw [Nat.pow_succ,Nat.pow_mul]
    change 4^s*2 = 2*4^s
    exact Nat.mul_comm _ _
  have h3 : 3^(2*s+1) = 3^(s+1)*3^s := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h2,h3] at h
  apply Nat.le_of_mul_le_mul_left (c:=3^(s+1)) _ (Nat.pow_pos (by decide))
  calc 3^(s+1)*(2*4^s*(iidTuples law (2*s+1)).countP (atLeastBad bad (s+1)))
          = (2*4^s*3^(s+1))*(iidTuples law (2*s+1)).countP (atLeastBad bad (s+1)) := by ac_rfl
       _ ≤ _ := h
       _ = _ := Nat.mul_assoc _ _ _

private theorem count_or_le {α : Type} (f g : α → Bool) (xs : List α) :
    xs.countP (fun x => f x || g x) ≤ xs.countP f + xs.countP g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons]
    cases f x <;> cases g x <;> simp <;> omega

/-- Simultaneous union bound. Every predicate is evaluated on the same
independent block tuple. Correlations among different prefixes are allowed. -/
theorem simultaneous_prefix_bound {α : Type} (law : List α) (prefixes : List (α → Bool))
    (hb : ∀ f ∈ prefixes, 4*law.countP f ≤ law.length) (s : Nat) :
    (2*4^s)*(iidTuples law (2*s+1)).countP
      (fun row => prefixes.any (fun f => atLeastBad f (s+1) row)) ≤
      prefixes.length*(3^s*(iidTuples law (2*s+1)).length) := by
  let rows := iidTuples law (2*s+1)
  induction prefixes with
  | nil => simp
  | cons f fs ih =>
    have hhead := majority_amplification law f (hb f (by simp)) s
    have hrest := ih (fun g hg => hb g (by simp [hg]))
    simp only [List.any_cons,List.length_cons]
    calc 2*4^s*rows.countP (fun row =>
             atLeastBad f (s+1) row || fs.any (fun g => atLeastBad g (s+1) row))
          ≤ 2*4^s*(rows.countP (atLeastBad f (s+1)) +
             rows.countP (fun row => fs.any (fun g => atLeastBad g (s+1) row))) :=
              Nat.mul_le_mul_left _ (count_or_le _ _ _)
         _ ≤ 3^s*rows.length + fs.length*(3^s*rows.length) := by
           rw [Nat.mul_add]
           exact Nat.add_le_add hhead hrest
         _ = (fs.length+1)*(3^s*rows.length) := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]

/-- Concrete composition: Chebyshev on each fresh sample block, followed
by independent majority amplification. -/
theorem block_means_amplified (law : List Int) (hc : weightedSum id law = 0)
    {n a d : Nat} (hK : 0 < law.length) (hn : 0 < n) (ha : 0 < a) (hd : 0 < d)
    (hsize : 4*(d*d*energy law) ≤ law.length*n*a*a) (s : Nat) :
    let blocks := sampleSums law n
    let bad := fun x : Int => decide (n*a < d*x.natAbs)
    (2*4^s)*(iidTuples blocks (2*s+1)).countP (atLeastBad bad (s+1)) ≤
      3^s*(iidTuples blocks (2*s+1)).length := by
  have hg := block_three_quarters law hc hK hn ha hd hsize
  have hp := count_partition (sampleSums law n) (n*a) d
  apply majority_amplification
  change 4*badCount (sampleSums law n) (n*a) d ≤ (sampleSums law n).length
  omega

end Screening.SampleVariance

/- Source module: Screening.NaturalWindow -/

/-! Finite precedence and displacement certificates for complete arithmetic menus. -/

namespace Screening.NaturalWindow

open Screening.ScreeningCost (scan survives newHit populationCost newHitMass)
open Screening.CostMoments (probeRank subsetTerms)

private def total (xs : List α) (f : α → Int) : Int := (xs.map f).sum

@[simp] private theorem total_nil (f : α → Int) : total [] f = 0 := rfl

@[simp] private theorem total_cons (x : α) (xs : List α) (f : α → Int) :
    total (x :: xs) f = f x + total xs f := rfl

private theorem total_zero (xs : List α) : total xs (fun _ => 0) = 0 := by
  induction xs <;> simp_all

private theorem total_congr (xs : List α) {f g : α → Int} (eq : ∀ x ∈ xs, f x = g x) :
    total xs f = total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [total_cons, total_cons, eq x (by simp), ih (fun y inside => eq y (by simp [inside]))]

private theorem total_add (xs : List α) (f g : α → Int) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [total_cons, ih]
    omega

private theorem total_sub (xs : List α) (f g : α → Int) :
    total xs (fun x => f x - g x) = total xs f - total xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [total_cons, ih]
    omega

private theorem total_neg (xs : List α) (f : α → Int) :
    total xs (fun x => -f x) = -total xs f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [total_cons, ih]
    omega

private theorem total_map (xs : List α) (g : α → β) (f : β → Int) :
    total (xs.map g) f = total xs (fun x => f (g x)) := by
  rw [total, List.map_map]
  rfl

private theorem total_append (xs ys : List α) (f : α → Int) :
    total (xs ++ ys) f = total xs f + total ys f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, total_cons, ih, Int.add_assoc]

private theorem total_left_mul (xs : List α) (a : Int) (f : α → Int) :
    total xs (fun x => a * f x) = a * total xs f := by
  induction xs <;> simp_all [Int.mul_add]

private theorem total_commute (xs : List α) (ys : List β) (f : α → β → Int) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [total_zero]
  | cons x xs ih => simp only [total_cons, total_add, ih]

private theorem total_nonnegative (xs : List α) (f : α → Int)
    (h : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ total xs f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [total_cons]
    exact Int.add_nonneg (h x (by simp)) (ih (fun y inside => h y (by simp [inside])))

/-- Prefixes of the middle block, including the full block and the empty prefix. -/
def inclusivePrefixes : List α → List (List α)
  | [] => [[]]
  | i :: rest => [] :: (inclusivePrefixes rest).map (i :: ·)

theorem empty_mem_inclusivePrefixes (xs : List α) : [] ∈ inclusivePrefixes xs := by
  cases xs <;> simp [inclusivePrefixes]

theorem inclusivePrefixes_sublist {xs ys : List α} (member : ys ∈ inclusivePrefixes xs) :
    ys.Sublist xs := by
  induction xs generalizing ys with
  | nil =>
    have eq : ys = [] := by simpa [inclusivePrefixes] using member
    subst ys
    exact .slnil
  | cons i xs ih =>
    rw [inclusivePrefixes, List.mem_cons] at member
    rcases member with rfl | extended
    · exact List.nil_sublist _
    · obtain ⟨earlier, inside, rfl⟩ := List.mem_map.mp extended
      exact .cons₂ i (ih inside)

private theorem scan_through_hit (hit : α → Bool) (fallback : Nat) (middle suffix : List α)
    {i : α} (found : hit i = true) :
    (scan hit fallback (middle ++ i :: suffix) : Int) =
      total (inclusivePrefixes middle) (fun before => ((survives hit before).toNat : Int)) := by
  induction middle with
  | nil => simp [inclusivePrefixes, scan, survives, found]
  | cons x middle ih =>
    simp only [List.cons_append, inclusivePrefixes, total_cons, total_map]
    cases test : hit x
    · simpa [scan, survives, test, Int.ofNat_add] using congrArg (fun t : Int => 1 + t) ih
    · simp [scan, survives, test, total_zero]

private theorem scan_equal_hits (hit : α → Bool) (fallback : Nat) (middle suffix : List α)
    {i j : α} (same : hit i = hit j) :
    scan hit fallback (middle ++ i :: suffix) = scan hit fallback (middle ++ j :: suffix) := by
  induction middle with
  | nil => simp [scan, same]
  | cons x middle ih => cases hx : hit x <;> simp [scan, hx, ih]

/-- A nonadjacent exchange decomposes into all affected common-prefix hazards. -/
theorem atom_nonadjacent_swap (hit : α → Bool) (fallback : Nat)
    (pre middle suffix : List α) (i j : α) :
    (scan hit fallback (pre ++ j :: (middle ++ i :: suffix)) : Int) -
        (scan hit fallback (pre ++ i :: (middle ++ j :: suffix)) : Int) =
      total (inclusivePrefixes middle) (fun part =>
        (newHit hit (pre ++ part) i : Int) - (newHit hit (pre ++ part) j : Int)) := by
  induction pre with
  | nil =>
    simp only [List.nil_append]
    cases hi : hit i <;> cases hj : hit j
    · have equal := scan_equal_hits hit fallback middle suffix (hi.trans hj.symm)
      simp [scan, hi, hj, newHit, total_zero, equal]
    · simp only [scan, hi, hj, Bool.false_eq_true, if_false, if_true, Int.ofNat_add]
      rw [scan_through_hit hit fallback middle suffix hj]
      simp [newHit, hi, hj, total_neg]
      omega
    · simp only [scan, hi, hj, Bool.false_eq_true, if_false, if_true, Int.ofNat_add]
      rw [scan_through_hit hit fallback middle suffix hi]
      simp [newHit, hi, hj]
      omega
    · simp [scan, hi, hj, newHit, total_zero]
  | cons x pre ih =>
    simp only [List.cons_append]
    cases hx : hit x
    · have cancel (a b : Int) : 1 + a - (1 + b) = a - b := by omega
      simpa [scan, newHit, survives, hx, Int.ofNat_add, cancel] using ih
    · simp [scan, newHit, survives, hx, total_zero]

private theorem coe_weighted (law : List (X × Nat)) (f : X → Nat) :
    (Screening.ScreeningCost.weighted law f : Int) =
      total law (fun atom => (atom.2 : Int) * (f atom.1 : Int)) := by
  induction law with
  | nil => rfl
  | cons atom law ih =>
    change ((atom.2 * f atom.1 + Screening.ScreeningCost.weighted law f : Nat) : Int) = _
    simp only [Int.ofNat_add, Int.ofNat_mul, total_cons, ih]

theorem population_nonadjacent_swap (law : List (X × Nat)) (hit : X → α → Bool)
    (fallback : Nat) (pre middle suffix : List α) (i j : α) :
    (populationCost law hit fallback (pre ++ j :: (middle ++ i :: suffix)) : Int) -
        (populationCost law hit fallback (pre ++ i :: (middle ++ j :: suffix)) : Int) =
      total (inclusivePrefixes middle) (fun part =>
        (newHitMass law hit (pre ++ part) i : Int) - (newHitMass law hit (pre ++ part) j : Int)) := by
  simp only [populationCost, newHitMass, coe_weighted, ← total_sub]
  apply Eq.trans (b := total law (fun atom =>
    total (inclusivePrefixes middle) (fun part =>
      (atom.2 : Int) * ((newHit (hit atom.1) (pre ++ part) i : Int) -
        (newHit (hit atom.1) (pre ++ part) j : Int)))))
  · apply total_congr
    intro atom _
    rw [← Int.mul_sub, atom_nonadjacent_swap, total_left_mul]
  · rw [total_commute]
    apply total_congr
    intro part _
    apply total_congr
    intro atom _
    exact Int.mul_sub ..

/-- Weak dominance on the affected prefixes and strict dominance at the first
one make the exchange a strict operational improvement. -/
theorem strict_nonadjacent_improvement (law : List (X × Nat)) (hit : X → α → Bool)
    (fallback : Nat) (pre middle suffix : List α) (i j : α)
    (weak : ∀ part ∈ inclusivePrefixes middle, newHitMass law hit (pre ++ part) j ≤
      newHitMass law hit (pre ++ part) i)
    (first : newHitMass law hit pre j < newHitMass law hit pre i) :
    populationCost law hit fallback (pre ++ i :: (middle ++ j :: suffix)) <
      populationCost law hit fallback (pre ++ j :: (middle ++ i :: suffix)) := by
  have exchange := population_nonadjacent_swap law hit fallback pre middle suffix i j
  let term := fun part => (newHitMass law hit (pre ++ part) i : Int) -
    (newHitMass law hit (pre ++ part) j : Int)
  have initial : 0 < term [] := by
    simp only [term, List.append_nil]
    omega
  have nonnegative : ∀ part ∈ inclusivePrefixes middle, 0 ≤ term part := by
    intro part member
    have compares := weak part member
    simp only [term]
    omega
  change _ = total (inclusivePrefixes middle) term at exchange
  have positive : 0 < total (inclusivePrefixes middle) term := by
    cases middle with
    | nil => simpa [inclusivePrefixes] using initial
    | cons k tail =>
      simp only [inclusivePrefixes, total_cons]
      have tailSum := total_nonnegative ((inclusivePrefixes tail).map (k :: ·)) term
        (fun part member => nonnegative part (by simp [inclusivePrefixes, member]))
      omega
  omega

/-- Tests strictly before the named label in its actual scan order. -/
def before (order : List Nat) (label : Nat) : List Nat := order.take (order.idxOf label)

theorem mem_before_iff_rank_lt {order : List Nat} {i j : Nat} (inside : i ∈ order) :
    j ∈ before order i ↔ probeRank order j < probeRank order i := by
  have idx := List.idxOf_lt_length inside
  rw [before, Screening.CostMoments.mem_take_iff_probeRank (Nat.le_of_lt idx)]
  change probeRank order j ≤ order.idxOf i ↔ probeRank order j < order.idxOf i + 1
  omega

private theorem probeRank_injective_on_order {order : List Nat} {i j : Nat}
    (inside : i ∈ order) (same : probeRank order i = probeRank order j) : i = j := by
  have idx := List.idxOf_lt_length inside
  have within : order.idxOf i + 1 ≤ order.length := by omega
  have iHere : i ∈ order.take (order.idxOf i + 1) :=
    (Screening.CostMoments.mem_take_iff_probeRank within).mpr (by simp [probeRank])
  have jHere : j ∈ order.take (order.idxOf i + 1) :=
    (Screening.CostMoments.mem_take_iff_probeRank within).mpr (by
      rw [← same]
      simp [probeRank])
  have iNew : i ∉ order.take (order.idxOf i) := by
    intro part
    exact (Nat.lt_irrefl _) ((mem_before_iff_rank_lt inside).mp part)
  have jNew : j ∉ order.take (order.idxOf i) := by
    intro part
    have early := (mem_before_iff_rank_lt inside).mp part
    omega
  rw [List.take_succ_eq_append_getElem idx, List.mem_append] at iHere jHere
  have ie : i = order[order.idxOf i] := by
    simpa using iHere.resolve_left iNew
  have je : j = order[order.idxOf i] := by
    simpa using jHere.resolve_left jNew
  exact ie.trans je.symm

private theorem mem_drop_of_not_mem_take {order : List Nat} {i k : Nat}
    (inside : i ∈ order) (later : i ∉ order.take k) : i ∈ order.drop k := by
  have partition : i ∈ order.take k ++ order.drop k := by
    rwa [List.take_append_drop]
  exact (List.mem_append.mp partition).resolve_left later

private theorem split_rank_inversion {order : List Nat} {i j : Nat} (iInside : i ∈ order)
    (inversion : probeRank order j < probeRank order i) :
    ∃ pre middle suffix, order = pre ++ j :: (middle ++ i :: suffix) := by
  have jEarly := (mem_before_iff_rank_lt iInside).mpr inversion
  have iLate : i ∉ before order i := by
    intro member
    exact (Nat.lt_irrefl _) ((mem_before_iff_rank_lt iInside).mp member)
  have inDrop := mem_drop_of_not_mem_take iInside iLate
  obtain ⟨pre, left, cutAtJ⟩ := List.append_of_mem jEarly
  obtain ⟨right, suffix, cutAtI⟩ := List.append_of_mem inDrop
  refine ⟨pre, left ++ right, suffix, ?_⟩
  have parts := List.take_append_drop (order.idxOf i) order
  change before order i ++ order.drop (order.idxOf i) = order at parts
  rw [cutAtJ, cutAtI] at parts
  simpa [List.append_assoc] using parts.symm

private theorem swapped_perm (pre middle suffix : List Nat) (i j : Nat) :
    (pre ++ j :: (middle ++ i :: suffix)).Perm (pre ++ i :: (middle ++ j :: suffix)) := by
  apply List.Perm.append_left
  exact (List.perm_middle.cons j).trans
    ((List.Perm.swap i j (middle ++ suffix)).trans (List.perm_middle.symm.cons i))

/-- A complete order minimizes the actual finite population cost. -/
def CompleteOptimum (law : List (X × Nat)) (hit : X → Nat → Bool) (fallback : Nat)
    (menu order : List Nat) : Prop :=
  order.Perm menu ∧
    ∀ candidate, candidate.Perm menu →
      populationCost law hit fallback order ≤ populationCost law hit fallback candidate

/-- A globally dominating label cannot occur behind the dominated label in
any complete optimum. The hazards need comparison only on contexts without
either of the exchanged labels. -/
theorem optimum_respects_context_dominance (law : List (X × Nat)) (hit : X → Nat → Bool)
    (fallback : Nat) {menu order : List Nat} {i j : Nat}
    (unique : menu.Nodup) (optimal : CompleteOptimum law hit fallback menu order)
    (iInside : i ∈ menu) (distinct : i ≠ j)
    (dominates : ∀ ctx, ctx.Nodup → (∀ k ∈ ctx, k ∈ menu) → i ∉ ctx → j ∉ ctx →
      newHitMass law hit ctx j < newHitMass law hit ctx i) :
    probeRank order i < probeRank order j := by
  have iInOrder := optimal.1.mem_iff.mpr iInside
  have unequal : probeRank order i ≠ probeRank order j :=
    fun equal => distinct (probeRank_injective_on_order iInOrder equal)
  by_cases desired : probeRank order i < probeRank order j
  · exact desired
  · have inverse : probeRank order j < probeRank order i := by omega
    obtain ⟨pre, middle, suffix, shape⟩ := split_rank_inversion iInOrder inverse
    have perm := optimal.1
    rw [shape] at perm
    have allUnique := perm.symm.nodup unique
    have leftPrefixCtx : ∀ part ∈ inclusivePrefixes middle, (pre ++ part).Sublist
        (pre ++ j :: (middle ++ i :: suffix)) := by
      intro part member
      exact ((inclusivePrefixes_sublist member).trans
        (List.sublist_append_left middle (i :: suffix))).cons j |>.append_left pre
    have withoutI : i ∉ pre ++ middle := by
      intro member
      rcases List.mem_append.mp member with inPre | inMid
      · exact (List.pairwise_append.mp allUnique).2.2 i inPre i (by simp) rfl
      · have tailUnique := (List.nodup_cons.mp (List.pairwise_append.mp allUnique).2.1).2
        exact (List.pairwise_append.mp tailUnique).2.2 i inMid i (by simp) rfl
    have withoutJ : j ∉ pre ++ middle := by
      intro member
      rcases List.mem_append.mp member with inPre | inMid
      · exact (List.pairwise_append.mp allUnique).2.2 j inPre j (by simp) rfl
      · have jFresh := (List.nodup_cons.mp (List.pairwise_append.mp allUnique).2.1).1
        exact jFresh (List.mem_append_left _ inMid)
    have better : ∀ part ∈ inclusivePrefixes middle,
        newHitMass law hit (pre ++ part) j < newHitMass law hit (pre ++ part) i := by
      intro part member
      have contexts := (inclusivePrefixes_sublist member).append_left pre
      have contained := leftPrefixCtx part member
      exact dominates _ (allUnique.sublist contained)
        (fun k seen => perm.mem_iff.mp (contained.subset seen))
        (fun hi => withoutI (contexts.subset hi)) (fun hj => withoutJ (contexts.subset hj))
    have gains := strict_nonadjacent_improvement law hit fallback pre middle suffix i j
      (fun part member => Nat.le_of_lt (better part member)) (by
        simpa using better [] (empty_mem_inclusivePrefixes middle))
    have allowed := (swapped_perm pre middle suffix i j).symm.trans perm
    have comparator := optimal.2 _ allowed
    rw [shape] at comparator
    omega

private theorem nodup_length_le_of_subset [DecidableEq α] {xs ys : List α}
    (unique : xs.Nodup) (part : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have present := part x List.mem_cons_self
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp unique
    have tailPart : ∀ y ∈ xs, y ∈ ys.erase x := by
      intro y member
      have unequal : y ≠ x := fun equal => fresh (equal ▸ member)
      exact (List.mem_erase_of_ne unequal).mpr (part y (List.mem_cons_of_mem _ member))
    have reduced := ih rest tailPart
    rw [List.length_erase_of_mem present] at reduced
    have positive := List.length_pos_of_mem present
    simp only [List.length_cons]
    omega

private theorem value_lt_of_rank_lt {natural : List Nat} {value : Nat → Nat} {i j : Nat}
    (sorted : natural.Pairwise (fun a b => value a < value b)) (jInside : j ∈ natural)
    (earlier : probeRank natural i < probeRank natural j) : value i < value j := by
  have iEarly := (mem_before_iff_rank_lt jInside).mpr earlier
  have jLate : j ∉ before natural j := by
    intro inside
    exact (Nat.lt_irrefl _) ((mem_before_iff_rank_lt jInside).mp inside)
  exact sorted.rel_of_mem_take_of_mem_drop iEarly (mem_drop_of_not_mem_take jInside jLate)

private theorem length_before {order : List Nat} {i : Nat} (inside : i ∈ order) :
    (before order i).length = order.idxOf i := by
  rw [before, List.length_take, Nat.min_eq_left (Nat.le_of_lt (List.idxOf_lt_length inside))]

/-- Actual one-sided rank displacement follows from the local menu count.
The interval hypothesis is the only prime-counting input. -/
theorem rank_displacement_of_far_precedence {value : Nat → Nat} {G w : Nat} {natural order : List Nat}
    (unique : natural.Nodup) (sorted : natural.Pairwise (fun i j => value i < value j))
    (complete : order.Perm natural)
    (intervalCount : ∀ a,
      (natural.filter (fun k => decide (a ≤ value k ∧ value k ≤ a + G))).length ≤ w)
    (precedence : ∀ i ∈ natural, ∀ j ∈ natural, value i + G < value j →
      probeRank order i < probeRank order j) :
    ∀ i ∈ natural, probeRank natural i ≤ probeRank order i + w ∧
      probeRank order i ≤ probeRank natural i + w := by
  intro i iNatural
  have iOrder := complete.mem_iff.mpr iNatural
  let upper := natural.filter (fun j => decide (value i ≤ value j ∧ value j ≤ value i + G))
  let lower := natural.filter (fun j => decide (value i - G ≤ value j ∧ value j ≤ value i - G + G))
  have upperBound : upper.length ≤ w := intervalCount (value i)
  have lowerBound : lower.length ≤ w := intervalCount (value i - G)
  have orderBeforeUnique := (complete.symm.nodup unique).sublist (List.take_sublist (order.idxOf i) order)
  have naturalBeforeUnique := unique.sublist (List.take_sublist (natural.idxOf i) natural)
  have plus : (before order i).length ≤ (before natural i ++ upper).length := by
    apply nodup_length_le_of_subset orderBeforeUnique
    intro j early
    by_cases naturalEarly : j ∈ before natural i
    · exact List.mem_append_left _ naturalEarly
    · have jNatural := complete.mem_iff.mp (List.mem_of_mem_take early)
      have jEarly := (mem_before_iff_rank_lt iOrder).mp early
      have different : i ≠ j := by
        intro equal
        subst j
        exact (Nat.lt_irrefl _) jEarly
      have notEqual : probeRank natural i ≠ probeRank natural j :=
        fun same => different (probeRank_injective_on_order iNatural same)
      have naturalLater : probeRank natural i < probeRank natural j := by
        have notLess : ¬ probeRank natural j < probeRank natural i :=
          fun lt => naturalEarly ((mem_before_iff_rank_lt iNatural).mpr lt)
        omega
      have less := value_lt_of_rank_lt sorted jNatural naturalLater
      have close : value j ≤ value i + G := by
        by_cases within : value j ≤ value i + G
        · exact within
        · have beforeJ := precedence i iNatural j jNatural (by omega)
          omega
      apply List.mem_append_right
      exact List.mem_filter.mpr ⟨jNatural, decide_eq_true ⟨Nat.le_of_lt less, close⟩⟩
  have minus : (before natural i).length ≤ (before order i ++ lower).length := by
    apply nodup_length_le_of_subset naturalBeforeUnique
    intro j early
    by_cases orderEarly : j ∈ before order i
    · exact List.mem_append_left _ orderEarly
    · have jNatural := List.mem_of_mem_take early
      have less := value_lt_of_rank_lt sorted iNatural ((mem_before_iff_rank_lt iNatural).mp early)
      have close : value i - G ≤ value j := by
        by_cases within : value i - G ≤ value j
        · exact within
        · have inverted := precedence j jNatural i iNatural (by omega)
          exact False.elim (orderEarly ((mem_before_iff_rank_lt iOrder).mpr inverted))
      apply List.mem_append_right
      exact List.mem_filter.mpr ⟨jNatural, decide_eq_true ⟨close, by omega⟩⟩
  rw [List.length_append, length_before iOrder, length_before iNatural] at plus minus
  unfold probeRank
  omega

private def indicator (b : Bool) : Int := if b then 1 else 0

private theorem indicator_of_nat (b : Bool) : (b.toNat : Int) = indicator b := by cases b <;> rfl

private theorem indicator_and (a b : Bool) : indicator (a && b) = indicator a * indicator b := by
  cases a <;> cases b <;> decide

/-- The actual nonnegative population containment mass, represented as an integer. -/
def hitMoment (law : List (X × Nat)) (hit : X → Nat → Bool) (hits : List Nat) : Int :=
  total law (fun atom => (atom.2 : Int) * indicator (hits.all (hit atom.1)))

/-- The retained product-kernel contribution to a context, in common scaled units. -/
def referenceKernel (reference : List Nat → Int) (ctx : List Nat) : Int :=
  total (subsetTerms ctx) (fun term => term.2 * reference term.1)

private theorem survival_inclusion_exclusion (hit : Nat → Bool) (ctx : List Nat) :
    total (subsetTerms ctx) (fun term => term.2 * indicator (term.1.all hit)) =
      indicator (survives hit ctx) := by
  induction ctx with
  | nil => simp [subsetTerms, indicator, survives]
  | cons i ctx ih =>
    rw [subsetTerms, total_append, total_map]
    cases hi : hit i
    · simp [hi, indicator, survives, total_zero]
      simpa [indicator, survives] using ih
    · simp only [List.all_cons, hi, Bool.true_and, Int.neg_mul, total_neg, survives,
        Bool.not_true, Bool.false_and, indicator, Bool.false_eq_true, if_false]
      omega

/-- Inclusion–exclusion for the exact mass of a label being the first hit
after the context, using every subset of the common context. -/
theorem hazard_eq_moments (law : List (X × Nat)) (hit : X → Nat → Bool)
    (ctx : List Nat) (i : Nat) :
    (newHitMass law hit ctx i : Int) =
      total (subsetTerms ctx) (fun term => term.2 * hitMoment law hit (i :: term.1)) := by
  unfold newHitMass
  rw [coe_weighted]
  apply Eq.trans (b := total law (fun atom =>
    total (subsetTerms ctx) (fun term => term.2 * ((atom.2 : Int) *
      indicator ((i :: term.1).all (hit atom.1))))))
  · apply total_congr
    intro atom _
    rw [newHit, indicator_of_nat, indicator_and,
      ← survival_inclusion_exclusion (hit atom.1) ctx]
    simp only [Int.mul_assoc, Int.mul_comm (total _ _) (indicator (hit atom.1 i)),
      ← Int.mul_assoc, ← total_left_mul]
    apply total_congr
    intro term _
    rw [List.all_cons, indicator_and]
    ac_rfl
  · rw [total_commute]
    apply total_congr
    intro term _
    rw [total_left_mul]
    rfl

/-- Sum of the available error envelopes across context subsets. -/
def momentBudget (error : Nat → Nat) : Nat → Nat
  | 0 => error 0
  | n + 1 => momentBudget error n + momentBudget (fun k => error (k + 1)) n

private theorem sum_budget_eq_length (error : Nat → Nat) (ctx : List Nat) :
    ((subsetTerms ctx).map (fun term => error term.1.length)).sum = momentBudget error ctx.length := by
  have sumAppend (xs ys : List Nat) : (xs ++ ys).sum = xs.sum + ys.sum := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.cons_append, List.sum_cons, ih, Nat.add_assoc]
  induction ctx generalizing error with
  | nil => simp [subsetTerms, momentBudget]
  | cons x ctx ih =>
    simp only [subsetTerms, List.map_append, sumAppend, List.map_map,
      Function.comp_def, List.length_cons, momentBudget]
    rw [ih error, ih (fun k => error (k + 1))]

private theorem momentBudget_mono_length (error : Nat → Nat) {n m : Nat}
    (order : n ≤ m) : momentBudget error n ≤ momentBudget error m := by
  induction m with
  | zero =>
    have eq : n = 0 := by omega
    simp [eq]
  | succ m ih =>
    by_cases equal : n = m + 1
    · simp [equal]
    · have small : n ≤ m := by omega
      have smaller := ih small
      rw [momentBudget]
      omega

private theorem total_abs_le (xs : List α) (f : α → Int) (budget : α → Nat)
    (rows : ∀ x ∈ xs, (f x).natAbs ≤ budget x) :
    (total xs f).natAbs ≤ (xs.map budget).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [total_cons, List.map_cons, List.sum_cons]
    exact Nat.le_trans (Int.natAbs_add_le ..)
      (Nat.add_le_add (rows x (by simp)) (ih (fun y inside => rows y (by simp [inside]))))

private theorem sign_abs_of_term {ctx : List Nat} {term : List Nat × Int}
    (inside : term ∈ subsetTerms ctx) : term.2.natAbs = 1 := by
  rw [Screening.CostMoments.subset_term_sign inside]
  generalize term.1.length = n
  induction n with
  | zero => rfl
  | succ n ih => simp [Int.pow_succ, Int.natAbs_mul, ih]

/-- A per-degree containment envelope gives a uniform error for a context
hazard. The scale and reference use common integer units. -/
theorem hazard_error_of_moment_bounds (law : List (X × Nat)) (hit : X → Nat → Bool)
    (ctx : List Nat) (i : Nat) (scale reciprocal : Int) (reference : List Nat → Int)
    (error : Nat → Nat)
    (moments : ∀ hs, hs.Sublist ctx →
      (scale * hitMoment law hit (i :: hs) - reciprocal * reference hs).natAbs ≤ error hs.length) :
    (scale * (newHitMass law hit ctx i : Int) - reciprocal * referenceKernel reference ctx).natAbs ≤
      momentBudget error ctx.length := by
  rw [hazard_eq_moments, referenceKernel, ← total_left_mul, ← total_left_mul, ← total_sub,
    ← sum_budget_eq_length error ctx]
  apply total_abs_le
  intro term member
  have factoring :
      scale * (term.2 * hitMoment law hit (i :: term.1)) -
        reciprocal * (term.2 * reference term.1) =
      term.2 * (scale * hitMoment law hit (i :: term.1) - reciprocal * reference term.1) := by
    rw [Int.mul_sub, Int.mul_left_comm scale, Int.mul_left_comm reciprocal]
  rw [factoring, Int.natAbs_mul, sign_abs_of_term member, Nat.one_mul]
  exact moments term.1 (Screening.CostMoments.subset_term_sublist member)

private theorem int_le_of_abs {a : Int} {bound : Nat} (h : a.natAbs ≤ bound) :
    a ≤ (bound : Int) := Int.le_trans Int.le_natAbs (Int.ofNat_le.mpr h)

private theorem neg_le_of_abs {a : Int} {bound : Nat} (h : a.natAbs ≤ bound) :
    -a ≤ (bound : Int) := int_le_of_abs (by simpa using h)

/-- The reciprocal advantage dominates both perturbed hazard intervals. -/
theorem hazard_dominance_of_gap {hi hj E : Nat} {scale qi qj kernel kernelFloor : Int}
    (scalePositive : 0 < scale) (floorNonnegative : 0 ≤ kernelFloor)
    (floor : kernelFloor ≤ kernel)
    (errorI : (scale * (hi : Int) - qi * kernel).natAbs ≤ E)
    (errorJ : (scale * (hj : Int) - qj * kernel).natAbs ≤ E)
    (gap : 2 * (E : Int) < (qi - qj) * kernelFloor) : hj < hi := by
  have reciprocalNonnegative : 0 ≤ qi - qj := by
    by_cases nonneg : 0 ≤ qi - qj
    · exact nonneg
    · have upper := Int.mul_le_mul_of_nonneg_right (show qi - qj ≤ 0 by omega) floorNonnegative
      simp only [Int.zero_mul] at upper
      omega
  have advantage := Int.mul_le_mul_of_nonneg_left floor reciprocalNonnegative
  simp only [Int.sub_mul] at advantage gap
  have leftError := neg_le_of_abs errorI
  have rightError := int_le_of_abs errorJ
  have scaled : scale * (hj : Int) < scale * (hi : Int) := by omega
  by_cases ordered : hj < hi
  · exact ordered
  · have reverse := Int.mul_le_mul_of_nonneg_left (show (hi : Int) ≤ (hj : Int) by omega)
      (Int.le_of_lt scalePositive)
    omega

/-- A strict price gap above G forces a strict scaled reciprocal gap for all
prices in [1, 2P]. This is the integer-cross-multiplied dyadic-band criterion. -/
theorem reciprocal_gap_of_separation {pi pj P G E : Nat} {qi qj units kernelFloor : Int}
    (piPositive : 0 < pi) (pjPositive : 0 < pj) (piUpper : pi ≤ 2 * P) (pjUpper : pj ≤ 2 * P)
    (unitsPositive : 0 < units) (floorPositive : 0 < kernelFloor)
    (reciprocalI : qi * (pi : Int) = units) (reciprocalJ : qj * (pj : Int) = units)
    (threshold : (2 * (E : Int)) * ((2 * (P : Int)) * (2 * (P : Int))) ≤
      (units * kernelFloor) * (G : Int))
    (separated : pi + G < pj) :
    2 * (E : Int) < (qi - qj) * kernelFloor := by
  let product := (pi : Int) * (pj : Int)
  have productNonnegative : 0 ≤ product := Int.mul_nonneg (by omega) (by omega)
  have productBound : product ≤ (2 * (P : Int)) * (2 * (P : Int)) := by
    change (pi : Int) * (pj : Int) ≤ _
    have upI : (pi : Int) ≤ 2 * (P : Int) := by omega
    have upJ : (pj : Int) ≤ 2 * (P : Int) := by omega
    exact Int.mul_le_mul upI upJ (by omega) (by omega)
  have multiplierPositive : 0 < units * kernelFloor := Int.mul_pos unitsPositive floorPositive
  have crossIdentity : (qi - qj) * product = units * ((pj : Int) - (pi : Int)) := by
    change (qi - qj) * ((pi : Int) * (pj : Int)) = _
    calc
      _ = (qi * (pi : Int)) * (pj : Int) - (qj * (pj : Int)) * (pi : Int) := by
        rw [Int.sub_mul]
        congr 1 <;> ac_rfl
      _ = _ := by rw [reciprocalI, reciprocalJ, Int.mul_sub]
  have cross : (2 * (E : Int)) * product < ((qi - qj) * kernelFloor) * product := calc
    _ ≤ (2 * (E : Int)) * ((2 * (P : Int)) * (2 * (P : Int))) :=
      Int.mul_le_mul_of_nonneg_left productBound (by omega)
    _ ≤ (units * kernelFloor) * (G : Int) := threshold
    _ < (units * kernelFloor) * ((pj : Int) - (pi : Int)) :=
      Int.mul_lt_mul_of_pos_left (by omega) multiplierPositive
    _ = _ := by rw [Int.mul_right_comm units, ← crossIdentity, Int.mul_right_comm]
  by_cases desired : 2 * (E : Int) < (qi - qj) * kernelFloor
  · exact desired
  · have reverse := Int.mul_le_mul_of_nonneg_right
      (show (qi - qj) * kernelFloor ≤ 2 * (E : Int) by omega) productNonnegative
    omega

/-- Complete finite precedence certificate from capped or uncapped scaled
containment errors. The supplied kernel floor and interval count are
deterministic inputs, with no probability or asymptotic assumptions. -/
theorem arithmetic_optimum_window (law : List (X × Nat)) (hit : X → Nat → Bool)
    (fallback : Nat) {natural order : List Nat} (value : Nat → Nat)
    (reciprocal : Nat → Int) (reference : List Nat → Int) (error : Nat → Nat)
    (scale units kernelFloor : Int) (P G w : Nat)
    (scalePositive : 0 < scale) (unitsPositive : 0 < units) (floorPositive : 0 < kernelFloor)
    (unique : natural.Nodup) (sorted : natural.Pairwise (fun i j => value i < value j))
    (optimal : CompleteOptimum law hit fallback natural order)
    (prices : ∀ i ∈ natural, 0 < value i ∧ value i ≤ 2 * P ∧
      reciprocal i * (value i : Int) = units)
    (momentBounds : ∀ i ∈ natural, ∀ hs, hs.Nodup → (∀ k ∈ hs, k ∈ natural) → i ∉ hs →
      (scale * hitMoment law hit (i :: hs) - reciprocal i * reference hs).natAbs ≤ error hs.length)
    (kernelBound : ∀ ctx, ctx.Nodup → (∀ k ∈ ctx, k ∈ natural) →
      kernelFloor ≤ referenceKernel reference ctx)
    (threshold : (2 * (momentBudget error natural.length : Int)) *
      ((2 * (P : Int)) * (2 * (P : Int))) ≤ (units * kernelFloor) * (G : Int))
    (intervalCount : ∀ a,
      (natural.filter (fun k => decide (a ≤ value k ∧ value k ≤ a + G))).length ≤ w) :
    (∀ i ∈ natural, ∀ j ∈ natural, value i + G < value j →
      probeRank order i < probeRank order j) ∧
    (∀ i ∈ natural, probeRank natural i ≤ probeRank order i + w ∧
      probeRank order i ≤ probeRank natural i + w) := by
  have precedes : ∀ i ∈ natural, ∀ j ∈ natural, value i + G < value j →
      probeRank order i < probeRank order j := by
    intro i insideI j insideJ separated
    have distinct : i ≠ j := by intro eq; subst j; omega
    obtain ⟨pi, upperI, inverseI⟩ := prices i insideI
    obtain ⟨pj, upperJ, inverseJ⟩ := prices j insideJ
    have advantage := reciprocal_gap_of_separation pi pj upperI upperJ
      unitsPositive floorPositive inverseI inverseJ threshold separated
    apply optimum_respects_context_dominance law hit fallback unique optimal insideI distinct
    intro ctx ctxUnique kept missingI missingJ
    have budget := momentBudget_mono_length error (nodup_length_le_of_subset ctxUnique kept)
    have localError (k : Nat) (present : k ∈ natural) (missing : k ∉ ctx) :=
      hazard_error_of_moment_bounds law hit ctx k scale (reciprocal k) reference error
        (fun hs part => momentBounds k present hs (ctxUnique.sublist part)
          (fun t ht => kept t (part.subset ht)) (fun hk => missing (part.subset hk)))
    exact hazard_dominance_of_gap scalePositive (Int.le_of_lt floorPositive)
      (kernelBound ctx ctxUnique kept) (Nat.le_trans (localError i insideI missingI) budget)
      (Nat.le_trans (localError j insideJ missingJ) budget) advantage
  exact ⟨precedes, rank_displacement_of_far_precedence unique sorted optimal.1 intervalCount precedes⟩

private theorem atom_append_balance (hit : Nat → Bool) (fallback : Nat)
    (order : List Nat) (i : Nat) :
    scan hit fallback (order ++ [i]) + fallback * newHit hit order i =
      scan hit fallback order + (survives hit order).toNat := by
  induction order with
  | nil => cases h : hit i <;> simp [scan, newHit, survives, h, Nat.add_comm]
  | cons j order ih =>
    cases h : hit j
    · simpa [scan, newHit, survives, h, Nat.add_assoc] using congrArg (fun n : Nat => 1 + n) ih
    · simp [scan, newHit, survives, h]

theorem append_cost_difference (law : List (X × Nat)) (hit : X → Nat → Bool)
    (fallback : Nat) (order : List Nat) (i : Nat) :
    (populationCost law hit fallback (order ++ [i]) : Int) -
      (populationCost law hit fallback order : Int) =
    (Screening.ScreeningCost.survivalMass law hit order : Int) -
      (fallback : Int) * (newHitMass law hit order i : Int) := by
  simp only [populationCost, Screening.ScreeningCost.survivalMass, newHitMass, coe_weighted,
    ← total_left_mul, ← total_sub]
  apply total_congr
  intro atom _
  have balance := congrArg (fun n : Nat => (n : Int))
    (atom_append_balance (hit atom.1) fallback order i)
  simp only [Int.ofNat_add, Int.ofNat_mul] at balance
  simp only [← Int.mul_sub, Int.mul_left_comm (fallback : Int)]
  congr 1
  omega

/-- The mass belonging only to the specified label among all menu labels. -/
def singletonMass (law : List (X × Nat)) (hit : X → Nat → Bool) (menu : List Nat)
    (i : Nat) : Nat :=
  newHitMass law hit (menu.filter (fun j => !(j == i))) i

/-- Total (unnormalized) number of population tickets. -/
def totalMass (law : List (X × Nat)) : Nat := (law.map Prod.snd).sum

private theorem weighted_mono (law : List (X × Nat)) (f g : X → Nat)
    (h : ∀ x, f x ≤ g x) :
    Screening.ScreeningCost.weighted law f ≤ Screening.ScreeningCost.weighted law g := by
  induction law with
  | nil => exact Nat.le_refl 0
  | cons atom law ih =>
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (h atom.1)) ih

private theorem newHit_of_subset {hit : Nat → Bool} {small large : List Nat} {i : Nat}
    (inside : ∀ j ∈ small, j ∈ large) :
    newHit hit large i ≤ newHit hit small i := by
  unfold newHit
  cases found : (survives hit large && hit i) with
  | false => simp
  | true =>
    obtain ⟨largeMiss, hitI⟩ := Bool.and_eq_true_iff.mp found
    have smallMiss : survives hit small = true :=
      List.all_eq_true.mpr (fun j member => List.all_eq_true.mp largeMiss j (inside j member))
    simp [smallMiss, hitI]

private theorem survival_le_total (law : List (X × Nat)) (hit : X → Nat → Bool)
    (order : List Nat) :
    Screening.ScreeningCost.survivalMass law hit order ≤ totalMass law := by
  have expansion : Screening.ScreeningCost.weighted law (fun _ => 1) = totalMass law := by
    induction law with
    | nil => rfl
    | cons atom law ih =>
      change atom.2 * 1 + Screening.ScreeningCost.weighted law (fun _ => 1) =
        atom.2 + totalMass law
      simp [ih]
  rw [← expansion]
  exact weighted_mono _ _ _ (fun x => by cases survives (hit x) order <;> decide)

theorem append_improves_if_singleton (law : List (X × Nat)) (hit : X → Nat → Bool)
    (fallback : Nat) {menu order : List Nat} {i : Nat}
    (allowed : ∀ j ∈ order, j ∈ menu) (omitted : i ∉ order)
    (enough : totalMass law < fallback * singletonMass law hit menu i) :
    populationCost law hit fallback (order ++ [i]) < populationCost law hit fallback order := by
  have contains : ∀ j ∈ order, j ∈ menu.filter (fun j => !(j == i)) := by
    intro j member
    have distinct : j ≠ i := fun equal => omitted (equal ▸ member)
    exact List.mem_filter.mpr ⟨allowed j member, by simp [distinct]⟩
  have hazard : singletonMass law hit menu i ≤ newHitMass law hit order i :=
    weighted_mono _ _ _ (fun _ => newHit_of_subset contains)
  have lower := Nat.mul_le_mul_left fallback hazard
  have upper := survival_le_total law hit order
  have costs := append_cost_difference law hit fallback order i
  rw [← Int.ofNat_mul] at costs
  omega

/-- An optimum among all lists of distinct menu-label tests, including trials
that omit some of the menu. -/
def MenuOptimum (law : List (X × Nat)) (hit : X → Nat → Bool) (fallback : Nat)
    (menu order : List Nat) : Prop :=
  order.Nodup ∧ (∀ j ∈ order, j ∈ menu) ∧
    ∀ candidate, candidate.Nodup → (∀ j ∈ candidate, j ∈ menu) →
      populationCost law hit fallback order ≤ populationCost law hit fallback candidate

private theorem count_one_of_nodup {xs : List Nat} {i : Nat} (unique : xs.Nodup)
    (inside : i ∈ xs) : xs.count i = 1 := by
  induction xs with
  | nil => simp at inside
  | cons j xs ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp unique
    by_cases equal : i = j
    · subst j
      simp [List.count_cons, List.count_eq_zero.mpr fresh]
    · have member : i ∈ xs := (List.mem_cons.mp inside).resolve_left equal
      simp [List.count_cons, Ne.symm equal, ih rest member]

/-- A singleton-exclusive hit mass above total mass divided by fallback
forces every optimum to include all the menu tests. -/
theorem menu_optimum_complete_of_singletons (law : List (X × Nat)) (hit : X → Nat → Bool)
    (fallback : Nat) {menu order : List Nat} (unique : menu.Nodup)
    (optimal : MenuOptimum law hit fallback menu order)
    (singletons : ∀ i ∈ menu, totalMass law < fallback * singletonMass law hit menu i) :
    CompleteOptimum law hit fallback menu order := by
  obtain ⟨orderUnique, allowed, minimum⟩ := optimal
  have complete : ∀ i ∈ menu, i ∈ order := by
    intro i present
    by_cases included : i ∈ order
    · exact included
    · have improved := append_improves_if_singleton law hit fallback allowed included (singletons i present)
      have uniqueAppend : (order ++ [i]).Nodup := by
        unfold List.Nodup
        rw [List.pairwise_append]
        refine ⟨orderUnique, by simp, ?_⟩
        intro a already b added equal
        have eq : b = i := by simpa using added
        exact included (eq ▸ equal ▸ already)
      have attach : ∀ j ∈ order ++ [i], j ∈ menu := by
        intro j member
        rcases List.mem_append.mp member with previous | added
        · exact allowed j previous
        · have equal : j = i := by simpa using added
          exact equal ▸ present
      exact False.elim ((Nat.not_le_of_gt improved) (minimum _ uniqueAppend attach))
  have permutation : order.Perm menu := by
    apply List.perm_iff_count.mpr
    intro i
    by_cases inside : i ∈ menu
    · rw [count_one_of_nodup orderUnique (complete i inside), count_one_of_nodup unique inside]
    · rw [List.count_eq_zero.mpr inside, List.count_eq_zero.mpr (fun h => inside (allowed i h))]
  exact ⟨permutation, fun candidate perm => minimum candidate
    (perm.symm.nodup unique) (fun j member => perm.mem_iff.mp member)⟩

private def productOf (factor : Nat → Int) : List Nat → Int
  | [] => 1
  | i :: rest => factor i * productOf factor rest

/-- A degree-capped product moment. The denominator of each retained
degree is widened to the common scale s^cap. -/
def truncatedProductMoment (reciprocal : Nat → Int) (s : Int) (cap : Nat) (hs : List Nat) : Int :=
  if hs.length ≤ cap then s ^ (cap - hs.length) * productOf reciprocal hs else 0

/-- The actual alternating, truncated reference product for a context. -/
def truncatedProductKernel (reciprocal : Nat → Int) (s : Int) (cap : Nat) (ctx : List Nat) : Int :=
  referenceKernel (truncatedProductMoment reciprocal s cap) ctx

private theorem truncated_moment_cons (q : Nat → Int) (s : Int) (r i : Nat) (hs : List Nat) :
    truncatedProductMoment q s (r + 1) (i :: hs) = q i * truncatedProductMoment q s r hs := by
  by_cases degree : hs.length ≤ r
  · have nextDegree : (i :: hs).length ≤ r + 1 := by simpa using degree
    have exponent : r + 1 - (i :: hs).length = r - hs.length := by simp
    simp only [truncatedProductMoment, nextDegree, degree, if_true, exponent, productOf]
    ac_rfl
  · have nextDegree : ¬(i :: hs).length ≤ r + 1 := by simpa using degree
    simp [truncatedProductMoment, nextDegree, degree]

private theorem truncated_kernel_nil (q : Nat → Int) (s : Int) (r : Nat) :
    truncatedProductKernel q s r [] = s ^ r := by
  simp [truncatedProductKernel, referenceKernel, subsetTerms, truncatedProductMoment, productOf]

private theorem truncated_kernel_zero (q : Nat → Int) (s : Int) (ctx : List Nat) :
    truncatedProductKernel q s 0 ctx = 1 := by
  induction ctx with
  | nil => simp [truncated_kernel_nil]
  | cons i ctx ih =>
    unfold truncatedProductKernel referenceKernel at ih ⊢
    rw [subsetTerms, total_append, total_map, ih]
    simp [truncatedProductMoment, total_zero]

private theorem truncated_kernel_cons (q : Nat → Int) (s : Int) (r i : Nat) (ctx : List Nat) :
    truncatedProductKernel q s (r + 1) (i :: ctx) =
      truncatedProductKernel q s (r + 1) ctx - q i * truncatedProductKernel q s r ctx := by
  unfold truncatedProductKernel referenceKernel
  rw [subsetTerms, total_append, total_map]
  have tail :
      total (subsetTerms ctx) (fun term =>
        -term.2 * truncatedProductMoment q s (r + 1) (i :: term.1)) =
      -(q i * total (subsetTerms ctx) (fun term => term.2 * truncatedProductMoment q s r term.1)) := by
    rw [← total_left_mul, ← total_neg]
    apply total_congr
    intro term _
    rw [truncated_moment_cons, Int.neg_mul]
    congr 1
    ac_rfl
  rw [tail]
  omega

/-- The truncated product kernel lies between 0 and its constant term.
For positive cutoff its lower bound is the constant term minus degree one.
Only the sum of the nonnegative reciprocal numerators must be at most s. -/
theorem truncated_product_kernel_bounds (q : Nat → Int) (s : Int) (ctx : List Nat)
    (sNonnegative : 0 ≤ s) (nonnegative : ∀ i ∈ ctx, 0 ≤ q i)
    (small : total ctx q ≤ s) (r : Nat) :
    0 ≤ truncatedProductKernel q s r ctx ∧ truncatedProductKernel q s r ctx ≤ s ^ r ∧
      (0 < r → s ^ r - total ctx q * s ^ (r - 1) ≤ truncatedProductKernel q s r ctx) := by
  induction ctx generalizing r with
  | nil =>
    rw [truncated_kernel_nil, total_nil, Int.zero_mul, Int.sub_zero]
    exact ⟨Int.pow_nonneg sNonnegative, Int.le_refl _, fun _ => Int.le_refl _⟩
  | cons i ctx ih =>
    have head : 0 ≤ q i := nonnegative i (by simp)
    have tailNonnegative : ∀ j ∈ ctx, 0 ≤ q j :=
      fun j hj => nonnegative j (List.mem_cons_of_mem _ hj)
    have tailSmall : total ctx q ≤ s := by simp only [total_cons] at small; omega
    cases r with
    | zero => simp [truncated_kernel_zero]
    | succ r =>
      obtain ⟨previousNonnegative, previousUpper, _⟩ := ih tailNonnegative tailSmall r
      obtain ⟨_, currentUpper, currentLower⟩ := ih tailNonnegative tailSmall (r + 1)
      have previousGe : 0 ≤ q i * truncatedProductKernel q s r ctx :=
        Int.mul_nonneg head previousNonnegative
      have previousLe := Int.mul_le_mul_of_nonneg_left previousUpper head
      have low :
          s ^ (r + 1) - (q i + total ctx q) * s ^ r ≤
            truncatedProductKernel q s (r + 1) ctx - q i * truncatedProductKernel q s r ctx := by
        have prior := currentLower (by omega)
        simp only [Nat.add_sub_cancel] at prior
        rw [Int.add_mul]
        omega
      have lowNonnegative : 0 ≤ s ^ (r + 1) - (q i + total ctx q) * s ^ r := by
        have headTail : q i + total ctx q ≤ s := by simpa using small
        have product := Int.mul_le_mul_of_nonneg_right headTail
          (Int.pow_nonneg (m := r) sNonnegative)
        rw [Int.pow_succ, Int.mul_comm (s ^ r) s]
        omega
      rw [truncated_kernel_cons]
      refine ⟨by omega, by omega, ?_⟩
      intro _
      simpa only [total_cons, Nat.add_sub_cancel] using low

private theorem total_le_length_mul (q : Nat → Int) (ctx : List Nat) (Q : Int)
    (bounded : ∀ i ∈ ctx, q i ≤ Q) : total ctx q ≤ (ctx.length : Int) * Q := by
  induction ctx with
  | nil => simp
  | cons i ctx ih =>
    have tail := ih (fun j member => bounded j (by simp [member]))
    have head := bounded i (by simp)
    simp only [total_cons, List.length_cons, Int.ofNat_add, Int.ofNat_one, Int.add_mul, Int.one_mul]
    omega

/-- A bounded reciprocal numerator and a bound on the context size provide
a uniform explicit kernel floor, the finite form of the paper's 1−m/P bound. -/
theorem truncated_product_kernel_floor (q : Nat → Int) (s Q : Int) (r m : Nat)
    (ctx : List Nat) (sNonnegative : 0 ≤ s) (maxNonnegative : 0 ≤ Q)
    (bounded : ∀ i ∈ ctx, 0 ≤ q i ∧ q i ≤ Q) (size : ctx.length ≤ m)
    (small : (m : Int) * Q ≤ s) :
    s ^ (r + 1) - ((m : Int) * Q) * s ^ r ≤ truncatedProductKernel q s (r + 1) ctx := by
  have totalBound := total_le_length_mul q ctx Q (fun i member => (bounded i member).2)
  have sizeBound := Int.mul_le_mul_of_nonneg_right (show (ctx.length : Int) ≤ (m : Int) by omega)
    maxNonnegative
  have upper := Int.le_trans totalBound sizeBound
  have fits := Int.le_trans upper small
  have kth := (truncated_product_kernel_bounds q s ctx sNonnegative
    (fun i member => (bounded i member).1) fits (r + 1)).2.2 (by omega)
  have widened := Int.mul_le_mul_of_nonneg_right upper (Int.pow_nonneg (m := r) sNonnegative)
  simp only [Nat.add_sub_cancel] at kth
  omega

/-- Finite weighted hit-cap convention in the same units as the scan. -/
def PopulationHitCap (menu : List Nat) (h : Nat) (law : List (X × Nat))
    (hit : X → Nat → Bool) : Prop :=
  ∀ atom ∈ law, (menu.filter (hit atom.1)).length ≤ h

private theorem hitMoment_zero_above_cap {menu hits : List Nat} {h : Nat} {law : List (X × Nat)}
    {hit : X → Nat → Bool} (cap : PopulationHitCap menu h law hit)
    (unique : hits.Nodup) (allowed : ∀ i ∈ hits, i ∈ menu) (above : h < hits.length) :
    hitMoment law hit hits = 0 := by
  unfold hitMoment
  rw [← total_zero law]
  apply total_congr
  intro atom present
  cases all : hits.all (hit atom.1) with
  | false => simp [all, indicator]
  | true =>
    have found := List.all_eq_true.mp all
    have upper := nodup_length_le_of_subset unique
      (fun i seen => List.mem_filter.mpr ⟨allowed i seen, found i seen⟩)
    have lower := cap atom present
    omega

/-- A moment extending a context subset of size below the cutoff has the
rounding error, one at the cutoff has the top error, and others vanish. -/
def cappedDegreeError (cutoff rounded top : Nat) (degree : Nat) : Nat :=
  if degree < cutoff then rounded else if degree = cutoff then top else 0

/-- Finite natural-window certificate with the paper's separate rounded and
top containment tolerances. It certifies completion, strict precedence
outside G, and rank displacement from the counted local width. -/
theorem truncated_arithmetic_optimum_window (law : List (X × Nat)) (hit : X → Nat → Bool)
    (fallback : Nat) {natural order : List Nat} (value : Nat → Nat) (reciprocal : Nat → Int)
    (scale units qMax : Int) (P G w r rounded top : Nat)
    (scalePositive : 0 < scale) (unitsPositive : 0 < units) (qMaxNonnegative : 0 ≤ qMax)
    (small : (natural.length : Int) * qMax < units)
    (unique : natural.Nodup) (sorted : natural.Pairwise (fun i j => value i < value j))
    (optimal : MenuOptimum law hit fallback natural order)
    (singletons : ∀ i ∈ natural, totalMass law < fallback * singletonMass law hit natural i)
    (prices : ∀ i ∈ natural, 0 < value i ∧ value i ≤ 2 * P ∧
      reciprocal i * (value i : Int) = units)
    (numerators : ∀ i ∈ natural, 0 ≤ reciprocal i ∧ reciprocal i ≤ qMax)
    (cap : PopulationHitCap natural (r + 2) law hit)
    (moments : ∀ i ∈ natural, ∀ hs, hs.Nodup → (∀ k ∈ hs, k ∈ natural) → i ∉ hs →
      hs.length ≤ r + 1 →
      (scale * hitMoment law hit (i :: hs) -
        reciprocal i * truncatedProductMoment reciprocal units (r + 1) hs).natAbs ≤
        if hs.length < r + 1 then rounded else top)
    (threshold : (2 * (momentBudget (cappedDegreeError (r + 1) rounded top) natural.length : Int)) *
      ((2 * (P : Int)) * (2 * (P : Int))) ≤
      (units * (units ^ (r + 1) - ((natural.length : Int) * qMax) * units ^ r)) * (G : Int))
    (intervalCount : ∀ a,
      (natural.filter (fun k => decide (a ≤ value k ∧ value k ≤ a + G))).length ≤ w) :
    CompleteOptimum law hit fallback natural order ∧
    (∀ i ∈ natural, ∀ j ∈ natural, value i + G < value j →
      probeRank order i < probeRank order j) ∧
    (∀ i ∈ natural, probeRank natural i ≤ probeRank order i + w ∧
      probeRank order i ≤ probeRank natural i + w) := by
  let floor := units ^ (r + 1) - ((natural.length : Int) * qMax) * units ^ r
  have floorPositive : 0 < floor := by
    unfold floor
    rw [Int.pow_succ, Int.mul_comm (units ^ r) units, ← Int.sub_mul]
    exact Int.mul_pos (by omega) (Int.pow_pos unitsPositive)
  have complete := menu_optimum_complete_of_singletons law hit fallback unique optimal singletons
  refine ⟨complete, arithmetic_optimum_window law hit fallback value reciprocal
    (truncatedProductMoment reciprocal units (r + 1)) (cappedDegreeError (r + 1) rounded top)
    scale units floor P G w scalePositive unitsPositive floorPositive unique sorted complete
    prices ?_ ?_ threshold intervalCount⟩
  · intro i present hs hsUnique hsAllowed notIn
    by_cases degree : hs.length ≤ r + 1
    · have bounds := moments i present hs hsUnique hsAllowed notIn degree
      by_cases low : hs.length < r + 1
      · simpa [cappedDegreeError, low] using bounds
      · have topDegree : hs.length = r + 1 := by omega
        simpa [cappedDegreeError, low, topDegree] using bounds
    · have above : r + 2 < (i :: hs).length := by simp; omega
      have largeCell := hitMoment_zero_above_cap cap (List.nodup_cons.mpr ⟨notIn, hsUnique⟩)
        (fun j member => (List.mem_cons.mp member).elim (fun eq => eq ▸ present) (hsAllowed j)) above
      have modelZero : truncatedProductMoment reciprocal units (r + 1) hs = 0 := by
        simp [truncatedProductMoment, degree]
      rw [largeCell, modelZero]
      simp
  · intro ctx ctxUnique ctxAllowed
    exact truncated_product_kernel_floor reciprocal units qMax r natural.length ctx
      (Int.le_of_lt unitsPositive) qMaxNonnegative
      (fun i present => numerators i (ctxAllowed i present))
      (nodup_length_le_of_subset ctxUnique ctxAllowed) (Int.le_of_lt small)

/-- The paper's literal interval of odd words provides the population hit cap. -/
theorem odd_word_population_hit_cap {natural : List Nat} (value : Nat → Nat)
    (law : List (Nat × Nat)) {L P h : Nat}
    (sorted : natural.Pairwise (fun i j => value i < value j))
    (prime : ∀ i ∈ natural, Screening.IntervalCounts.IsPrime (value i))
    (low : ∀ i ∈ natural, P ≤ value i) (pPositive : 0 < P) (window : 4 * L < P ^ (h + 1))
    (support : ∀ atom ∈ law, atom.1 < L) :
    PopulationHitCap natural h law (fun k i => decide (value i ∣ Screening.IntervalCounts.word L k)) := by
  intro atom member
  have unique : (natural.map value).Nodup :=
    List.pairwise_map.mpr (sorted.imp Nat.ne_of_lt)
  have cap := Screening.IntervalCounts.natural_window_hit_cap (support atom member)
    pPositive window (natural.map value) unique
    (fun p present => by obtain ⟨i, inside, rfl⟩ := List.mem_map.mp present; exact prime i inside)
    (fun p present => by obtain ⟨i, inside, rfl⟩ := List.mem_map.mp present; exact low i inside)
  simpa only [List.filter_map, List.length_map, Function.comp_def] using cap

/-- The local rank bound becomes the global displacement hypothesis of the
surrogate lemma when labels are numbered 1 through m. -/
theorem canonical_window_displacement {order : List Nat} {m w : Nat}
    (complete : order.Perm (List.range' 1 m))
    (rankBound : ∀ i ∈ List.range' 1 m,
      probeRank (List.range' 1 m) i ≤ probeRank order i + w ∧
      probeRank order i ≤ probeRank (List.range' 1 m) i + w) :
    Screening.LargestHits.Displacement (Screening.CostMoments.extendedProbeRank order) w := by
  apply Screening.CostMoments.extendedProbeRank_displacement
  intro i inOrder
  have inMenu := complete.mem_iff.mp inOrder
  have bound := rankBound i inMenu
  rwa [Screening.CostMoments.natural_probeRank inMenu] at bound

/-- Convert the nonnegative population-cost weights into the signed finite
law representation used by the centered-moment surrogate theorem. -/
theorem populationCost_eq_signed_cost (law : List (X × Nat)) (hit : X → Nat → Bool)
    (fallback : Nat) (order : List Nat) :
    (populationCost law hit fallback order : Int) =
      Screening.CostMoments.finiteCost (law.map (fun atom => (atom.1, (atom.2 : Int))))
        hit fallback order := by
  unfold populationCost Screening.CostMoments.finiteCost
  rw [coe_weighted]
  change _ = total (law.map _) _
  rw [total_map]

private theorem indicator_nonnegative (b : Bool) : 0 ≤ indicator b := by
  cases b <;> decide

private theorem atom_singleton_union (hit : Nat → Bool) (i : Nat) (ctx : List Nat) :
    indicator (hit i) ≤ (newHit hit ctx i : Int) +
      total ctx (fun j => indicator (hit i && hit j)) := by
  induction ctx with
  | nil => simp [newHit, survives, indicator_of_nat]
  | cons j ctx ih =>
    cases hi : hit i
    · simp [hi, indicator, newHit, total_zero]
    · cases hj : hit j
      · simpa [hi, hj, newHit, survives, indicator, indicator_of_nat] using ih
      · have nonnegative := total_nonnegative ctx (fun k => indicator (hit k))
          (fun k _ => indicator_nonnegative (hit k))
        simp [hi, hj, newHit, survives, indicator] at nonnegative ⊢
        omega

/-- The union bound on actual ticket counts for the singleton-exclusive mass. -/
theorem singleton_lower_of_pair_moments (law : List (X × Nat)) (hit : X → Nat → Bool)
    (menu : List Nat) (i : Nat) :
    hitMoment law hit [i] ≤ (singletonMass law hit menu i : Int) +
      total (menu.filter (fun j => !(j == i))) (fun j => hitMoment law hit [i, j]) := by
  let peers := menu.filter (fun j => !(j == i))
  let individual := fun (a : X × Nat) => (a.2 : Int) * indicator (hit a.1 i)
  let single := fun (a : X × Nat) => (a.2 : Int) * (newHit (hit a.1) peers i : Int)
  let pairs := fun (a : X × Nat) => (a.2 : Int) *
    total peers (fun j => indicator (hit a.1 i && hit a.1 j))
  have lower := total_nonnegative law (fun a => single a + pairs a - individual a) (by
    intro atom _
    unfold single pairs individual
    dsimp only
    have mono := Int.mul_le_mul_of_nonneg_left (atom_singleton_union (hit atom.1) i peers)
      (show 0 ≤ (atom.2 : Int) by omega)
    rw [Int.mul_add] at mono
    omega)
  rw [total_sub, total_add] at lower
  have left : total law individual = hitMoment law hit [i] := by
    unfold individual hitMoment
    simp only [List.all_cons, List.all_nil, Bool.and_true]
  have middle : total law single = (singletonMass law hit menu i : Int) := by
    unfold singletonMass newHitMass
    rw [coe_weighted]
  have right : total law pairs = total peers (fun j => hitMoment law hit [i, j]) := by
    unfold pairs
    simp only [← total_left_mul]
    rw [total_commute]
    apply total_congr
    intro j _
    unfold hitMoment
    simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [left, middle, right] at lower
  change _ ≤ _ + total peers _
  omega

/-- A uniform pair-moment upper envelope and singleton-marginal lower
envelope give the exact finite threshold for appending a missing probe. -/
theorem singleton_threshold_of_pair_envelope (law : List (X × Nat)) (hit : X → Nat → Bool)
    (menu : List Nat) (i fallback : Nat) (singleLower pairUpper : Int)
    (nonnegative : 0 ≤ pairUpper)
    (single : singleLower ≤ hitMoment law hit [i])
    (pairs : ∀ j ∈ menu, j ≠ i → hitMoment law hit [i, j] ≤ pairUpper)
    (threshold : (totalMass law : Int) <
      (fallback : Int) * (singleLower - (menu.length : Int) * pairUpper)) :
    totalMass law < fallback * singletonMass law hit menu i := by
  let peers := menu.filter (fun j => !(j == i))
  have pairBound := total_le_length_mul (fun j => hitMoment law hit [i, j]) peers pairUpper (by
    intro j member
    obtain ⟨inMenu, distinct⟩ := List.mem_filter.mp member
    exact pairs j inMenu (by simpa using distinct))
  have peerCount : peers.length ≤ menu.length := List.length_filter_le _ _
  have uniformBound := Int.mul_le_mul_of_nonneg_right
    (show (peers.length : Int) ≤ (menu.length : Int) by omega) nonnegative
  have residual := singleton_lower_of_pair_moments law hit menu i
  change _ ≤ _ + total peers _ at residual
  have enough : singleLower - (menu.length : Int) * pairUpper ≤
      (singletonMass law hit menu i : Int) := by omega
  have scaled := Int.mul_le_mul_of_nonneg_left enough (show 0 ≤ (fallback : Int) by omega)
  rw [← Int.ofNat_mul] at scaled
  omega

end Screening.NaturalWindow

/- Source module: Screening.WitnessOverlap -/

/-! Counting signed perturbations that can change one exact hit cell.
Edges use the order inherited from a common menu of distinct tests. -/

namespace Screening.WitnessOverlap

private theorem filter_support [DecidableEq V] {xs menu : List V}
    (sub : xs.Sublist menu) (unique : menu.Nodup) :
    menu.filter (fun x => decide (x ∈ xs)) = xs := by
  induction sub with
  | slnil => rfl
  | @cons xs rest v sub ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    have absent : v ∉ xs := fun h => fresh (sub.subset h)
    simpa [List.filter_cons, absent] using ih tail
  | @cons₂ xs rest v sub ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    have agree : rest.filter (fun z => decide (z ∈ v::xs)) =
        rest.filter (fun z => decide (z ∈ xs)) := by
      apply List.filter_congr
      intro z hz
      have ne : z ≠ v := fun eq => fresh (eq ▸ hz)
      simp [ne]
    simp only [List.filter_cons, List.mem_cons_self, decide_true, if_true, agree, ih tail]

def residual [DecidableEq V] (cell edge : List V) := edge.filter (fun x => !decide (x ∈ cell))

/-- Canonical sublists of a duplicate-free menu are determined by membership. -/
theorem canonical_ext [DecidableEq V] {menu e f : List V} (unique : menu.Nodup)
    (em : e.Sublist menu) (fm : f.Sublist menu) (ef : e ⊆ f) (fe : f ⊆ e) : e = f := by
  calc
    e = _ := (filter_support em unique).symm
    _ = _ := List.filter_congr (fun x _ => by
      simp only [show x∈e ↔ x∈f from ⟨fun h => ef h, fun h => fe h⟩])
    _ = f := filter_support fm unique

private theorem residual_length [DecidableEq V] {cell edge : List V}
    (sub : cell.Sublist edge) (unique : edge.Nodup) :
    (residual cell edge).length = edge.length - cell.length := by
  have h := (List.filter_append_perm (fun x => decide (x ∈ cell)) edge).length_eq
  rw [List.length_append, filter_support sub unique] at h
  unfold residual
  omega

private theorem residual_injective [DecidableEq V] {menu cell e f : List V}
    (menuUnique : menu.Nodup) (em : e.Sublist menu) (fm : f.Sublist menu)
    (ce : cell.Sublist e) (cf : cell.Sublist f)
    (same : residual cell e = residual cell f) : e = f := by
  have support (x : V) : x ∈ e ↔ x ∈ f := by
    by_cases hc : x ∈ cell
    · exact ⟨fun _ => cf.subset hc, fun _ => ce.subset hc⟩
    · have h : x ∈ residual cell e ↔ x ∈ residual cell f := by rw [same]
      simpa [residual, hc] using h
  calc
    e = _ := (filter_support em menuUnique).symm
    _ = _ := List.filter_congr (fun x _ => by simp only [support x])
    _ = f := filter_support fm menuUnique

private def tuples (menu : List V) : Nat → List (List V)
  | 0 => [[]]
  | k+1 => menu.flatMap (fun x => (tuples menu k).map (x :: ·))

private theorem flat_length (xs : List A) (f : A → List B) (n : Nat)
    (h : ∀ x ∈ xs, (f x).length = n) : (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx])), Nat.succ_mul, Nat.add_comm]

private theorem tuples_length (menu : List V) (k : Nat) :
    (tuples menu k).length = menu.length^k := by
  induction k with
  | zero => simp [tuples]
  | succ k ih => rw [tuples, flat_length _ _ (menu.length^k) (by simp [ih]),
      Nat.pow_succ, Nat.mul_comm]

private theorem mem_tuples (menu xs : List V) (within : xs ⊆ menu) :
    xs ∈ tuples menu xs.length := by
  induction xs with
  | nil => simp [tuples]
  | cons x xs ih =>
    apply List.mem_flatMap.mpr
    exact ⟨x, within (by simp), List.mem_map.mpr
      ⟨xs, ih (fun _ hx => within (List.mem_cons_of_mem x hx)), rfl⟩⟩

theorem length_le_of_subset [DecidableEq A] {xs ys : List A} (unique : xs.Nodup)
    (sub : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨left, right, rfl⟩ := List.append_of_mem (sub (by simp : a ∈ a :: xs))
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    have hs : xs ⊆ left ++ right := by
      intro z hz
      have ne : z ≠ a := fun eq => fresh (eq ▸ hz)
      have all := sub (List.mem_cons_of_mem a hz)
      simpa [List.mem_append, ne] using all
    have bound := ih tail hs
    simp only [List.length_append, List.length_cons] at bound ⊢
    omega

private theorem map_unique (xs : List A) (f : A → B) (unique : xs.Nodup)
    (inj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨b,hb,he⟩ := List.mem_map.mp h
      exact fresh ((inj b (by simp [hb]) a (by simp) he) ▸ hb)
    · exact ih tail (fun x hx y hy => inj x (by simp [hx]) y (by simp [hy]))

/-- Each h-edge containing a j-cell is encoded injectively by its other h−j
vertices, a tuple of menu entries. The bound is valid for every subfamily
of the complete family of canonical h-edges, including signed subfamilies. -/
theorem overlap_bound [DecidableEq V] (menu cell : List V) (edges : List (List V)) (h : Nat)
    (menuUnique : menu.Nodup) (edgeUnique : edges.Nodup)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (size : ∀ e ∈ edges, e.length = h) :
    edges.countP (fun e => decide (cell.Sublist e)) ≤ menu.length^(h-cell.length) := by
  let candidates := edges.filter (fun e => decide (cell.Sublist e))
  have info {e : List V} (he : e ∈ candidates) : e ∈ edges ∧ cell.Sublist e := by
    simpa [candidates] using he
  have uniqueC : candidates.Nodup := edgeUnique.filter _
  have codesUnique := map_unique candidates (residual cell) uniqueC
    (fun e he f hf => residual_injective menuUnique
      (canonical e (info he).1) (canonical f (info hf).1) (info he).2 (info hf).2)
  have sub : candidates.map (residual cell) ⊆ tuples menu (h-cell.length) := by
    intro t ht
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ht
    obtain ⟨inside, hasCell⟩ := info he
    have inc := canonical e inside
    have hl := residual_length hasCell (inc.nodup menuUnique)
    rw [size e inside] at hl
    rw [← hl]
    exact mem_tuples menu _ (List.Subset.trans List.filter_sublist.subset inc.subset)
  have result := length_le_of_subset codesUnique sub
  simpa [List.countP_eq_length_filter, candidates, tuples_length] using result

private def pad (k : Nat) (xs : List V) : List (Option V) :=
  xs.map some ++ List.replicate (k-xs.length) none

private theorem unpad (k : Nat) (xs : List V) : (pad k xs).filterMap id = xs := by
  have hn (n : Nat) : (List.replicate n (none : Option V)).filterMap id = [] := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, List.filterMap_cons, ih]
  have hs (ys : List V) : (ys.map some).filterMap id = ys := by
    induction ys with
    | nil => rfl
    | cons a ys ih => simp [List.filterMap_cons, ih]
  simp [pad, List.filterMap_append, hn, hs]

/-- With edge sizes at most h, a padding symbol provides the same injection,
using an alphabet of m+1 symbols. This controls simultaneous rounding
corrections at all containment degrees. -/
theorem bounded_degree_overlap [DecidableEq V] (menu cell : List V) (edges : List (List V))
    (h : Nat) (menuUnique : menu.Nodup) (edgeUnique : edges.Nodup)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (size : ∀ e ∈ edges, e.length ≤ h) :
    edges.countP (fun e => decide (cell.Sublist e)) ≤ (menu.length+1)^(h-cell.length) := by
  let cs := edges.filter (fun e => decide (cell.Sublist e))
  let k := h - cell.length
  let alphabet := none :: menu.map some
  let code := fun e => pad k (residual cell e)
  have info {e : List V} (he : e ∈ cs) : e ∈ edges ∧ cell.Sublist e := by simpa [cs] using he
  have uniq := map_unique cs code (edgeUnique.filter _) (by
    intro e he f hf eq
    have r := congrArg (List.filterMap id) eq
    simp only [code, unpad] at r
    exact residual_injective menuUnique (canonical e (info he).1) (canonical f (info hf).1)
      (info he).2 (info hf).2 r)
  have sub : cs.map code ⊆ tuples alphabet k := by
    intro t ht
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ht
    obtain ⟨inside, contains⟩ := info he
    have inc := canonical e inside
    have hl := residual_length contains (inc.nodup menuUnique)
    have sizeE := size e inside
    have small : (residual cell e).length ≤ k := by dsimp [k]; omega
    have codeLen : (code e).length = k := by simp [code,pad]; omega
    rw [← codeLen]
    apply mem_tuples
    intro z hz
    change z ∈ (residual cell e).map some ++ List.replicate _ none at hz
    rcases List.mem_append.mp hz with left | right
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp left
      have member : v ∈ menu := inc.subset (List.filter_sublist.subset hv)
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨v,member,rfl⟩)
    · have eq := (List.mem_replicate.mp right).2
      subst z
      exact List.mem_cons_self
  have result := length_le_of_subset uniq sub
  simpa [cs,k, List.countP_eq_length_filter,tuples_length,alphabet] using result

end Screening.WitnessOverlap

/- Source module: Screening.ArithmeticWitness -/

/-! Arithmetic hard-source construction, with rational masses on one common
scale. The reference slack and physical fiber occupancy are explicit inputs.
The signed exact-cell perturbation, its overlap bound, and the resulting
physical-word law are constructed rather than assumed. -/

namespace Screening.ArithmeticWitness
open Screening.MomentCube
open Screening.CellLift

def exactMass [DecidableEq V] (atoms : List (List V × Int)) (c : List V) : Int :=
  sumOn atoms (fun a => if a.1 = c then a.2 else 0)

def table (labels : List (List V)) (a : List V → Nat) : List (List V × Int) :=
  labels.map (fun c => (c, (a c : Int)))

def specs (edges : List (List V)) (coef : List V → Int) : List (List V × Int) :=
  edges.map (fun e => (e,coef e))

def source (base : List (List V × Int)) (edges : List (List V)) (coef : List V → Int) :=
  addCubes base (specs edges coef)

def effect [DecidableEq V] (c : List V) (coef : List V → Int) : List (List V) → Int
  | [] => 0
  | e :: es => (if c.Sublist e then coef e * (-1 : Int)^c.length else 0) + effect c coef es

theorem sum_congr (xs : List A) {f g : A → Int} (h : ∀ x ∈ xs, f x = g x) :
    sumOn xs f = sumOn xs g := congrArg List.sum (List.map_congr_left h)

theorem sum_append (xs ys : List A) (f : A → Int) :
    sumOn (xs++ys) f = sumOn xs f + sumOn ys f := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    change f a + sumOn (xs++ys) f = (f a + sumOn xs f) + sumOn ys f
    rw [ih, Int.add_assoc]

private theorem sum_zero (xs : List A) : sumOn xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change 0 + sumOn xs (fun _ => 0) = 0; omega

private theorem sum_plus (xs : List A) (f g : A → Int) :
    sumOn xs (fun x => f x + g x) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change f a + g a + sumOn xs (fun x => f x + g x) =
      (f a + sumOn xs f) + (g a + sumOn xs g)
    omega

theorem sum_factor (xs : List A) (k : Int) (f : A → Int) :
    sumOn xs (fun x => k*f x) = k * sumOn xs f := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    change k*f a + sumOn xs (fun x => k*f x) = k*(f a+sumOn xs f)
    rw [ih, Int.mul_add]

theorem sum_pick [DecidableEq A] (xs : List A) (g : A → Int) (c : A)
    (unique : xs.Nodup) :
    sumOn xs (fun a => if a=c then g a else 0) = if c ∈ xs then g c else 0 := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    change (if a=c then g a else 0) + sumOn xs (fun z => if z=c then g z else 0) = _
    rw [ih tail]
    by_cases h : a=c
    · subst a; simp [fresh]
    · simp [List.mem_cons, h, Ne.symm h]

theorem exact_cube [DecidableEq V] (edge c : List V) (d : Int) (hd : edge.Nodup) :
    exactMass (cubeAtoms edge d) c = if c.Sublist edge then d * (-1 : Int)^c.length else 0 := by
  unfold exactMass cubeAtoms
  simp only [sumOn, List.map_map, Function.comp_def]
  have picked := sum_pick (cells edge) (fun x => d * (-1 : Int)^x.length) c (cells_nodup hd)
  simpa only [sumOn, mem_cells] using picked

theorem exact_table [DecidableEq V] (labels : List (List V)) (a : List V → Nat) (c : List V)
    (hd : labels.Nodup) (hc : c ∈ labels) : exactMass (table labels a) c = (a c : Int) := by
  unfold exactMass table
  simpa only [sumOn, List.map_map, Function.comp_def, if_pos hc] using
    sum_pick labels (fun z => (a z : Int)) c hd

theorem exact_source [DecidableEq V] (base : List (List V × Int)) (edges : List (List V))
    (coef : List V → Int) (c : List V) (hd : ∀ e ∈ edges, e.Nodup) :
    exactMass (source base edges coef) c = exactMass base c + effect c coef edges := by
  induction edges with
  | nil => simp [source, specs, addCubes, effect]
  | cons e es ih =>
    change sumOn (cubeAtoms e (coef e) ++ source base es coef) _ = _
    rw [sum_append]
    change exactMass (cubeAtoms e (coef e)) c + exactMass (source base es coef) c = _
    rw [exact_cube e c _ (hd e (by simp)), ih (fun z hz => hd z (by simp [hz]))]
    simp only [effect]
    omega

private theorem sign_abs (j : Nat) : ((-1 : Int)^j).natAbs = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [Int.pow_succ, Int.natAbs_mul, ih]

private theorem effect_count [DecidableEq V] (edges : List (List V)) (coef : List V → Int)
    (c : List V) (d : Nat) (amp : ∀ e ∈ edges, (coef e).natAbs ≤ d) :
    (effect c coef edges).natAbs ≤ d * edges.countP (fun e => decide (c.Sublist e)) := by
  induction edges with
  | nil => simp [effect]
  | cons e es ih =>
    have hi := ih (fun t ht => amp t (by simp [ht]))
    by_cases h : c.Sublist e
    · simp only [effect, h, if_true, List.countP_cons, decide_true, Nat.mul_add, Nat.mul_one]
      have hd := amp e (by simp)
      have := Int.natAbs_add_le (coef e * (-1:Int)^c.length) (effect c coef es)
      simp only [Int.natAbs_mul, sign_abs, Nat.mul_one] at this
      omega
    · simpa [effect, h, List.countP_cons] using hi

/-- A j-cell changes by at most d*m^(h−j) integer numerator units,
uniformly over all choices of coefficient signs. -/
theorem exact_perturbation_bound [DecidableEq V] (base : List (List V × Int))
    (menu c : List V) (edges : List (List V)) (coef : List V → Int) (h d : Nat)
    (menuUnique : menu.Nodup) (distinct : edges.Nodup)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (degree : ∀ e ∈ edges, e.length=h)
    (amp : ∀ e ∈ edges, (coef e).natAbs ≤ d) :
    (exactMass (source base edges coef) c - exactMass base c).natAbs ≤
      d * menu.length^(h-c.length) := by
  rw [exact_source _ _ _ _ (fun e he => (canonical e he).nodup menuUnique)]
  rw [show exactMass base c + effect c coef edges - exactMass base c = effect c coef edges by omega]
  exact Nat.le_trans (effect_count edges coef c d amp) (Nat.mul_le_mul_left d
    (Screening.WitnessOverlap.overlap_bound menu c edges h menuUnique distinct canonical degree))

def legalCells (menu : List V) (h : Nat) :=
  (cells menu).filter (fun c => decide (c.length ≤ h))

theorem legal_unique (menu : List V) (h : Nat) (unique : menu.Nodup) :
    (legalCells menu h).Nodup := (cells_nodup unique).filter _

private theorem covers_source (menu : List V) (h : Nat) (base : List (List V × Int))
    (edges : List (List V)) (coef : List V → Int)
    (covered : ∀ a ∈ base, a.1 ∈ legalCells menu h)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (degree : ∀ e ∈ edges, e.length≤h) :
    ∀ a ∈ source base edges coef, a.1 ∈ legalCells menu h := by
  induction edges with
  | nil => exact covered
  | cons e es ih =>
    intro a ha
    change a ∈ cubeAtoms e (coef e) ++ source base es coef at ha
    rcases List.mem_append.mp ha with hleft | hright
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hleft
      have inside := mem_cells.mp hc
      have sz := inside.length_le
      have fit := Nat.le_trans sz (degree e (by simp))
      exact List.mem_filter.mpr ⟨mem_cells.mpr (inside.trans (canonical e (by simp))), by simpa⟩
    · exact ih (fun z hz => canonical z (by simp [hz])) (fun z hz => degree z (by simp [hz])) a hright

private theorem regroup [DecidableEq V] (atoms : List (List V × Int))
    (labels : List (List V)) (q : List V) (unique : labels.Nodup)
    (covered : ∀ a ∈ atoms, a.1 ∈ labels) :
    histogramMoment atoms q = sumOn labels (fun c => if q ⊆ c then exactMass atoms c else 0) := by
  induction atoms with
  | nil =>
    have z := sum_zero labels
    simpa [histogramMoment, exactMass, sumOn] using z.symm
  | cons a xs ih =>
    obtain ⟨z,v⟩ := a
    have inside : z ∈ labels := covered (z,v) (by simp)
    have hrest := ih (fun a ha => covered a (by simp [ha]))
    let entry := fun c => if c=z then (if q ⊆ z then v else 0) else 0
    let remainder := fun c => if q ⊆ c then exactMass xs c else 0
    have split :
        sumOn labels (fun c => if q ⊆ c then exactMass ((z,v)::xs) c else 0) =
        sumOn labels entry + sumOn labels remainder := by
      rw [← sum_plus]
      apply sum_congr
      intro c _
      change (if q ⊆ c then (if z=c then v else 0) + exactMass xs c else 0) = _
      by_cases eq : c=z
      · subst c; by_cases hq : q ⊆ z <;> simp [entry, remainder, hq]
      · by_cases hq : q ⊆ c <;> simp [entry,remainder,hq,eq,Ne.symm eq]
    have single := sum_pick labels (fun _ => if q ⊆ z then v else 0) z unique
    rw [if_pos inside] at single
    change (if q ⊆ z then v else 0) + histogramMoment xs q = _
    change sumOn labels entry = (if q ⊆ z then v else 0) at single
    rw [split, ← hrest, single]

private theorem sum_cast (labels : List A) (a : A → Nat) :
    sumOn labels (fun c => (a c : Int)) = (sumNat labels a : Int) := by
  induction labels with
  | nil => rfl
  | cons c cs ih =>
    change (a c : Int) + sumOn cs (fun x => (a x : Int)) = (↑(a c + sumNat cs a) : Int)
    rw [ih, Int.natCast_add]

def wordAtoms (words : List W) (tag : W → List V) (weight : W → Nat) :=
  words.map (fun w => (tag w, (weight w : Int)))

private theorem words_exact [DecidableEq V] (words : List W) (tag : W → List V)
    (weight : W → Nat) (c : List V) :
    exactMass (wordAtoms words tag weight) c = (cellMass words tag weight c : Int) := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    change (if tag w = c then (weight w : Int) else 0) + exactMass (wordAtoms ws tag weight) c =
      (↑((if tag w = c then weight w else 0) + cellMass ws tag weight c) : Int)
    rw [ih,Int.natCast_add]
    by_cases h : tag w=c <;> simp [h]

private theorem table_covered (labels : List (List V)) (a : List V → Nat) :
    ∀ t ∈ table labels a, t.1 ∈ labels := by
  intro t ht
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
  exact hc

private theorem preserve_low [DecidableEq V] (base : List (List V × Int))
    (edges : List (List V)) (coef : List V → Int) (q : List V) (h : Nat)
    (unique : ∀ e ∈ edges, e.Nodup) (degree : ∀ e ∈ edges, e.length=h)
    (low : q.length<h) : histogramMoment (source base edges coef) q = histogramMoment base q := by
  apply superposition_preserves_lower
  · intro s hs
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
    exact unique e he
  · intro s hs
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
    simpa [degree e he] using low

/-- A coarse reference cell provides enough room on both sides for its
signed update. The updated numerator is strictly positive, and the bounds
on the *updated* cell are conclusions. -/
theorem guarded_numerator (x : Int) (a cap factor low high : Nat)
    (positiveLower : 0 < low) (discrepancy : (x - (a:Int)).natAbs ≤ cap)
    (left : low + factor*cap ≤ factor*a) (right : factor*a + factor*cap ≤ high) :
    0 < x ∧ low ≤ factor*x.toNat ∧ factor*x.toNat ≤ high := by
  have inside : cap < a := Nat.lt_of_mul_lt_mul_left (by omega : factor*cap < factor*a)
  have linear := Int.natAbs_eq (x-(a:Int))
  have xpos : 0 < x := by rcases linear with hp|hp <;> omega
  have lower : a ≤ x.toNat + cap := by rcases linear with hp|hp <;> omega
  have upper : x.toNat ≤ a + cap := by rcases linear with hp|hp <;> omega
  have hl := Nat.mul_le_mul_left factor lower
  have hr := Nat.mul_le_mul_left factor upper
  rw [Nat.mul_add] at hl hr
  exact ⟨xpos,by omega,by omega⟩

/-- Reference error and perturbation can share the allowed relative-density
error budget. This concrete sufficient condition allocates half to each.
All integers are on the common rational scale used in the physical lift. -/
theorem half_slack (L n a cap D b e : Nat) (eps : e ≤ b)
    (refError : 2 * ((↑(b*L*a) : Int) - (↑(b*D*n):Int)).natAbs ≤ e*D*n)
    (cubeError : 2*(b*L*cap) ≤ e*D*n) :
    (b-e)*D*n + b*L*cap ≤ b*L*a ∧ b*L*a + b*L*cap ≤ (b+e)*D*n := by
  have range := Nat.mul_le_mul_right n (Nat.mul_le_mul_right D eps)
  simp only [Nat.sub_mul, Nat.add_mul]
  have cases := Int.natAbs_eq ((↑(b*L*a):Int) - (↑(b*D*n):Int))
  rcases cases with hc|hc <;> omega

/-- A single amplitude condition suffices for every cell once the physical
fiber has size at least L/(2*Q^j). In the paper Q=2P and m≤Q. -/
theorem scalar_amplitude_budget (m Q L n b D eps d h j : Nat)
    (degree : j≤h) (sparse : m≤Q) (fiberLower : L ≤ 2*n*Q^j)
    (amp : 4*b*d*Q^h ≤ eps*D) :
    2 * (b*L*(d*m^(h-j))) ≤ eps*D*n := by
  have qbound : m^(h-j) ≤ Q^(h-j) := Nat.pow_le_pow_left sparse _
  have qexp : Q^j * Q^(h-j) = Q^h := by rw [← Nat.pow_add, Nat.add_sub_of_le degree]
  calc
    _ ≤ 2 * (b*(2*n*Q^j)*(d*Q^(h-j))) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul_left b fiberLower)
        (Nat.mul_le_mul_left d qbound))
    _ = 4*b*d*(Q^j*Q^(h-j))*n := by
      change 2 * (b*((2*n)*Q^j)*(d*Q^(h-j))) = (2*2)*b*d*(Q^j*Q^(h-j))*n
      ac_rfl
    _ = 4*b*d*Q^h*n := by rw [qexp]
    _ ≤ _ := Nat.mul_le_mul_right n amp

private theorem table_total [DecidableEq V] (labels : List (List V)) (ref : List V → Nat) :
    histogramMoment (table labels ref) [] = (sumNat labels ref : Int) := by
  simpa [histogramMoment, table, sumOn, List.map_map, Function.comp_def] using sum_cast labels ref

/-- Realization of the signed hard laws on a tagged integer population.

The reference masses are ref(c)/D and uniform physical masses are n(c)/L.
The two error premises allocate half the relative allowance eps/b to the
reference discrepancy and half to the cube perturbations, respectively.
They concern the unperturbed reference, the independently supplied amplitude
bound, and actual fiber counts. The conclusion constructs a new physical law
for every choice of signs; none of its probabilities are inputs. -/
theorem physical_witness [DecidableEq V] (words : List Nat) (tag : Nat → List V)
    (menu : List V) (edges : List (List V)) (coef : List V → Int)
    (ref : List V → Nat) (h d D b eps : Nat)
    (degreePos : 0<h) (denPos : 0<D) (epsSmall : eps<b)
    (menuUnique : menu.Nodup) (distinct : edges.Nodup)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (degree : ∀ e ∈ edges, e.length=h)
    (amp : ∀ e ∈ edges, (coef e).natAbs ≤ d)
    (complete : ∀ w ∈ words, tag w ∈ legalCells menu h)
    (occupied : ∀ c ∈ legalCells menu h, 0 < fiberSize words tag c)
    (normalized : sumNat (legalCells menu h) ref = D)
    (referenceError : ∀ c ∈ legalCells menu h,
      2 * ((↑(b*words.length*ref c):Int) - (↑(b*D*fiberSize words tag c):Int)).natAbs ≤
        eps*D*fiberSize words tag c)
    (perturbationBudget : ∀ c ∈ legalCells menu h,
      2 * (b*words.length*(d*menu.length^(h-c.length))) ≤ eps*D*fiberSize words tag c) :
    ∃ K : Nat, ∃ weight : Nat → Nat,
      0<K ∧ sumNat words weight = D*K ∧
      (∀ w ∈ words,
        (b-eps)*(D*K) ≤ b*words.length*weight w ∧
        b*words.length*weight w ≤ (b+eps)*(D*K)) ∧
      (∀ c ∈ legalCells menu h,
        0 < cellMass words tag weight c ∧
        (cellMass words tag weight c : Int) =
          (K:Int)*exactMass (source (table (legalCells menu h) ref) edges coef) c) ∧
      (∀ q : List V, q.length<h →
        histogramMoment (wordAtoms words tag weight) q =
          (K:Int)*histogramMoment (table (legalCells menu h) ref) q) := by
  let labels := legalCells menu h
  let base := table labels ref
  let updated := source base edges coef
  let num := fun c => (exactMass updated c).toNat
  have unique : labels.Nodup := legal_unique menu h menuUnique
  have unE : ∀ e ∈ edges, e.Nodup := fun e he => (canonical e he).nodup menuUnique
  have cov : ∀ t ∈ updated, t.1 ∈ labels :=
    covers_source menu h base edges coef (table_covered labels ref) canonical
      (fun e he => Nat.le_of_eq (degree e he))
  have cal (c : List V) (hc : c ∈ labels) :
      0 < exactMass updated c ∧
      (b-eps)*D*fiberSize words tag c ≤ b*words.length*num c ∧
      b*words.length*num c ≤ (b+eps)*D*fiberSize words tag c := by
    have bound := exact_perturbation_bound base menu c edges coef h d menuUnique distinct canonical degree amp
    have baseEq : exactMass base c = (ref c:Int) := exact_table labels ref c unique hc
    rw [baseEq] at bound
    obtain ⟨lo,hi⟩ := half_slack words.length (fiberSize words tag c) (ref c)
      (d*menu.length^(h-c.length)) D b eps (Nat.le_of_lt epsSmall)
      (referenceError c hc) (perturbationBudget c hc)
    exact guarded_numerator (exactMass updated c) (ref c) _ (b*words.length) _ _
      (Nat.mul_pos (Nat.mul_pos (by omega) denPos) (occupied c hc)) bound lo hi
  have repr (c : List V) (hc : c ∈ labels) : (num c:Int)=exactMass updated c :=
    Int.toNat_of_nonneg (Int.le_of_lt (cal c hc).1)
  have totalEq : (sumNat labels num:Int) = (D:Int) := by
    calc
      _ = sumOn labels (fun c => (num c:Int)) := (sum_cast labels num).symm
      _ = sumOn labels (exactMass updated) := sum_congr labels repr
      _ = histogramMoment updated [] := by simpa using (regroup updated labels [] unique cov).symm
      _ = histogramMoment base [] := preserve_low base edges coef [] h unE degree degreePos
      _ = (sumNat labels ref:Int) := table_total labels ref
      _ = _ := by rw [normalized]
  obtain ⟨K,weight,Kpos,_,total,recovers,_,denBounds⟩ :=
    lift_rational_cell_law words labels tag num D b (b-eps) (b+eps) denPos (by omega)
      unique complete occupied (Int.ofNat_inj.mp totalEq) (fun c hc => (cal c hc).2)
  have cellEq (c : List V) (hc : c ∈ labels) : (cellMass words tag weight c:Int) =
      (K:Int)*exactMass updated c := by
    rw [recovers c hc, Int.natCast_mul, repr c hc]
  have wordCov : ∀ a ∈ wordAtoms words tag weight, a.1 ∈ labels := by
    intro a ha
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact complete w hw
  refine ⟨K,weight,Kpos,total,denBounds,?_,?_⟩
  · intro c hc
    have npos : 0 < num c := by
      have := (cal c hc).1
      have := repr c hc
      omega
    exact ⟨by rw [recovers c hc]; exact Nat.mul_pos Kpos npos, cellEq c hc⟩
  · intro q size
    calc
      _ = sumOn labels (fun c => if q ⊆ c then exactMass (wordAtoms words tag weight) c else 0) :=
        regroup _ _ _ unique wordCov
      _ = sumOn labels (fun c => (K:Int) * (if q ⊆ c then exactMass updated c else 0)) := by
        apply sum_congr
        intro c hc
        by_cases sub : q ⊆ c <;> simp [sub, words_exact, cellEq c hc]
      _ = (K:Int)*histogramMoment updated q := by
        rw [sum_factor, ← regroup updated labels q unique cov]
      _ = _ := by rw [show histogramMoment updated q = histogramMoment base q from
          preserve_low base edges coef q h unE degree size]

def correction [DecidableEq V] (base : List (List V × Int)) (target : List V → Int) (e : List V) :=
  (-1:Int)^e.length * (target e - histogramMoment base e)

def calibrated [DecidableEq V] (menu : List V) (h : Nat) (base : List (List V × Int))
    (target : List V → Int) := source base (legalCells menu h) (correction base target)

private theorem legal_info {menu c : List V} {h : Nat} (hc : c ∈ legalCells menu h) :
    c.Sublist menu ∧ c.length ≤ h := by simpa [legalCells, mem_cells] using hc

private theorem sign_squared (n : Nat) : (-1:Int)^n * (-1:Int)^n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Int.pow_succ, Int.neg_mul, Int.mul_neg, ih]

/-- Möbius calibration corrects all legal containment moments simultaneously,
including the empty query. The target may be the scaled reciprocal products.
This is an exact identity for the constructed signed table, before positivity. -/
theorem calibrated_moment [DecidableEq V] (menu : List V) (h : Nat) (base : List (List V×Int))
    (target : List V → Int) (q : List V) (unique : menu.Nodup) (legal : q∈legalCells menu h) :
    histogramMoment (calibrated menu h base target) q = target q := by
  let labels := legalCells menu h
  let corr := correction base target
  have hd : ∀ s ∈ specs labels corr, s.1.Nodup := by
    intro s hs
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
    exact (legal_info he).1.nodup unique
  have calcMom := histogram_superposition base (specs labels corr) q hd
  have sumEq : sumOn (specs labels corr) (fun s =>
      if s.1 ⊆ q ∧ q ⊆ s.1 then s.2 * (-1:Int)^s.1.length else 0) =
      sumOn labels (fun e => if e=q then target e-histogramMoment base e else 0) := by
    change (((labels.map _).map _).sum) = _
    simp only [List.map_map, Function.comp_def]
    apply sum_congr labels
    intro e he
    have seteq : (e ⊆ q ∧ q ⊆ e) ↔ e=q := by
      constructor
      · intro both
        exact Screening.WitnessOverlap.canonical_ext unique (legal_info he).1
          (legal_info legal).1 both.1 both.2
      · rintro rfl; simp
    by_cases eq : e=q
    · rw [if_pos (seteq.mpr eq),if_pos eq]
      change ((-1:Int)^e.length*(target e-histogramMoment base e))*(-1:Int)^e.length = _
      calc
        _ = ((-1:Int)^e.length*(-1:Int)^e.length)*(target e-histogramMoment base e) := by ac_rfl
        _ = _ := by rw [sign_squared,Int.one_mul]
    · simp [seteq,eq]
  rw [sumEq, sum_pick _ _ _ (legal_unique menu h unique), if_pos legal] at calcMom
  change histogramMoment (addCubes base (specs labels corr)) q = _
  omega

/-- If each count on its common numerator scale differs from the desired
containment by at most U, the reference adjustment on a j-cell is at most
U*(m+1)^(h−j). The count includes all correction degrees rather than h alone. -/
theorem calibration_discrepancy [DecidableEq V] (menu c : List V) (h U : Nat)
    (base : List (List V×Int)) (target : List V→Int) (unique : menu.Nodup)
    (rounding : ∀ e ∈ legalCells menu h, (target e-histogramMoment base e).natAbs ≤ U) :
    (exactMass (calibrated menu h base target) c - exactMass base c).natAbs ≤
      U*(menu.length+1)^(h-c.length) := by
  let labels := legalCells menu h
  let corr := correction base target
  have hd := fun e (he : e ∈ labels) => (legal_info he).1.nodup unique
  have a : ∀ e ∈ labels, (corr e).natAbs ≤ U := by
    intro e he
    simpa [corr,correction,Int.natAbs_mul,sign_abs] using rounding e he
  change (exactMass (source base labels corr) c - exactMass base c).natAbs ≤ _
  rw [exact_source _ _ _ _ hd]
  rw [show exactMass base c + effect c corr labels - exactMass base c = effect c corr labels by omega]
  exact Nat.le_trans (effect_count labels corr c U a)
    (Nat.mul_le_mul_left U (Screening.WitnessOverlap.bounded_degree_overlap menu c labels h
      unique (legal_unique menu h unique) (fun e he => (legal_info he).1)
      (fun e he => (legal_info he).2)))

private theorem positive_table_moment [DecidableEq V] (atoms : List (List V×Int))
    (labels : List (List V)) (q : List V) (unique : labels.Nodup)
    (cover : ∀ a ∈ atoms, a.1∈labels) (positive : ∀ c∈labels, 0≤exactMass atoms c) :
    histogramMoment (table labels (fun c => (exactMass atoms c).toNat)) q =
      histogramMoment atoms q := by
  rw [regroup _ labels q unique (table_covered _ _),regroup atoms labels q unique cover]
  apply sum_congr
  intro c hc
  rw [exact_table _ _ c unique hc,Int.toNat_of_nonneg (positive c hc)]

/-- Uniform integer words first receive small rounding corrections at every
degree, after which the signed h-cubes encode the hard instance. This result
starts from the physical uniform cell counts; it produces and calibrates the
reference as part of the proof. Q=2P in the interval application. -/
theorem calibrated_physical_witness [DecidableEq V] (words : List Nat) (tag : Nat → List V)
    (menu : List V) (edges : List (List V)) (coef : List V → Int)
    (target : List V → Int) (h d U b eps Q : Nat)
    (degreePos : 0<h) (uPos : 0<U) (wordsPos : 0<words.length) (epsSmall : eps<b)
    (sparse : menu.length+1 ≤ Q) (menuUnique : menu.Nodup) (distinct : edges.Nodup)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (degree : ∀ e ∈ edges, e.length=h)
    (amp : ∀ e ∈ edges, (coef e).natAbs ≤ d)
    (complete : ∀ w∈words, tag w∈legalCells menu h)
    (fiberLower : ∀ c∈legalCells menu h, words.length ≤ 2*fiberSize words tag c*Q^c.length)
    (intervalSize : 4*b*Q^h ≤ eps*words.length)
    (amplitude : 4*b*d*Q^h ≤ eps*(words.length*U))
    (targetTotal : target [] = (↑(words.length*U):Int))
    (rounding : ∀ c∈legalCells menu h,
      (target c - histogramMoment
        (table (legalCells menu h) (fun s => U*fiberSize words tag s)) c).natAbs ≤ U) :
    ∃ K : Nat, ∃ weight : Nat → Nat, 0<K ∧
      sumNat words weight = (words.length*U)*K ∧
      (∀ w∈words,
        (b-eps)*((words.length*U)*K) ≤ b*words.length*weight w ∧
        b*words.length*weight w ≤ (b+eps)*((words.length*U)*K)) ∧
      (∀ c∈legalCells menu h, 0<cellMass words tag weight c) ∧
      (∀ q∈legalCells menu h, q.length<h →
        histogramMoment (wordAtoms words tag weight) q = (K:Int)*target q) ∧
      (∀ c∈legalCells menu h,
        (cellMass words tag weight c : Int) =
          (K:Int)*(exactMass
            (calibrated menu h (table (legalCells menu h) (fun s => U*fiberSize words tag s)) target)
            c + effect c coef edges)) := by
  let labels := legalCells menu h
  let D := words.length*U
  let a0 := fun c => U*fiberSize words tag c
  let start := table labels a0
  let base := calibrated menu h start target
  let ref := fun c => (exactMass base c).toNat
  have unique := legal_unique menu h menuUnique
  have dp : 0 < D := Nat.mul_pos wordsPos uPos
  have occupied (c : List V) (hc : c∈labels) : 0 < fiberSize words tag c := by
    have hl := fiberLower c hc
    by_cases z : fiberSize words tag c=0
    · simp only [z,Nat.mul_zero,Nat.zero_mul] at hl
      omega
    · omega
  have scalar : 4*b*U*Q^h ≤ eps*D := by
    calc
      _ = (4*b*Q^h)*U := by ac_rfl
      _ ≤ (eps*words.length)*U := Nat.mul_le_mul_right U intervalSize
      _ = _ := by dsimp [D]; ac_rfl
  have refControl (c : List V) (hc : c∈labels) :
      0<exactMass base c ∧
      2*((↑(b*words.length*ref c):Int)-(↑(b*D*fiberSize words tag c):Int)).natAbs ≤
        eps*D*fiberSize words tag c := by
    let cap := U*(menu.length+1)^(h-c.length)
    let n := fiberSize words tag c
    let F := b*words.length
    have lim : 2*(F*cap) ≤ eps*D*n :=
      scalar_amplitude_budget (menu.length+1) Q words.length n b D eps U h c.length
        (legal_info hc).2 sparse (fiberLower c hc) scalar
    have center : F*a0 c=b*D*n := by dsimp [F,a0,D,n]; ac_rfl
    have delta : (exactMass base c - (↑(a0 c):Int)).natAbs ≤ cap := by
      have r := calibration_discrepancy menu c h U start target menuUnique rounding
      rw [show exactMass start c = (a0 c:Int) from exact_table labels a0 c unique hc] at r
      exact r
    have zeroError : 2*((↑(F*a0 c):Int)-(↑(b*D*n):Int)).natAbs ≤ eps*D*n := by
      simp [center]
    obtain ⟨lo,hi⟩ := half_slack words.length n (a0 c) cap D b eps
      (Nat.le_of_lt epsSmall) zeroError lim
    have positive := (guarded_numerator (exactMass base c) (a0 c) cap F _ _
      (Nat.mul_pos (Nat.mul_pos (by omega) dp) (occupied c hc)) delta lo hi).1
    refine ⟨positive,?_⟩
    have ra : (ref c : Int)=exactMass base c := Int.toNat_of_nonneg (Int.le_of_lt positive)
    change 2*((↑(F*ref c):Int)-(↑(b*D*n):Int)).natAbs ≤ _
    rw [← center,Int.natCast_mul F (ref c),Int.natCast_mul F (a0 c),ra, ← Int.mul_sub,
      Int.natAbs_mul,Int.natAbs_ofNat]
    exact Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left F delta)) lim
  have coverBase : ∀ t∈base,t.1∈labels := covers_source menu h start labels
    (correction start target) (table_covered labels a0) (fun e he => (legal_info he).1)
    (fun e he => (legal_info he).2)
  have moments (q : List V) (hq : q∈labels) :
      histogramMoment (table labels ref) q = target q :=
    (positive_table_moment base labels q unique coverBase
      (fun c hc => Int.le_of_lt (refControl c hc).1)).trans
      (calibrated_moment menu h start target q menuUnique hq)
  have emptyLegal : []∈labels := by simp [labels,legalCells,mem_cells]
  have norm : sumNat labels ref=D := by
    apply Int.ofNat_inj.mp
    exact (table_total labels ref).symm.trans ((moments [] emptyLegal).trans targetTotal)
  have budget (c : List V) (hc : c∈labels) :
      2*(b*words.length*(d*menu.length^(h-c.length))) ≤ eps*D*fiberSize words tag c :=
    scalar_amplitude_budget menu.length Q words.length _ b D eps d h c.length
      (legal_info hc).2 (by omega) (fiberLower c hc) amplitude
  obtain ⟨K,weight,kpos,tot,dens,cell,low⟩ :=
    physical_witness words tag menu edges coef ref h d D b eps degreePos dp epsSmall
      menuUnique distinct canonical degree amp complete occupied norm (fun c hc => (refControl c hc).2)
      budget
  refine ⟨K,weight,kpos,tot,dens,fun c hc => (cell c hc).1,?_,?_⟩
  · intro q hq small
    exact (low q small).trans (congrArg ((K:Int)*·) (moments q hq))
  · intro c hc
    rw [(cell c hc).2,exact_source _ _ _ _ (fun e he => (canonical e he).nodup menuUnique),
      exact_table _ _ c unique hc]
    change (K:Int)*((↑(ref c):Int) + _) = _
    rw [show (↑(ref c):Int)=exactMass base c from Int.toNat_of_nonneg (Int.le_of_lt (refControl c hc).1)]

private theorem uniform_exact_count [DecidableEq V] (words : List Nat) (tag : Nat→List V)
    (U : Nat) (c : List V) :
    exactMass (wordAtoms words tag (fun _ => U)) c = (↑(U*fiberSize words tag c):Int) := by
  induction words with
  | nil => simp [exactMass,wordAtoms,sumOn,fiberSize]
  | cons w ws ih =>
    change (if tag w=c then (U:Int) else 0) + exactMass (wordAtoms ws tag (fun _ => U)) c = _
    rw [ih]
    by_cases he : tag w=c <;>
      simp [fiberSize,List.filter_cons,he,Nat.mul_succ,Int.natCast_add,Int.add_comm]

/-- The histogram of uniform fiber counts is exactly U times the literal
number of physical words on which all members of the query hit. -/
theorem uniform_table_count [DecidableEq V] (words : List Nat) (tag : Nat→List V)
    (labels : List (List V)) (U : Nat) (q : List V) (unique : labels.Nodup)
    (complete : ∀ w∈words, tag w∈labels) :
    histogramMoment (table labels (fun s => U*fiberSize words tag s)) q =
      (↑(U*words.countP (fun w => decide (q⊆tag w))):Int) := by
  have covered : ∀ t∈wordAtoms words tag (fun _ => U), t.1∈labels := by
    intro t ht
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
    exact complete w hw
  calc
    _ = histogramMoment (wordAtoms words tag (fun _ => U)) q := by
      rw [regroup _ labels q unique (table_covered _ _),regroup _ labels q unique covered]
      apply sum_congr
      intro c hc
      rw [exact_table _ _ c unique hc,uniform_exact_count]
    _ = _ := by
      clear complete covered
      induction words with
      | nil => simp [histogramMoment,wordAtoms,sumOn]
      | cons w ws ih =>
        change (if q⊆tag w then (U:Int) else 0) + histogramMoment (wordAtoms ws tag (fun _ => U)) q = _
        rw [ih]
        by_cases hc : q⊆tag w <;>
          simp [List.countP_cons,hc,Nat.mul_add,Nat.mul_succ,Int.natCast_add,Int.add_comm]

end Screening.ArithmeticWitness

/- Source module: Screening.OneHitInversion -/

/-! Fair-sign inversion of local exact hit cells from a marked-first stopped scan.
The distinguished label is j. The d positions following it in its block
are indexed by a Boolean cube. All arithmetic is integral, with explicit
powers of two for the denominators of the fair public coins. -/
namespace Screening.OneHitInversion

/-- A recursively indexed Boolean cube with one coordinate per tail position. -/
def Mask : Nat → Type
  | 0 => Unit
  | d+1 => Bool × Mask d

instance maskDecEq (d : Nat) : DecidableEq (Mask d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ d ih =>
    letI : DecidableEq (Mask d) := ih
    exact inferInstanceAs (DecidableEq (Bool × Mask d))

def cubeSum : (d : Nat) → (Mask d → Int) → Int
  | 0,f => f ()
  | d+1,f => cubeSum d (fun t => f (false,t)) + cubeSum d (fun t => f (true,t))

theorem cube_scale (d : Nat) (c : Int) (f : Mask d → Int) :
    cubeSum d (fun t => c*f t) = c*cubeSum d f := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [cubeSum,ih,Int.mul_add]

theorem cube_add (d : Nat) (f g : Mask d → Int) :
    cubeSum d (fun t => f t+g t) = cubeSum d f + cubeSum d g := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [cubeSum,ih]; ac_rfl

theorem cube_const (d : Nat) (c : Int) :
    cubeSum d (fun _ => c) = 2^d*c := by
  induction d with
  | zero => simp [cubeSum]
  | succ d ih =>
    have two : 2*c = c+c := by omega
    simp only [cubeSum,ih,Int.pow_succ,Int.mul_assoc,two,Int.mul_add]

/-- A scan label is true exactly at the single distinguished index j.
A missing hit returns none. -/
structure Test where
  pivot : Bool
  positive : Bool
  hit : Bool

def scan : List Test → Option Bool
  | [] => none
  | x::xs => if x.hit then some x.pivot else scan xs

def markedFirst (xs : List Test) : List Test :=
  xs.filter (fun x => x.positive) ++ xs.filter (fun x => !x.positive)

def ordinary (x : Bool × Bool) : Test := ⟨false,x.2,x.1⟩

/-- For earlier and later blocks, their public scans may already be listed in
any order. Every earlier test precedes this block and every later test
follows it. All local tests use the actual marked-before-unmarked priority. -/
def stopped (before left right after : List (Bool × Bool)) (jhit jmark : Bool) : Option Bool :=
  scan (before.map ordinary ++
        markedFirst (left.map ordinary ++ [⟨true,jmark,jhit⟩] ++ right.map ordinary) ++
        after.map ordinary)

def clear (xs : List (Bool × Bool)) : Bool := !(xs.any (fun x => x.1))
def noPositiveHit (xs : List (Bool × Bool)) : Bool := !(xs.any (fun x => x.1 && x.2))

private theorem scan_append (xs ys : List Test) : scan (xs++ys) = (scan xs).or (scan ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : x.hit <;> simp [scan,h,ih,Option.or]

private theorem scan_ordinary (xs : List (Bool × Bool)) :
    scan (xs.map ordinary) = if clear xs then none else some false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨h,m⟩
    cases h <;> simp [scan,ordinary,clear,List.any_cons] at ih ⊢ <;> exact ih

private theorem scan_part (xs : List (Bool × Bool)) (mark : Bool) :
    scan ((xs.map ordinary).filter (fun x => x.positive == mark)) =
      if xs.any (fun x => x.1 && (x.2 == mark)) then some false else none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨h,m⟩
    cases h <;> cases m <;> cases mark <;>
      simp [List.filter_cons,scan,ordinary,List.any_cons] at ih ⊢ <;> exact ih

private theorem clear_parts (xs : List (Bool × Bool)) :
    xs.any (fun x => x.1) =
      (xs.any (fun x => x.1 && x.2) || xs.any (fun x => x.1 && !x.2)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨h,m⟩
    cases h <;> cases m <;> simp [List.any_cons,ih]

/-- Detection of a negative pivot from the stopped log is equivalent to j
being the natural first hit and all tail hits in its block being unmarked.
Earlier positions of the current block also have to miss. -/
theorem negative_first (before left right after : List (Bool × Bool)) (jhit : Bool) :
    stopped before left right after jhit false = some true ↔
      (clear before && clear left && jhit && noPositiveHit right) = true := by
  have pos (l : List (Bool × Bool)) := scan_part l true
  have neg (l : List (Bool × Bool)) := scan_part l false
  simp only [beq_true] at pos
  simp only [beq_false] at neg
  unfold stopped markedFirst noPositiveHit clear
  simp only [List.filter_append,List.filter_cons,List.filter_nil,Bool.not_false,
    Bool.false_eq_true,if_false,if_true,List.nil_append,List.cons_append,
    scan_append,scan_ordinary,pos,neg,scan]
  rw [clear_parts left]
  unfold clear
  cases jhit <;> cases before.any (fun x => x.1) <;>
    cases left.any (fun x => x.1 && x.2) <;> cases left.any (fun x => x.1 && !x.2) <;>
    cases right.any (fun x => x.1 && x.2) <;> cases right.any (fun x => x.1 && !x.2) <;>
    cases after.any (fun x => x.1) <;> decide

def slots : (d : Nat) → Mask d → Mask d → List (Bool × Bool)
  | 0,_,_ => []
  | d+1,(z,zs),(s,ss) => (z,s)::slots d zs ss

/-- This includes the negative sign (-1) for every selected tail position:
a positive public sign contributes -2 and a negative public sign +2. -/
def charBit (query sign : Bool) : Int :=
  if query then (if sign then -2 else 2) else 1

def character : (d : Nat) → Mask d → Mask d → Int
  | 0,_,_ => 1
  | d+1,(t,ts),(s,ss) => charBit t s * character d ts ss

/-- The score uses only public signs, the recorded pivot flag and the
partition coin. In particular it never reads the underlying hit set. -/
def score (d : Nat) (query marks : Mask d) (assigned jmark : Bool) (log : Option Bool) : Int :=
  if assigned && !jmark && (log == some true) then 4*character d query marks else 0

/-- Unnormalized forward matrix for one tail coordinate. Rows are query
membership, columns are actual hit membership. Dividing by 2 gives
[[1,1/2],[0,1]]. -/
def forwardBit : Bool → Bool → Int
  | false, false => 2
  | false, true => 1
  | true, false => 0
  | true, true => 2

/-- The inverse matrix, also scaled by 2, is [[2,-1],[0,2]]. -/
def inverseBit : Bool → Bool → Int
  | false, false => 2
  | false, true => -1
  | true, false => 0
  | true, true => 2

def kernel (entry : Bool → Bool → Int) : (d : Nat) → Mask d → Mask d → Int
  | 0,_,_ => 1
  | d+1,(x,xs),(y,ys) => entry x y * kernel entry d xs ys

private def activeBit (z s : Bool) : Int := if z && s then 0 else 1

private theorem negative_cons (d : Nat) (zs ss : Mask d) (z s : Bool) :
    (if noPositiveHit ((z,s)::slots d zs ss) then (1:Int) else 0) =
      activeBit z s * (if noPositiveHit (slots d zs ss) then 1 else 0) := by
  cases z <;> cases s <;> simp [noPositiveHit,activeBit]

private theorem marked_kernel (d : Nat) (t z : Mask d) :
    cubeSum d (fun s => (if noPositiveHit (slots d z s) then (1:Int) else 0) *
      character d t s) = kernel forwardBit d t z := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases t with ⟨t,ts⟩; rcases z with ⟨z,zs⟩
    have branch (b : Bool) :
        cubeSum d (fun ss => (if noPositiveHit (slots (d+1) (z,zs) (b,ss)) then (1:Int) else 0) *
          character (d+1) (t,ts) (b,ss)) =
          (activeBit z b*charBit t b)*kernel forwardBit d ts zs := by
      have hfun : (fun ss => (if noPositiveHit (slots (d+1) (z,zs) (b,ss)) then (1:Int) else 0) *
          character (d+1) (t,ts) (b,ss)) =
        (fun ss => (activeBit z b*charBit t b)*
          ((if noPositiveHit (slots d zs ss) then (1:Int) else 0)*character d ts ss)) := by
        funext ss; rw [slots,negative_cons,character]; ac_rfl
      rw [hfun,cube_scale,ih]
    rw [cubeSum,branch,branch,kernel,← Int.add_mul]
    cases t <;> cases z <;> rfl

/-- Sum over all public marks and the two independent fair choices for
the partition and the pivot's own sign. On the other partition its
record may be entirely arbitrary, since that branch has zero score. -/
def rawScoreSum (d : Nat) (query z : Mask d) (before left after : List (Bool × Bool))
    (jhit : Bool) (other : Bool → Mask d → Option Bool) : Int :=
  cubeSum d fun s =>
    score d query s false false (other false s) + score d query s false true (other true s) +
    score d query s true false (stopped before left (slots d z s) after jhit false) +
    score d query s true true (stopped before left (slots d z s) after jhit true)

/-- There are 4·2^d public outcomes in this sum. Conditional on the
word, the mean is the forward kernel divided by 2^d if j is the natural
minimum, and zero otherwise. All hits after this block are arbitrary. -/
theorem stopped_forward (d : Nat) (query z : Mask d) (before left after : List (Bool × Bool))
    (jhit : Bool) (other : Bool → Mask d → Option Bool) :
    rawScoreSum d query z before left after jhit other =
      (if clear before && clear left && jhit then 4 else 0) * kernel forwardBit d query z := by
  let gate := clear before && clear left && jhit
  have hf (s : Mask d) :
      score d query s false false (other false s) + score d query s false true (other true s) +
      score d query s true false (stopped before left (slots d z s) after jhit false) +
      score d query s true true (stopped before left (slots d z s) after jhit true) =
      (if gate then 4 else 0) *
      ((if noPositiveHit (slots d z s) then (1:Int) else 0)*character d query s) := by
    have obs := negative_first before left (slots d z s) after jhit
    change (stopped before left (slots d z s) after jhit false = some true ↔
      (gate && noPositiveHit (slots d z s)) = true) at obs
    by_cases hg : gate <;> by_cases hs : noPositiveHit (slots d z s) <;>
      simp [score,hg,hs] at obs ⊢ <;> simp [obs]
  unfold rawScoreSum
  simp only [hf,cube_scale,marked_kernel,gate]

/-- Exact two-sided triangular inversion on every Boolean subset interval,
with no type-level restriction on d. -/
theorem inverse_forward (d : Nat) (u z : Mask d) :
    cubeSum d (fun t => kernel inverseBit d u t * kernel forwardBit d t z) =
      if u=z then (4:Int)^d else 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases u with ⟨u,us⟩; rcases z with ⟨z,zs⟩
    have branch (t : Bool) :
        cubeSum d (fun ts => kernel inverseBit (d+1) (u,us) (t,ts) *
          kernel forwardBit (d+1) (t,ts) (z,zs)) =
        (inverseBit u t*forwardBit t z)*(if us=zs then (4:Int)^d else 0) := by
      have eqf : (fun ts => kernel inverseBit (d+1) (u,us) (t,ts) *
          kernel forwardBit (d+1) (t,ts) (z,zs)) =
        (fun ts => (inverseBit u t*forwardBit t z) *
          (kernel inverseBit d us ts*kernel forwardBit d ts zs)) := by
        funext ts; simp only [kernel]; ac_rfl
      rw [eqf,cube_scale,ih]
    rw [cubeSum,branch,branch,← Int.add_mul]
    change _ = if ((u,us) : Bool × Mask d) = (z,zs) then _ else _
    simp only [Prod.mk.injEq]
    cases u <;> cases z <;> by_cases he : us=zs <;>
      simp [he,inverseBit,forwardBit,Int.pow_succ,Int.mul_comm]

theorem cube_swap (d e : Nat) (f : Mask d → Mask e → Int) :
    cubeSum d (fun x => cubeSum e (f x)) = cubeSum e (fun y => cubeSum d (fun x => f x y)) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change cubeSum d (fun x => cubeSum e (f (false,x))) +
      cubeSum d (fun x => cubeSum e (f (true,x))) = _
    rw [ih,ih,← cube_add]
    rfl

private theorem cube_scale_right (d : Nat) (c : Int) (f : Mask d → Int) :
    cubeSum d (fun x => f x*c) = cubeSum d f*c := by
  simpa only [Int.mul_comm c] using cube_scale d c f

private theorem cube_point (d : Nat) (f : Mask d → Int) (z : Mask d) :
    cubeSum d (fun u => if u=z then f u else 0) = f z := by
  induction d with
  | zero => cases z; rfl
  | succ d ih =>
    rcases z with ⟨b,z⟩
    rw [cubeSum]
    change (cubeSum d (fun u => if ((false,u) : Bool × Mask d) = (b,z) then _ else _) +
      cubeSum d (fun u => if ((true,u) : Bool × Mask d) = (b,z) then _ else _)) = _
    cases b <;> simp [Prod.mk.injEq,ih,cube_const]

/-- Coefficients of a local payoff in observed signed features, scaled by
2^d. Any integer payoff on the exact local hit cell can be used. -/
def coefficient (d : Nat) (f : Mask d → Int) (t : Mask d) : Int :=
  cubeSum d (fun u => f u * kernel inverseBit d u t)

theorem decode_kernel (d : Nat) (f : Mask d → Int) (z : Mask d) :
    cubeSum d (fun t => coefficient d f t * kernel forwardBit d t z) =
      (4:Int)^d*f z := by
  unfold coefficient
  simp only [← cube_scale_right, Int.mul_assoc]
  rw [cube_swap]
  simp only [cube_scale,inverse_forward]
  have hf (u : Mask d) : f u * (if u=z then (4:Int)^d else 0) =
      if u=z then f u*4^d else 0 := by split <;> simp_all
  simp only [hf,cube_point,Int.mul_comm ((4:Int)^d)]

/-- Public estimator based on one log, shared by all its queried subsets. -/
def decodedLog (d : Nat) (f : Mask d → Int) (marks : Mask d)
    (assigned jmark : Bool) (log : Option Bool) : Int :=
  cubeSum d (fun t => coefficient d f t * score d t marks assigned jmark log)

/-- A single training experiment has four public partition/pivot-sign
choices for each enumerated tail-sign assignment. -/
def integrateMarks (d : Nat) (F : Bool → Bool → Mask d → Int) : Int :=
  cubeSum d (fun s => F false false s + F false true s + F true false s + F true true s)

private theorem integrate_scale (d : Nat) (c : Int) (F : Bool → Bool → Mask d → Int) :
    integrateMarks d (fun a b s => c*F a b s) = c*integrateMarks d F := by
  unfold integrateMarks
  simp only [← Int.mul_add,cube_scale]

private theorem integrate_features (d : Nat) (F : Mask d → Bool → Bool → Mask d → Int) :
    integrateMarks d (fun a b s => cubeSum d (fun t => F t a b s)) =
      cubeSum d (fun t => integrateMarks d (F t)) := by
  unfold integrateMarks
  simp only [← cube_add]
  exact cube_swap d d _

structure Word (d : Nat) where
  before : List (Bool × Bool)
  left : List (Bool × Bool)
  pivotHit : Bool
  tailHits : Mask d
  after : List (Bool × Bool)

def eligible {d : Nat} (w : Word d) := clear w.before && clear w.left && w.pivotHit

def observed {d : Nat} (w : Word d) (other : Bool → Mask d → Option Bool)
    (assigned jmark : Bool) (s : Mask d) : Option Bool :=
  if assigned then stopped w.before w.left (slots d w.tailHits s) w.after w.pivotHit jmark
  else other jmark s

/-- Exact single-word reconstruction of any local payoff. Divide the
estimator by 2^d and average it over its 4·2^d public outcomes. -/
theorem one_word_unbiased (d : Nat) (f : Mask d → Int) (w : Word d)
    (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s => decodedLog d f s a b (observed w other a b s)) =
      4*(4:Int)^d*(if eligible w then f w.tailHits else 0) := by
  unfold decodedLog
  rw [integrate_features]
  simp only [integrate_scale]
  have hg (t : Mask d) :
      integrateMarks d (fun a b s => score d t s a b (observed w other a b s)) =
        (if eligible w then 4 else 0)*kernel forwardBit d t w.tailHits :=
    stopped_forward d t w.tailHits w.before w.left w.after w.pivotHit other
  simp only [hg]
  by_cases h : eligible w
  · simp only [h,if_true]
    have hmul (t : Mask d) : coefficient d f t*(4*kernel forwardBit d t w.tailHits) =
        4*(coefficient d f t*kernel forwardBit d t w.tailHits) := by ac_rfl
    simp only [hmul,cube_scale,decode_kernel,Int.mul_assoc]
  · simp [h,cube_const]

def sumOn {α : Type} (xs : List α) (f : α → Int) := (xs.map f).sum

/-- Summing over an arbitrary finite population is sufficient for every
rational finite law, by repeating words according to integer weights. -/
theorem population_unbiased (d : Nat) (f : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    sumOn law (fun w => integrateMarks d
      (fun a b s => decodedLog d f s a b (observed w (other w) a b s))) =
      (4*(4:Int)^d)*sumOn law (fun w => if eligible w then f w.tailHits else 0) := by
  induction law with
  | nil => simp [sumOn]
  | cons w ws ih =>
    change integrateMarks d _ + sumOn ws _ = 4*4^d*((if eligible w then f w.tailHits else 0)+sumOn ws _)
    rw [one_word_unbiased,ih,Int.mul_add]

/-- Local centered survival of a prefix: was the distinguished minimum
tested, was any other local hit tested, and would the natural prefix survive? -/
def prefixPayoff (d : Nat) (tailPrefix : Mask d) (includesPivot referenceSurvives : Bool)
    (z : Mask d) : Int :=
  (if !includesPivot && noPositiveHit (slots d z tailPrefix) then 1 else 0) -
  (if referenceSurvives then 1 else 0)

theorem population_prefix_unbiased (d : Nat) (tailPrefix : Mask d)
    (includesPivot referenceSurvives : Bool) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    let f := prefixPayoff d tailPrefix includesPivot referenceSurvives
    sumOn law (fun w => integrateMarks d
      (fun a b s => decodedLog d f s a b (observed w (other w) a b s))) =
      (4*(4:Int)^d)*sumOn law (fun w => if eligible w then f w.tailHits else 0) :=
  population_unbiased _ _ _ _

def weight : (d : Nat) → Mask d → Nat
  | 0,_ => 0
  | d+1,(b,bs) => weight d bs + if b then 1 else 0

private theorem forward_heavy (d : Nat) (t z : Mask d) (h : weight d z < weight d t) :
    kernel forwardBit d t z = 0 := by
  induction d with
  | zero => simp [weight] at h
  | succ d ih =>
    rcases t with ⟨t,ts⟩; rcases z with ⟨z,zs⟩
    cases t <;> cases z <;> simp [weight,kernel,forwardBit] at h ⊢ <;>
      rw [ih ts zs (by omega)] <;> simp

def linearLog (d : Nat) (c : Mask d → Int) (marks : Mask d)
    (assigned jmark : Bool) (log : Option Bool) : Int :=
  cubeSum d (fun t => c t * score d t marks assigned jmark log)

theorem one_word_field (d : Nat) (c : Mask d → Int) (w : Word d)
    (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s => linearLog d c s a b (observed w other a b s)) =
      (if eligible w then 4 else 0)*cubeSum d (fun t => c t*kernel forwardBit d t w.tailHits) := by
  unfold linearLog
  rw [integrate_features]
  simp only [integrate_scale]
  have hb (t : Mask d) :
      integrateMarks d (fun a b s => score d t s a b (observed w other a b s)) =
      (if eligible w then 4 else 0)*kernel forwardBit d t w.tailHits :=
    stopped_forward d t w.tailHits w.before w.left w.after w.pivotHit other
  simp only [hb]
  rw [← cube_scale]
  congr 1
  funext t; ac_rfl

/-- Keep at most h tail coordinates per queried subset. The pivot itself
adds one to obtain the manuscript's total hit cap. -/
def limited (d h : Nat) (c : Mask d → Int) (t : Mask d) : Int :=
  if weight d t ≤ h then c t else 0

theorem capped_unbiased (d h : Nat) (f : Mask d → Int) (w : Word d)
    (hcap : weight d w.tailHits ≤ h) (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s =>
      linearLog d (limited d h (coefficient d f)) s a b (observed w other a b s)) =
      4*(4:Int)^d*(if eligible w then f w.tailHits else 0) := by
  rw [one_word_field]
  have ht (t : Mask d) : limited d h (coefficient d f) t * kernel forwardBit d t w.tailHits =
      coefficient d f t * kernel forwardBit d t w.tailHits := by
    unfold limited
    split
    · rfl
    · rename_i hh
      rw [forward_heavy d t w.tailHits (by omega)]
      simp
  simp only [ht,decode_kernel]
  cases eligible w <;> simp [Int.mul_assoc]

/-- The tail cap is needed only when j is the first hit. In particular a
word with h+1 tail hits and no pivot contributes zero, as required by a
global cap of h+1 true hits. -/
theorem capped_when_eligible (d h : Nat) (f : Mask d → Int) (w : Word d)
    (hcap : eligible w = true → weight d w.tailHits ≤ h) (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s =>
      linearLog d (limited d h (coefficient d f)) s a b (observed w other a b s)) =
      4*(4:Int)^d*(if eligible w then f w.tailHits else 0) := by
  by_cases he : eligible w=true
  · exact capped_unbiased d h f w (hcap he) other
  · rw [one_word_field]; simp [he]

private def gramWeight : (d : Nat) → Mask d → Int
  | 0,_ => 1
  | d+1,(b,bs) => (if b then 8 else 2)*gramWeight d bs

private theorem gram_weight_formula (d : Nat) (t : Mask d) :
    gramWeight d t = 2^d*(4:Int)^(weight d t) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases t with ⟨b,bs⟩
    cases b <;> simp only [weight,gramWeight,ih,if_true,if_false,Bool.false_eq_true,
      Nat.add_zero,Int.pow_succ]
    · ac_rfl
    · change (2*4:Int)*(2^d*4^(weight d bs)) = _
      ac_rfl

/-- Orthogonality proved by summing products over every actual fair sign
assignment, including the normalization of the diagonal character energy. -/
theorem walsh_orthogonality (d : Nat) (t u : Mask d) :
    cubeSum d (fun s => character d t s * character d u s) =
      if t=u then gramWeight d t else 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases t with ⟨t,ts⟩; rcases u with ⟨u,us⟩
    have br (b : Bool) :
        cubeSum d (fun ss => character (d+1) (t,ts) (b,ss)*character (d+1) (u,us) (b,ss)) =
        (charBit t b*charBit u b)*(if ts=us then gramWeight d ts else 0) := by
      have hfun : (fun ss => character (d+1) (t,ts) (b,ss)*character (d+1) (u,us) (b,ss)) =
        (fun ss => (charBit t b*charBit u b)*(character d ts ss*character d us ss)) := by
        funext ss; simp only [character]; ac_rfl
      rw [hfun,cube_scale,ih]
    rw [cubeSum,br,br,← Int.add_mul]
    change _ = if ((t,ts) : Bool × Mask d) = (u,us) then _ else _
    simp only [Prod.mk.injEq]
    cases t <;> cases u <;> by_cases he : ts=us <;> simp [he,charBit,gramWeight]

private theorem product_sums (d : Nat) (f g : Mask d → Int) :
    cubeSum d f * cubeSum d g = cubeSum d (fun t => cubeSum d (fun u => f t*g u)) := by
  simp only [cube_scale,cube_scale_right]

def polynomial (d : Nat) (c : Mask d → Int) (s : Mask d) : Int :=
  cubeSum d (fun t => c t*character d t s)

def spectralEnergy (d : Nat) (c : Mask d → Int) : Int :=
  cubeSum d (fun t => (c t*c t)*(4:Int)^(weight d t))

theorem walsh_square (d : Nat) (c : Mask d → Int) :
    cubeSum d (fun s => polynomial d c s * polynomial d c s) =
      2^d*spectralEnergy d c := by
  unfold polynomial
  have expand (s : Mask d) :
      cubeSum d (fun t => c t*character d t s) * cubeSum d (fun t => c t*character d t s) =
      cubeSum d (fun t => cubeSum d (fun u => (c t*c u)*(character d t s*character d u s))) := by
    rw [product_sums]
    congr 1; funext t; congr 1; funext u; ac_rfl
  simp only [expand]
  rw [cube_swap]
  have inner (t : Mask d) : cubeSum d (fun s =>
      cubeSum d (fun u => (c t*c u)*(character d t s*character d u s))) =
      (c t*c t)*gramWeight d t := by
    rw [cube_swap]
    simp only [cube_scale,walsh_orthogonality]
    have hg (u : Mask d) : (c t*c u)*(if t=u then gramWeight d t else 0) =
        if u=t then (c t*c u)*gramWeight d t else 0 := by
      by_cases he : t=u <;> simp [he,eq_comm]
    simp only [hg,cube_point]
  simp only [inner,gram_weight_formula]
  unfold spectralEnergy
  rw [← cube_scale]
  congr 1; funext t; ac_rfl

private theorem cube_mono (d : Nat) (f g : Mask d → Int) (h : ∀ s, f s ≤ g s) :
    cubeSum d f ≤ cubeSum d g := by
  induction d with
  | zero => exact h ()
  | succ d ih =>
    exact Int.add_le_add (ih _ _ (fun s => h (false,s))) (ih _ _ (fun s => h (true,s)))

private theorem sq_nonneg (v : Int) : 0 ≤ v*v := by
  rw [← Int.natAbs_mul_self]; omega

theorem observed_linear (d : Nat) (c : Mask d → Int) (s : Mask d) (a b : Bool)
    (log : Option Bool) :
    linearLog d c s a b log =
      if a && !b && (log == some true) then 4*polynomial d c s else 0 := by
  unfold linearLog score polynomial
  split
  · rw [← cube_scale]
    congr 1; funext t; ac_rfl
  · simp [cube_const]

/-- Four public coin cases and 2^d tail signs. After dividing by their
number the second moment on an eligible word is at most 4 times the
weighted squared coefficient sum; an ineligible word has zero second moment. -/
theorem observed_second_moment (d : Nat) (c : Mask d → Int) (w : Word d)
    (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s =>
      let v := linearLog d c s a b (observed w other a b s)
      v*v) ≤
    (if eligible w then 16 else 0)*(2^d*spectralEnergy d c) := by
  rw [← walsh_square,←cube_scale]
  unfold integrateMarks
  apply cube_mono
  intro s
  simp only [observed_linear,observed, Bool.false_and,Bool.true_and,
    Bool.not_true,Bool.not_false,if_true,if_false,Bool.false_eq_true,
    Int.zero_mul,Int.add_zero,Int.zero_add]
  have obs := negative_first w.before w.left (slots d w.tailHits s) w.after w.pivotHit
  change _ ↔ (eligible w && noPositiveHit (slots d w.tailHits s)) = true at obs
  by_cases hg : eligible w <;> by_cases hs : noPositiveHit (slots d w.tailHits s) <;>
    simp [hg,hs] at obs ⊢ <;> simp [obs]
  all_goals first
    | have he : (4*polynomial d c s)*(4*polynomial d c s) =
          16*(polynomial d c s * polynomial d c s) := by
        change ((4:Int)*_)*(4*_) = (4*4)*(_*_); ac_rfl
      rw [he]; exact Int.le_refl _
    | exact Int.mul_nonneg (by decide) (sq_nonneg _)

private def absWeight : (d : Nat) → Mask d → Nat
  | 0,_ => 1
  | d+1,(b,bs) => (if b then 3 else 2)*absWeight d bs

private theorem coefficient_cons (d : Nat) (f : Mask (d+1) → Int) (b : Bool) (t : Mask d) :
    coefficient (d+1) f (b,t) =
      inverseBit false b * coefficient d (fun u => f (false,u)) t +
      inverseBit true b * coefficient d (fun u => f (true,u)) t := by
  unfold coefficient
  rw [cubeSum]
  have br (v : Bool) :
      cubeSum d (fun u => f (v,u)*kernel inverseBit (d+1) (v,u) (b,t)) =
        inverseBit v b * cubeSum d (fun u => f (v,u)*kernel inverseBit d u t) := by
    rw [← cube_scale]; congr 1; funext u; simp only [kernel]; ac_rfl
  rw [br,br]

private theorem coefficient_bound (d : Nat) (f : Mask d → Int)
    (hf : ∀ z, (f z).natAbs ≤ 1) (t : Mask d) :
    (coefficient d f t).natAbs ≤ absWeight d t := by
  induction d with
  | zero => simpa [coefficient,cubeSum,kernel,absWeight] using hf ()
  | succ d ih =>
    rcases t with ⟨b,t⟩
    rw [coefficient_cons]
    have h0 := ih (fun u => f (false,u)) (fun u => hf (false,u)) t
    have h1 := ih (fun u => f (true,u)) (fun u => hf (true,u)) t
    apply Nat.le_trans (Int.natAbs_add_le _ _)
    cases b <;> simp [inverseBit,absWeight,Int.natAbs_mul] <;> omega

private theorem abs_weight_formula (d : Nat) (t : Mask d) :
    absWeight d t * absWeight d t * 4^(weight d t) = 4^d * 9^(weight d t) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases t with ⟨b,t⟩
    cases b
    · simp only [absWeight,weight,if_false,Bool.false_eq_true,Nat.add_zero,Nat.pow_succ]
      calc 2*absWeight d t*(2*absWeight d t)*4^(weight d t)
            = (2*2)*(absWeight d t*absWeight d t*4^(weight d t)) := by ac_rfl
           _ = _ := by rw [ih]; change 4*(4^d*9^(weight d t)) = _; ac_rfl
    · simp only [absWeight,weight,if_true,Nat.pow_succ]
      calc 3*absWeight d t*(3*absWeight d t)*(4^(weight d t)*4)
            = (3*3)*4*(absWeight d t*absWeight d t*4^(weight d t)) := by ac_rfl
           _ = _ := by rw [ih]; change 9*4*(4^d*9^(weight d t)) = _; ac_rfl

/-- Number of tail-query sets of cardinality at most h. -/
def smallCount : Nat → Nat → Nat
  | 0,_ => 1
  | _+1,0 => 1
  | d+1,h+1 => smallCount d (h+1) + smallCount d h

private theorem count_small (d h : Nat) :
    cubeSum d (fun t => if weight d t ≤ h then (1:Int) else 0) = (smallCount d h : Int) := by
  induction d generalizing h with
  | zero => simp [cubeSum,weight,smallCount]
  | succ d ih =>
    cases h with
    | zero =>
      have impossible (t : Mask d) : ¬ weight d t + 1 ≤ 0 := by omega
      have exactZero : smallCount d 0 = 1 := by cases d <;> rfl
      simp only [cubeSum,weight,Bool.false_eq_true,if_false,if_true,Nat.add_zero,
        Nat.not_succ_le_zero,cube_const,Int.mul_zero,Int.add_zero,smallCount]
      simp only [impossible,if_false,cube_const,Int.mul_zero,Int.add_zero,ih,exactZero]
    | succ h =>
      simp only [cubeSum,weight,Bool.false_eq_true,if_false,if_true,Nat.add_zero,
        Nat.add_le_add_iff_right,ih,smallCount,Int.natCast_add]

theorem small_count_le (d h : Nat) : smallCount d h ≤ (d+1)^h := by
  induction d generalizing h with
  | zero => simp [smallCount]
  | succ d ih =>
    cases h with
    | zero => simp [smallCount]
    | succ h =>
      change smallCount d (h+1) + smallCount d h ≤ (d+2)^(h+1)
      calc _ ≤ (d+1)^(h+1)+(d+1)^h := Nat.add_le_add (ih (h+1)) (ih h)
           _ = (d+1)^h*(d+2) := by rw [Nat.pow_succ,Nat.mul_succ ((d+1)^h) (d+1)]
           _ ≤ (d+2)^h*(d+2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) h)
           _ = _ := (Nat.pow_succ _ _).symm

/-- The coefficient bound includes the 2^d scaling of the reported decoder.
After dividing by its square the energy is at most 9^h times the actual
number of tail subsets of size at most h. -/
theorem capped_energy (d h : Nat) (f : Mask d → Int) (hf : ∀ z, (f z).natAbs ≤ 1) :
    spectralEnergy d (limited d h (coefficient d f)) ≤
      ((4^d*9^h*smallCount d h : Nat):Int) := by
  let bound : Int := ((4^d*9^h : Nat):Int)
  have point (t : Mask d) :
      (limited d h (coefficient d f) t * limited d h (coefficient d f) t)*(4:Int)^(weight d t) ≤
      bound*(if weight d t ≤ h then 1 else 0) := by
    by_cases hi : weight d t ≤ h
    · simp only [limited,hi,if_true,Int.mul_one]
      have v := coefficient_bound d f hf t
      have hn : (coefficient d f t).natAbs*(coefficient d f t).natAbs*4^(weight d t) ≤ 4^d*9^h :=
        Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul v v))
          (by rw [abs_weight_formula]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hi))
      have hz := Int.ofNat_le.mpr hn
      rw [Int.natCast_mul _ (4^(weight d t)),Int.natAbs_mul_self] at hz
      simpa only [Int.natCast_mul,Int.natCast_pow,bound] using hz
    · simp [limited,hi]
  have hsum := cube_mono d _ _ point
  rw [cube_scale,count_small] at hsum
  simpa only [spectralEnergy, Int.natCast_mul, bound] using hsum

theorem prefix_payoff_bound (d : Nat) (r : Mask d) (hasJ reference : Bool) (z : Mask d) :
    (prefixPayoff d r hasJ reference z).natAbs ≤ 1 := by
  unfold prefixPayoff
  cases hasJ <;> cases reference <;> cases noPositiveHit (slots d z r) <;> decide

/-- At population level the square bound is proportional to the number
of words having j as their minimum, not the whole number of input words. -/
theorem population_second_moment (d : Nat) (c : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    sumOn law (fun w => integrateMarks d (fun a b s =>
      let v := linearLog d c s a b (observed w (other w) a b s)
      v*v)) ≤
    16*(law.countP eligible : Int)*(2^d*spectralEnergy d c) := by
  induction law with
  | nil => simp [sumOn]
  | cons w ws ih =>
    have hw := observed_second_moment d c w (other w)
    have hh := Int.add_le_add hw ih
    change integrateMarks d _ + sumOn ws _ ≤ _
    apply Int.le_trans hh
    cases he : eligible w <;>
      simp [List.countP_cons,he,Int.natCast_add,Int.add_mul,Int.mul_add] <;> omega

theorem bounded_population_second_moment (d h : Nat) (f : Mask d → Int)
    (hf : ∀ z, (f z).natAbs ≤ 1) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    sumOn law (fun w => integrateMarks d (fun a b s =>
      let v := linearLog d (limited d h (coefficient d f)) s a b (observed w (other w) a b s)
      v*v)) ≤
    16*(law.countP eligible : Int)*(2^d*((4^d*9^h*(d+1)^h : Nat):Int)) := by
  apply Int.le_trans (population_second_moment d _ law other)
  apply Int.mul_le_mul_of_nonneg_left _ (Int.mul_nonneg (by decide) (by omega))
  apply Int.mul_le_mul_of_nonneg_left _ (by exact Int.pow_nonneg (by decide))
  apply Int.le_trans (capped_energy d h f hf)
  exact Int.ofNat_le.mpr (Nat.mul_le_mul_left _ (small_count_le d h))

theorem sum_append {α : Type} (xs ys : List α) (f : α → Int) :
    sumOn (xs++ys) f = sumOn xs f+sumOn ys f := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    change f x+sumOn (xs++ys) f = (f x+sumOn xs f)+sumOn ys f
    rw [ih,Int.add_assoc]

theorem sum_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → Int) :
    sumOn (xs.flatMap f) g = sumOn xs (fun x => sumOn (f x) g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change sumOn (f x++xs.flatMap f) g = sumOn (f x) g + sumOn xs _
    rw [sum_append,ih]

private def visit : (d : Nat) → (Mask d → List Int) → List Int
  | 0,f => f ()
  | d+1,f => visit d (fun t => f (false,t)) ++ visit d (fun t => f (true,t))

private theorem integrate_visits (d : Nat) (f : Mask d → List Int) (g : Int → Int) :
    sumOn (visit d f) g = cubeSum d (fun s => sumOn (f s) g) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [visit,sum_append,ih,ih,cubeSum]

def wordTickets (d : Nat) (c : Mask d → Int) (w : Word d) (other : Bool → Mask d → Option Bool) :=
  visit d (fun s =>
    let v := fun a b => linearLog d c s a b (observed w other a b s)
    [v false false,v false true,v true false,v true true])

/-- Actual estimator tickets, with multiplicity, over independent word and
public signs. The size is the number of input tickets times 4·2^d. -/
def logTickets (d : Nat) (c : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :=
  law.flatMap (fun w => wordTickets d c w (other w))

private theorem integrate_tickets (d : Nat) (c : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) (g : Int → Int) :
    sumOn (logTickets d c law other) g = sumOn law (fun w => integrateMarks d
      (fun a b s => g (linearLog d c s a b (observed w (other w) a b s)))) := by
  rw [logTickets,sum_flatMap]
  congr 1; funext w
  rw [wordTickets,integrate_visits]
  unfold integrateMarks
  congr 1; funext s
  simp [sumOn,Int.add_assoc]

private theorem sum_one {α : Type} (xs : List α) : sumOn xs (fun _ => 1) = (xs.length : Int) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (1:Int)+sumOn xs (fun _ => 1) = ((xs.length+1 : Nat):Int)
    rw [ih,Int.natCast_succ,Int.add_comm]

theorem sum_const {α : Type} (xs : List α) (k : Int) :
    sumOn xs (fun _ => k) = (xs.length : Int)*k := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    change k+sumOn xs _ = ((xs.length+1 : Nat):Int)*k
    rw [ih,Int.natCast_succ,Int.add_mul,Int.one_mul,Int.add_comm]

theorem log_ticket_count (d : Nat) (c : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    (logTickets d c law other).length = law.length*(4*2^d) := by
  have ht := integrate_tickets d c law other (fun _ => 1)
  rw [sum_one] at ht
  simp only [integrateMarks,cube_const,sum_const] at ht
  have hg : (1+1+1+1:Int)=4 := by decide
  rw [hg,Int.mul_comm ((2:Int)^d) 4] at ht
  have eq : ((logTickets d c law other).length:Int) = ((law.length*(4*2^d):Nat):Int) := by
    simpa only [Int.natCast_mul,Int.natCast_pow] using ht
  omega

theorem actual_logged_mean (d h : Nat) (f : Mask d → Int) (law : List (Word d))
    (hcap : ∀ w ∈ law, weight d w.tailHits ≤ h)
    (other : Word d → Bool → Mask d → Option Bool) :
    sumOn (logTickets d (limited d h (coefficient d f)) law other) id =
      (4*(4:Int)^d)*sumOn law (fun w => if eligible w then f w.tailHits else 0) := by
  rw [integrate_tickets]
  simp only [id_eq]
  induction law with
  | nil => simp [sumOn]
  | cons w ws ih =>
    change integrateMarks d _ + sumOn ws _ = _*((if eligible w then f w.tailHits else 0)+sumOn ws _)
    rw [capped_unbiased d h f w (hcap w (by simp)),ih (fun w hw => hcap w (by simp [hw])),Int.mul_add]

private theorem ticket_energy (xs : List Int) :
    sumOn xs (fun v => v*v) = (SampleVariance.energy xs : Int) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x*x+sumOn xs _ = ((x.natAbs*x.natAbs+SampleVariance.energy xs : Nat):Int)
    rw [ih,Int.natCast_add,Int.natAbs_mul_self]

theorem actual_logged_energy (d h : Nat) (f : Mask d → Int) (hf : ∀ z, (f z).natAbs≤1)
    (law : List (Word d)) (other : Word d → Bool → Mask d → Option Bool) :
    SampleVariance.energy (logTickets d (limited d h (coefficient d f)) law other) ≤
      16*law.countP eligible*(2^d*(4^d*9^h*(d+1)^h)) := by
  apply Int.ofNat_le.mp
  rw [← ticket_energy,integrate_tickets]
  simpa only [Int.natCast_mul,Int.natCast_pow] using bounded_population_second_moment d h f hf law other

private theorem square_shift (k x s : Int) :
    (k*x-s)*(k*x-s) = k*k*(x*x) - (k*s+k*s)*x + s*s := by
  have h1 : (k*x)*(k*x) = k*k*(x*x) := by ac_rfl
  have h2 : (k*x)*s = k*s*x := by ac_rfl
  have h3 : s*(k*x) = k*s*x := by ac_rfl
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,h1,h2,h3]; omega

private theorem shifted_sum (k s : Int) (xs : List Int) :
    sumOn xs (fun x => (k*x-s)*(k*x-s)) =
      k*k*sumOn xs (fun x => x*x) - (k*s+k*s)*sumOn xs id + (xs.length : Int)*(s*s) := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    change (k*x-s)*(k*x-s)+sumOn xs _ =
      k*k*(x*x+sumOn xs _) - (k*s+k*s)*(x+sumOn xs id) + ((xs.length+1 : Nat):Int)*(s*s)
    rw [square_shift,ih,Int.natCast_succ]
    simp only [Int.mul_add,Int.add_mul,Int.one_mul]; omega

private theorem weight_sum_id (xs : List Int) : SampleVariance.weightedSum id xs = sumOn xs id := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change x+SampleVariance.weightedSum id xs=x+sumOn xs id; rw [ih]

/-- Usual inequality Var(V) ≤ E[V²], with the integral centering used by
the independent-sample module. -/
theorem centering_energy_le (xs : List Int) :
    SampleVariance.energy (SampleVariance.centered xs) ≤ xs.length*xs.length*SampleVariance.energy xs := by
  let k : Int := xs.length
  let s := sumOn xs id
  have he : (SampleVariance.energy (SampleVariance.centered xs):Int) =
      sumOn xs (fun x => (k*x-s)*(k*x-s)) := by
    rw [←ticket_energy]
    simp only [SampleVariance.centered,weight_sum_id,k,s,sumOn,List.map_map,Function.comp_def]
  apply Int.ofNat_le.mp
  rw [he,shifted_sum,ticket_energy,Int.natCast_mul,Int.natCast_mul]
  change k*k*(SampleVariance.energy xs : Int) -(k*s+k*s)*s+k*(s*s) ≤ k*k*(SampleVariance.energy xs : Int)
  rw [Int.add_mul,Int.mul_assoc k s s]
  have hn : 0 ≤ k*(s*s) := Int.mul_nonneg (by dsimp [k]; omega) (sq_nonneg s)
  omega

theorem centered_size (xs : List Int) (D n t : Nat)
    (h : 4*(D*D*SampleVariance.energy xs) ≤ xs.length*n*t*t) :
    4*(D*D*SampleVariance.energy (SampleVariance.centered xs)) ≤
      (SampleVariance.centered xs).length*n*(xs.length*t)*(xs.length*t) := by
  simp only [SampleVariance.centered,List.length_map] at h ⊢
  let K := xs.length
  have he := centering_energy_le xs
  calc 4*(D*D*SampleVariance.energy (SampleVariance.centered xs))
           ≤ 4*(D*D*(K*K*SampleVariance.energy xs)) :=
             Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ he)
       _ = (K*K)*(4*(D*D*SampleVariance.energy xs)) := by ac_rfl
       _ ≤ (K*K)*(K*n*t*t) := Nat.mul_le_mul_left _ h
       _ = _ := by ac_rfl

/-- An explicit sample size for one local prefix contribution. The
integer threshold a/D is in original payoff units (the recorded linear
score itself has scale 2^d). Eligibility counts the actual words for
which this pivot is the minimum. For a hit cap H, h=H−1. -/
theorem local_prefix_concentration (d h : Nat) (r : Mask d) (hasJ reference : Bool)
    (law : List (Word d)) (other : Word d → Bool → Mask d → Option Bool)
    {n a D : Nat} (hn : 0<n) (ha : 0<a) (hD : 0<D) (hK : 0<law.length)
    (hsize : 16*D*D*law.countP eligible*(9^h*(d+1)^h) ≤ law.length*n*a*a) :
    let f := prefixPayoff d r hasJ reference
    let xs := logTickets d (limited d h (coefficient d f)) law other
    let blocks := SampleVariance.sampleSums (SampleVariance.centered xs) n
    3*blocks.length ≤ 4*SampleVariance.goodCount blocks (n*(xs.length*(2^d*a))) D := by
  let f := prefixPayoff d r hasJ reference
  let xs := logTickets d (limited d h (coefficient d f)) law other
  have he := actual_logged_energy d h f (prefix_payoff_bound d r hasJ reference) law other
  have ht : xs.length = law.length*(4*2^d) := log_ticket_count _ _ _ _
  have h2 : 4^d = (2^d)*(2^d) := Nat.mul_pow 2 2 d
  have hraw : 4*(D*D*SampleVariance.energy xs) ≤ xs.length*n*(2^d*a)*(2^d*a) := by
    rw [ht]
    calc 4*(D*D*SampleVariance.energy xs)
          ≤ 4*(D*D*(16*law.countP eligible*(2^d*(4^d*9^h*(d+1)^h)))) :=
            Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ he)
         _ = (4*2^d*4^d)*(16*D*D*law.countP eligible*(9^h*(d+1)^h)) := by ac_rfl
         _ ≤ (4*2^d*4^d)*(law.length*n*a*a) := Nat.mul_le_mul_left _ hsize
         _ = _ := by rw [h2]; ac_rfl
  have hc := centered_size xs D n (2^d*a) hraw
  have hlen : 0<xs.length := ht ▸ Nat.mul_pos hK (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
  apply SampleVariance.block_three_quarters (SampleVariance.centered xs)
    (SampleVariance.centered_mean_zero xs) _ hn (Nat.mul_pos hlen (Nat.mul_pos (Nat.pow_pos (by decide)) ha)) hD hc
  simpa only [SampleVariance.centered,List.length_map] using hlen

/-- The two shifted blockings used by the actual public design. For every
j at least one blocking keeps the whole interval [j,j+2W] together. -/
theorem two_shift_cover (W j : Nat) :
    let b := 2*W+1
    ∃ offset, (offset=0 ∨ offset=b) ∧
      ∀ i, j≤i → i≤j+2*W → (j+offset)/(2*b)=(i+offset)/(2*b) := by
  let b := 2*W+1
  let D := 2*b
  have hp : 0<D := by dsimp [D,b]; omega
  have hb : b<D := by dsimp [D,b]; omega
  have hW : 2*W<D := by dsimp [D,b]; omega
  have hsum : b+2*W<D := by dsimp [D,b]; omega
  have span (offset : Nat) (h : (j+offset)/D=(j+2*W+offset)/D) (i : Nat)
      (h1 : j≤i) (h2 : i≤j+2*W) : (j+offset)/D=(i+offset)/D := by
    have mono {x y : Nat} (hh : x ≤ y) : x/D ≤ y/D :=
      (Nat.le_div_iff_mul_le hp).mpr (Nat.le_trans (Nat.div_mul_le_self x D) hh)
    have hl := mono (Nat.add_le_add_right h1 offset)
    have hu := mono (Nat.add_le_add_right h2 offset)
    omega
  by_cases small : j%D<b
  · refine ⟨0,Or.inl rfl,span 0 ?_⟩
    simp only [Nat.add_zero]
    rw [Nat.add_div (a:=j) (b:=2*W) hp,Nat.div_eq_of_lt hW,Nat.mod_eq_of_lt hW]
    have hnone : ¬ D≤j%D+2*W := by dsimp [D,b] at *; omega
    simp only [if_neg hnone,Nat.add_zero]
  · refine ⟨b,Or.inr rfl,span b ?_⟩
    rw [Nat.add_right_comm j (2*W) b,Nat.add_assoc]
    rw [Nat.add_div (a:=j) (b:=b) hp,Nat.add_div (a:=j) (b:=b+2*W) hp,
      Nat.div_eq_of_lt hb,Nat.mod_eq_of_lt hb,Nat.div_eq_of_lt hsum,Nat.mod_eq_of_lt hsum]
    have hc1 : D≤j%D+b := by dsimp [D,b] at *; omega
    have hc2 : D≤j%D+(b+2*W) := by omega
    rw [if_pos hc1,if_pos hc2]

/-- A prefix of a permutation whose inverse ranks satisfy displacement W
is decided outside its central strip. Labels and ranks here start at zero. -/
theorem displaced_prefix_band (rank : Nat → Nat) (W t : Nat)
    (hdis : ∀ i, rank i≤i+W ∧ i≤rank i+W) :
    (∀ i, i+W<t → rank i<t) ∧ (∀ i, t+W≤i → ¬rank i<t) := by
  constructor
  · intro i h; have hi := (hdis i).1; omega
  · intro i h; have hi := (hdis i).2; omega

/-- Centered survival outside the strip vanishes. Inside the strip, hits
past j+2W have no effect, so the exact local payoff equals whole-word
centered survival. A hit set is enumerated as j followed by its other hits. -/
theorem displaced_local_survival (rank : Nat → Nat) (W t j : Nat) (hits : List Nat)
    (hdis : ∀ i, rank i≤i+W ∧ i≤rank i+W) (hmin : ∀ i ∈ hits, j≤i) :
    let R := fun i => decide (rank i<t)
    let natural := fun i : Nat => decide (i<t)
    let Z := j::hits
    let Zlocal := j::hits.filter (fun i => decide (i≤j+2*W))
    ((!Z.any R) = ((!Z.any natural))) ∨
      ((j+W≥t ∧ j<t+W) ∧ (!Z.any R) = (!Zlocal.any R)) := by
  dsimp only
  obtain ⟨low,high⟩ := displaced_prefix_band rank W t hdis
  by_cases early : j+W<t
  · exact Or.inl (by simp [List.any_cons,low j early,show j<t by omega])
  by_cases late : t+W≤j
  · left
    have hfalse {i} (hi : j≤i) : ¬rank i<t ∧ ¬i<t := by
      have := high i (by omega); omega
    have rzero : hits.any (fun i => decide (rank i<t)) = false := by
      apply List.any_eq_false.mpr
      intro i hi; simp [(hfalse (hmin i hi)).1]
    have nzero : hits.any (fun i => decide (i<t)) = false := by
      apply List.any_eq_false.mpr
      intro i hi; simp [(hfalse (hmin i hi)).2]
    simp [List.any_cons,(hfalse (Nat.le_refl j)).1,(hfalse (Nat.le_refl j)).2,rzero,nzero]
  right
  refine ⟨⟨by omega,by omega⟩,?_⟩
  have filter_same :
      hits.any (fun i => decide (rank i<t)) =
      (hits.filter (fun i => decide (i≤j+2*W))).any (fun i => decide (rank i<t)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨i,hi,hr⟩
      have bound := (hdis i).2
      exact ⟨i,⟨hi,by omega⟩,hr⟩
    · rintro ⟨i,⟨hi,_⟩,hr⟩; exact ⟨i,hi,hr⟩
  simp only [List.any_cons,filter_same]

/-- On a shared global first-hit record Y, every local index j computes
a contribution supported on Y=j. Their cross products vanish pointwise. -/
theorem only_reported_square {α : Type} (indices : List Nat) (hd : indices.Nodup)
    (record : α) (Y : α → Option Nat) (v : Nat → α → Int) :
    let contribution := fun j => if Y record=some j then v j record else 0
    sumOn indices contribution * sumOn indices contribution =
      sumOn indices (fun j => contribution j*contribution j) := by
  dsimp only
  induction indices with
  | nil => simp [sumOn]
  | cons j js ih =>
    obtain ⟨hnot,hrest⟩ := List.nodup_cons.mp hd
    change ((if Y record=some j then v j record else 0)+sumOn js _)*
      ((if Y record=some j then v j record else 0)+sumOn js _) =
      (if Y record=some j then v j record else 0)*(if Y record=some j then v j record else 0)+sumOn js _
    by_cases he : Y record=some j
    · have hz : sumOn js (fun i => if Y record=some i then v i record else 0) = 0 := by
        have hmap : js.map (fun i => if Y record=some i then v i record else 0) =
            js.map (fun _ => (0:Int)) := by
          apply List.map_congr_left
          intro i hi
          have hn : j≠i := fun h => hnot (h ▸ hi)
          simp [he,hn]
        simpa [sumOn,hmap] using sum_const js (0:Int)
      rw [← ih hrest,hz]; simp
    · simp [he,ih hrest]

private theorem swap_lists {α β : Type} (xs : List α) (ys : List β) (g : α → β → Int) :
    sumOn xs (fun x => sumOn ys (g x)) = sumOn ys (fun y => sumOn xs (fun x => g x y)) := by
  have add {γ : Type} (l : List γ) (a b : γ → Int) :
      sumOn l (fun z => a z+b z) = sumOn l a+sumOn l b := by
    induction l with
    | nil => rfl
    | cons z zs ih => change a z+b z+sumOn zs _ = (a z+sumOn zs a)+(b z+sumOn zs b); rw [ih]; ac_rfl
  induction xs with
  | nil =>
    change 0 = sumOn ys (fun _ => 0)
    rw [sum_const, Int.mul_zero]
  | cons x xs ih =>
    change sumOn ys (g x)+sumOn xs _ = sumOn ys (fun y => g x y+sumOn xs _)
    rw [add,ih]

def projection {α : Type} (Y : α → Option Nat) (v : Nat → α → Int) (j : Nat) (x : α) : Int :=
  if Y x=some j then v j x else 0

def sharedTickets {α : Type} (xs : List α) (js : List Nat)
    (Y : α → Option Nat) (v : Nat → α → Int) :=
  xs.map (fun x => sumOn js (fun j => projection Y v j x))

/-- Per-minimum square certificates add exactly on a common first-hit log.
No independence across minima is required. -/
theorem shared_energy {α : Type} (xs : List α) (js : List Nat) (hd : js.Nodup)
    (Y : α → Option Nat) (v : Nat → α → Int) :
    ((SampleVariance.energy (sharedTickets xs js Y v)):Int) =
      sumOn js (fun j => ((SampleVariance.energy (xs.map (projection Y v j))):Int)) := by
  rw [← ticket_energy]
  simp only [sharedTickets,sumOn,List.map_map,Function.comp_def]
  have hsq := fun x => only_reported_square js hd x Y v
  change sumOn xs (fun x => sumOn js (fun j => projection Y v j x) * sumOn js (fun j => projection Y v j x)) = _
  have h (x : α) : sumOn js (fun j => projection Y v j x)*sumOn js (fun j => projection Y v j x) =
      sumOn js (fun j => projection Y v j x*projection Y v j x) := hsq x
  simp only [h]
  rw [swap_lists]
  change sumOn js _ = sumOn js _
  congr 1; funext j
  rw [← ticket_energy]
  simp [sumOn,List.map_map,Function.comp_def]

/-- A whole prefix evaluated on one shared record per word. A separate
per-pivot variance certificate can be used for each projection. The only
probabilistic hypothesis here is the numerical second-moment limit for
each projection; actual_logged_energy supplies it on the local design. -/
theorem shared_block_guarantee {α : Type} (rows : List α) (js : List Nat) (hd : js.Nodup)
    (Y : α → Option Nat) (v : Nat → α → Int) {B N T D : Nat}
    (hB : ∀ j ∈ js, SampleVariance.energy (rows.map (projection Y v j)) ≤ B)
    (hrows : 0<rows.length) (hn : 0<N) (ht : 0<T) (hD : 0<D)
    (hsize : 4*(D*D*(js.length*B)) ≤ rows.length*N*T*T) :
    let scores := sharedTickets rows js Y v
    let blocks := SampleVariance.sampleSums (SampleVariance.centered scores) N
    3*blocks.length ≤ 4*SampleVariance.goodCount blocks (N*(scores.length*T)) D := by
  let scores := sharedTickets rows js Y v
  have eqK : scores.length=rows.length := List.length_map _
  have hm : ∀ l : List Nat, (∀ j ∈ l, SampleVariance.energy (rows.map (projection Y v j)) ≤ B) →
      sumOn l (fun j => ((SampleVariance.energy (rows.map (projection Y v j))):Int)) ≤ ((l.length*B:Nat):Int) := by
    intro l
    induction l with
    | nil => intro _; simp [sumOn]
    | cons j l ih =>
      intro hh
      have hb := Int.ofNat_le.mpr (hh j (by simp))
      have hr := ih (fun j hj => hh j (by simp [hj]))
      have hcomb := Int.add_le_add hb hr
      change _ + sumOn l _ ≤ ((l.length+1)*B:Nat)
      simpa only [Nat.add_mul,Nat.one_mul,Int.natCast_add,Int.add_comm (B:Int)] using hcomb
  have he : SampleVariance.energy scores ≤ js.length*B := by
    apply Int.ofNat_le.mp
    rw [shared_energy rows js hd Y v]
    exact hm js hB
  have hc := centered_size scores D N T (by
    rw [eqK]
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ he)) hsize)
  have hk : 0<scores.length := eqK ▸ hrows
  apply SampleVariance.block_three_quarters _ (SampleVariance.centered_mean_zero scores) _ hn
    (Nat.mul_pos hk ht) hD hc
  simpa only [SampleVariance.centered,List.length_map] using hk

def windowCode : (d start : Nat) → (Nat → Bool) → Mask d
  | 0,_,_ => ()
  | d+1,start,p => (p start,windowCode d (start+1) p)

private theorem window_injective (d start : Nat) (p q : Nat → Bool)
    (h : windowCode d start p = windowCode d start q) :
    ∀ i, start≤i → i<start+d → p i=q i := by
  induction d generalizing start with
  | zero => intro i h1 h2; omega
  | succ d ih =>
    have eq : (p start,windowCode d (start+1) p) = (q start,windowCode d (start+1) q) := h
    obtain ⟨first,rest⟩ := Prod.mk.inj eq
    intro i h1 h2
    by_cases hs : start=i
    · simpa [hs] using first
    · exact ih (start+1) rest i (by omega) (by omega)

def inBand (W t : Nat) (p : Nat → Bool) : Prop :=
   (∀ i, i+W<t → p i=true) ∧ (∀ i, t+W≤i → p i=false)

theorem band_code_injective (W t : Nat) (p q : Nat → Bool)
    (hp : inBand W t p) (hq : inBand W t q)
    (hcode : windowCode (2*W) (t-W) p = windowCode (2*W) (t-W) q) : p=q := by
  funext i
  by_cases low : i+W<t
  · rw [hp.1 i low,hq.1 i low]
  by_cases high : t+W≤i
  · rw [hp.2 i high,hq.2 i high]
  exact window_injective (2*W) (t-W) p q hcode i (by omega) (by omega)

private def allMasks : (d : Nat) → List (Mask d)
  | 0 => [()]
  | d+1 => ((allMasks d).map (false,·)) ++ ((allMasks d).map (true,·))

private theorem mem_masks (d : Nat) (s : Mask d) : s ∈ allMasks d := by
  induction d with
  | zero => cases s; simp [allMasks]
  | succ d ih =>
    rcases s with ⟨s,ss⟩
    cases s <;> simp [allMasks,ih]

private theorem masks_length (d : Nat) : (allMasks d).length=2^d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [allMasks,List.length_append,List.length_map,ih,Nat.pow_succ]; omega

private theorem nodup_subset_length {α : Type} (xs ys : List α) (hd : xs.Nodup)
    (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hn,hr⟩ := List.nodup_cons.mp hd
    obtain ⟨a,b,rfl⟩ := List.append_of_mem (hs (by simp : x ∈ x::xs))
    have sub : xs ⊆ a++b := by
      intro z hz
      have hother : z≠x := fun he => hn (he ▸ hz)
      have : z ∈ a++x::b := hs (by simp [hz])
      simpa [List.mem_append,hother] using this
    have := ih (a++b) hr sub
    simp only [List.length_append,List.length_cons] at *; omega

/-- At a fixed prefix length, every legal membership function is encoded
by at most 2W bits even when the window extends beyond the menu. -/
theorem prefix_count (W t : Nat) (prefixes : List (Nat → Bool)) (hd : prefixes.Nodup)
    (hb : ∀ p ∈ prefixes, inBand W t p) : prefixes.length ≤ 2^(2*W) := by
  let code := windowCode (2*W) (t-W)
  have nd : (prefixes.map code).Nodup := by
    induction prefixes with
    | nil => simp
    | cons p ps ih =>
      obtain ⟨hn,hr⟩ := List.nodup_cons.mp hd
      rw [List.map_cons,List.nodup_cons]
      refine ⟨?_,ih hr (fun q hq => hb q (by simp [hq]))⟩
      intro hp
      obtain ⟨q,hq,e⟩ := List.mem_map.mp hp
      have he := band_code_injective W t q p (hb q (by simp [hq])) (hb p (by simp)) e
      exact hn (he ▸ hq)
  have hl := nodup_subset_length (prefixes.map code) (allMasks (2*W)) nd (fun _ _ => mem_masks _ _)
  simpa only [List.length_map,masks_length] using hl

/-- Optimization step. If each candidate's sum of m prefix errors has
absolute discrepancy at most mδ, exact minimization of the estimated
cost gives true excess at most 2mδ. All quantities may be scaled integers. -/
theorem minimizing_estimated_cost {α : Type} (C estimated : α → Int) (chosen best : α)
    (m δ : Nat) (hc : C chosen ≤ estimated chosen + (m*δ:Nat))
    (hb : estimated best ≤ C best + (m*δ:Nat)) (hfit : estimated chosen ≤ estimated best) :
    C chosen - C best ≤ 2*((m*δ:Nat):Int) := by omega

end Screening.OneHitInversion

/- Source module: Screening.PrimeIntervalWitness -/

/-! Specialization of the calibrated hard law to the actual odd integers in
[2L,4L). All divisibility predicates are computed on the corresponding word.
The prime menu is an input, so its existence need not be an axiom. -/

namespace Screening.PrimeIntervalWitness
open Screening.IntervalCounts Screening.ArithmeticWitness Screening.CellLift Screening.MomentCube

def words (L : Nat) := (List.range L).map (word L)
def tag (menu : List Nat) (w : Nat) := menu.filter (fun p => decide (p ∣ w))
def count (ws : List Nat) (menu query : List Nat) :=
  ws.countP (fun w => decide (query ⊆ tag menu w))

theorem words_nodup (L : Nat) : (words L).Nodup := by
  apply List.pairwise_map.mpr
  exact (List.nodup_range (n := L)).imp (by
    intro x y ne eq
    unfold word at eq
    omega)

theorem mem_words (L w : Nat) :
    w∈words L ↔ 2*L ≤ w ∧ w < 4*L ∧ w%2=1 := by
  constructor
  · intro inside
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp inside
    have := List.mem_range.mp hk
    unfold word
    omega
  · rintro ⟨lower,upper,odd⟩
    apply List.mem_map.mpr
    refine ⟨w/2-L,List.mem_range.mpr (by omega),?_⟩
    unfold word
    omega

private theorem legal_info {menu c : List Nat} {h : Nat} (hc : c∈legalCells menu h) :
    c.Sublist menu ∧ c.length≤h := by simpa [legalCells,mem_cells] using hc

theorem complete_tags (menu : List Nat) (P L h : Nat) (positive : 0<P)
    (cap : 4*L < P^(h+1)) (unique : menu.Nodup) (prime : ∀p∈menu, IsPrime p)
    (lo : ∀p∈menu,P≤p) : ∀w∈words L,tag menu w∈legalCells menu h := by
  intro w hw
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hw
  have kfit := List.mem_range.mp hk
  exact List.mem_filter.mpr ⟨mem_cells.mpr List.filter_sublist,
    by simpa [tag] using natural_window_hit_cap kfit positive cap menu unique prime lo⟩

theorem literal_count (menu query : List Nat) (L : Nat) (inside : query ⊆ menu) :
    count (words L) menu query = containmentCount L L query := by
  unfold count words containmentCount
  rw [List.countP_map]
  apply List.countP_congr
  intro k _
  simp only [Function.comp_apply,decide_eq_true_eq,List.all_eq_true]
  constructor
  · intro hall x hx
    exact of_decide_eq_true (List.mem_filter.mp (hall hx)).2
  · intro hall x hx
    exact List.mem_filter.mpr ⟨inside hx,decide_eq_true (hall x hx)⟩

private theorem product_sub_dvd {xs ys : List Nat} (sub : xs.Sublist ys) :
    product xs ∣ product ys := by
  induction sub with
  | slnil => simp [product]
  | cons a _ ih => exact Nat.dvd_trans ih (Nat.dvd_mul_left _ a)
  | cons₂ a _ ih => exact Nat.mul_dvd_mul_left a ih

/-- On denominator L*U with U any multiple of the full menu product,
the target for q has numerator L*(U/product(q)). -/
def target (U L : Nat) (q : List Nat) : Int := (↑(L*(U/product q)):Int)

theorem product_target (menu c : List Nat) (U L : Nat) (multiple : product menu ∣ U)
    (sub : c.Sublist menu) : (L*(U/product c))*product c = L*U := by
  rw [Nat.mul_assoc,Nat.div_mul_cancel (Nat.dvd_trans (product_sub_dvd sub) multiple)]

theorem rounding_one_unit (menu : List Nat) (L h U : Nat) (multiple : product menu ∣ U)
    (unique : menu.Nodup)
    (prime : ∀p∈menu, IsPrime p) (odd : ∀p∈menu,p%2=1)
    (complete : ∀w∈words L,tag menu w∈legalCells menu h)
    (c : List Nat) (hc : c∈legalCells menu h) :
    (target U L c - histogramMoment
      (table (legalCells menu h) (fun s => U*fiberSize (words L) (tag menu) s)) c).natAbs ≤ U := by
  obtain ⟨sub,_⟩ := legal_info hc
  have cop := containment_eq L L c (sub.nodup unique) (fun p hp => prime p (sub.subset hp))
  have raw := count_error (odd_product c (fun p hp => odd p (sub.subset hp))) L L
  rw [← cop,← literal_count menu c L sub.subset] at raw
  let p := product c
  let n := count (words L) menu c
  let k := U/p
  have iden : k*p=U := Nat.div_mul_cancel (Nat.dvd_trans (product_sub_dvd sub) multiple)
  have dist : ((L:Int)-(↑(n*p):Int)).natAbs ≤ p := by
    change max (n*p-L) (L-n*p) < p at raw
    have s := Int.natAbs_eq ((L:Int)-(↑(n*p):Int))
    rcases s with h|h <;> omega
  rw [uniform_table_count _ _ _ _ _ (legal_unique menu h unique) complete]
  change ((↑(L*k):Int)-(↑(U*n):Int)).natAbs ≤ _
  have ident : (↑(L*k):Int)-(↑(U*n):Int) = (k:Int)*((L:Int)-(↑(n*p):Int)) := by
    rw [Int.mul_sub,← Int.natCast_mul,← Int.natCast_mul]
    rw [← iden]
    congr 2 <;> ac_rfl
  rw [ident,Int.natAbs_mul,Int.natAbs_ofNat]
  exact Nat.le_trans (Nat.mul_le_mul_left k dist) (Nat.le_of_eq iden)

private theorem count_sum (ws : List A) (f : A → Bool) :
    ws.countP f = sumNat ws (fun x => (f x).toNat) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (a::ws).countP f = (f a).toNat + sumNat ws (fun x => (f x).toNat)
    cases e : f a <;> simp [List.countP_cons,e,ih,Nat.add_comm]

private theorem sum_add (xs : List A) (f g : A → Nat) :
    sumNat xs (fun x => f x+g x) = sumNat xs f + sumNat xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x + g x + sumNat xs (fun z => f z+g z) = (f x+sumNat xs f)+(g x+sumNat xs g)
    omega

private theorem sum_const (xs : List A) (k : Nat) : sumNat xs (fun _ => k) = xs.length*k := by
  induction xs with
  | nil => simp [sumNat]
  | cons x xs ih => change k + sumNat xs (fun _ => k) = (xs.length+1)*k; rw [ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_mono (xs : List A) {f g : A → Nat} (le : ∀x∈xs, f x≤g x) :
    sumNat xs f≤sumNat xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.add_le_add (le x (by simp)) (ih (fun z hz => le z (by simp [hz])))

private theorem sum_swap (xs : List A) (ys : List B) (f : A→B→Nat) :
    sumNat xs (fun x => sumNat ys (f x)) = sumNat ys (fun y => sumNat xs (fun x => f x y)) := by
  induction xs with
  | nil => simpa [sumNat] using (sum_const ys 0).symm
  | cons x xs ih =>
    change sumNat ys (f x) + sumNat xs (fun x => sumNat ys (f x)) =
      sumNat ys (fun y => f x y + sumNat xs (fun x => f x y))
    rw [sum_add,ih]

private theorem member_le_sum (xs : List A) (f : A → Nat) (x : A) (mem : x∈xs) :
    f x ≤ sumNat xs f := by
  induction xs with
  | nil => simp at mem
  | cons z xs ih =>
    change f x ≤ f z + sumNat xs f
    rcases List.mem_cons.mp mem with eq|h
    · subst x; omega
    · have := ih h; omega

private theorem failed_subset (xs ys : List Nat) (no : ¬xs⊆ys) : ∃x∈xs,x∉ys := by
  induction xs with
  | nil => simp at no
  | cons z xs ih =>
    by_cases hz : z∈ys
    · have tail : ¬xs⊆ys := by
        intro hs
        apply no
        intro k hk
        rcases List.mem_cons.mp hk with he|hm
        · exact he ▸ hz
        · exact hs hm
      obtain ⟨k,hk,hn⟩ := ih tail
      exact ⟨k,by simp [hk],hn⟩
    · exact ⟨z,by simp,hz⟩

def extraCount (ws menu q : List Nat) (p : Nat) :=
  if p∈q then 0 else count ws menu (p::q)

/-- Union bound with exact physical meanings. A word containing q either
has exactly q as hits or also contains some new menu prime. -/
theorem contain_to_cell (ws menu q : List Nat) (unique : menu.Nodup) (sub : q.Sublist menu) :
    count ws menu q ≤ fiberSize ws (tag menu) q + sumNat menu (extraCount ws menu q) := by
  let row := fun w p => if p∈q then 0 else (decide (p::q ⊆ tag menu w)).toNat
  let mask := fun w => (decide (tag menu w=q)).toNat
  have each (w : Nat) : (decide (q⊆tag menu w)).toNat ≤ mask w + sumNat menu (row w) := by
    by_cases contains : q⊆tag menu w
    · by_cases eq : tag menu w=q
      · simp [mask,eq]
      · have ext : ¬tag menu w ⊆ q := fun h =>
          eq (Screening.WitnessOverlap.canonical_ext unique List.filter_sublist sub h contains)
        obtain ⟨p,hp,hq⟩ := failed_subset _ _ ext
        have union : p::q ⊆ tag menu w := by
          intro i hi
          rcases List.mem_cons.mp hi with he|hm
          · exact he ▸ hp
          · exact contains hm
        have bound := member_le_sum menu (row w) p (List.filter_sublist.subset hp)
        simp only [row,hq,if_false,union,decide_true,Bool.toNat_true] at bound
        simp only [contains,decide_true,Bool.toNat_true]
        exact Nat.le_trans bound (Nat.le_add_left _ _)
    · simp [contains]
  have fiber : sumNat ws mask = fiberSize ws (tag menu) q := by
    rw [← count_sum, List.countP_eq_length_filter]
    rfl
  have extra (p : Nat) : sumNat ws (fun w => row w p) = extraCount ws menu q p := by
    by_cases hp : p∈q
    · simp [row,extraCount,hp,sum_const]
    · simpa [row,extraCount,hp,count] using (count_sum ws (fun w => decide (p::q⊆tag menu w))).symm
  calc
    _ = sumNat ws (fun w => (decide (q⊆tag menu w)).toNat) := count_sum _ _
    _ ≤ sumNat ws (fun w => mask w+sumNat menu (row w)) := sum_mono ws (fun w _ => each w)
    _ = _ := by rw [sum_add, fiber, sum_swap]; simp only [extra]

/-- At full degree containment equals exact membership, with an arbitrary
menu order, provided the recorded tags respect the h-hit cap. -/
theorem full_cell_count (ws menu q : List Nat) (h : Nat) (unique : menu.Nodup)
    (sub : q.Sublist menu) (size : q.length=h) (cap : ∀w∈ws,(tag menu w).length ≤ h) :
    count ws menu q = fiberSize ws (tag menu) q := by
  unfold count fiberSize
  rw [← List.countP_eq_length_filter]
  apply List.countP_congr
  intro w hw
  simp only [decide_eq_true_eq]
  constructor
  · intro inc
    apply Screening.WitnessOverlap.canonical_ext unique List.filter_sublist sub _ inc
    intro p hp
    by_cases inside : p∈q
    · exact inside
    · have extra : p::q⊆tag menu w := by
        intro x hx
        rcases List.mem_cons.mp hx with he|hx
        · exact he ▸ hp
        · exact inc hx
      have nodes := Screening.WitnessOverlap.length_le_of_subset
        (List.nodup_cons.mpr ⟨inside,sub.nodup unique⟩) extra
      have limit := cap w hw
      simp only [List.length_cons] at nodes
      omega
  · rintro rfl; simp

private theorem product_upper (ps : List Nat) (Q : Nat) (hi : ∀ p∈ps,p≤Q) :
    product ps ≤ Q^ps.length := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    rw [product,List.length_cons,Nat.pow_succ,Nat.mul_comm p]
    exact Nat.mul_le_mul (ih (fun x hx => hi x (by simp [hx]))) (hi p (by simp))

private theorem product_positive (q : List Nat) (odd : ∀p∈q,p%2=1) : 0<product q := by
  have h := odd_product q odd
  omega

private theorem lower_algebra (L n f m p P : Nat) (sparse : 4*m ≤ P)
    (rounding : L ≤ n*p+p) (small : 4*((m+1)*p) ≤ L)
    (cover : n ≤ f + m*(L/(P*p)+1)) : L ≤ 2*f*p := by
  let k := L/(P*p)
  have gain1 : 4*(m*k*p) ≤ L := by
    calc
      _ = (4*m)*(k*p) := by ac_rfl
      _ ≤ P*(k*p) := Nat.mul_le_mul_right _ sparse
      _ = k*(P*p) := by ac_rfl
      _ ≤ _ := Nat.div_mul_le_self _ _
  have cover' := Nat.mul_le_mul_right p cover
  change n*p ≤ (f + m*(k+1))*p at cover'
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at cover' small
  simp only [Nat.one_mul] at small
  rw [Nat.mul_assoc]
  omega

/-- All actual exact cells, including the empty cell and every h-cell, have
at least L/(2 Q^j) words. For smaller cells this uses a union bound over one
extra menu prime. Full h-cells use the literal no-(h+1)-hits interval cap. -/
theorem physical_fiber_lower (menu : List Nat) (P Q L h : Nat)
    (positive : 0<P) (sparse : 4*menu.length≤P) (alphabet : menu.length+1≤Q)
    (large : 4*Q^h≤L) (cap : 4*L<P^(h+1)) (unique : menu.Nodup)
    (prime : ∀p∈menu,IsPrime p) (odd : ∀p∈menu,p%2=1)
    (lo : ∀p∈menu,P≤p) (hi : ∀p∈menu,p≤Q)
    (q : List Nat) (legal : q∈legalCells menu h) :
    L ≤ 2*fiberSize (words L) (tag menu) q*Q^q.length := by
  obtain ⟨sub,size⟩ := legal_info legal
  have inM {p : Nat} (hp : p∈q) := sub.subset hp
  let n := count (words L) menu q
  let f := fiberSize (words L) (tag menu) q
  let p := product q
  have ppos : 0<p := product_positive q (fun z hz => odd z (inM hz))
  have pmax : p≤Q^q.length := product_upper q Q (fun z hz => hi z (inM hz))
  have qpos : 0<Q := by omega
  have raw := count_error (odd_product q (fun z hz => odd z (inM hz))) L L
  rw [← containment_eq L L q (sub.nodup unique) (fun z hz => prime z (inM hz)),
    ← literal_count menu q L sub.subset] at raw
  change max (n*p-L) (L-n*p)<p at raw
  have base : L≤n*p+p := by omega
  have main : L≤2*f*p := by
    by_cases full : q.length=h
    · have allCap := complete_tags menu P L h positive cap unique prime lo
      have eq : n=f := full_cell_count (words L) menu q h unique sub full
        (fun w hw => (legal_info (allCap w hw)).2)
      have a : 4*p≤L := by rw [← full] at large; exact Nat.le_trans (Nat.mul_le_mul_left 4 pmax) large
      rw [eq] at base
      rw [Nat.mul_assoc]
      omega
    · have smaller : q.length+1≤h := by omega
      have lmax : 4*((menu.length+1)*p)≤L := by
        have top := Nat.pow_le_pow_right qpos smaller
        rw [Nat.pow_succ,Nat.mul_comm (Q^q.length) Q] at top
        exact Nat.le_trans (Nat.mul_le_mul_left 4 (Nat.le_trans (Nat.mul_le_mul alphabet pmax) top)) large
      have extra (r : Nat) (hr : r∈menu) : extraCount (words L) menu q r ≤ L/(P*p)+1 := by
        by_cases inQ : r∈q
        · simp [extraCount,inQ]
        · rw [extraCount,if_neg inQ]
          have oneIn : r::q⊆menu := by
            intro k hk
            rcases List.mem_cons.mp hk with he|hm
            · exact he ▸ hr
            · exact inM hm
          rw [literal_count _ _ _ oneIn,containment_eq L L _ (List.nodup_cons.mpr ⟨inQ,sub.nodup unique⟩)
            (fun k hk => prime k (oneIn hk))]
          have near := floor_or_ceiling (odd_product (r::q) (fun k hk => odd k (oneIn hk))) L L
          change hitCount L (r*p) L = L/(r*p) ∨ hitCount L (r*p) L = ceilingQuotient L (r*p) at near
          have divbound := Nat.div_le_div_left (Nat.mul_le_mul_right p (lo r hr)) (Nat.mul_pos positive ppos)
            (a := L)
          unfold ceilingQuotient at near
          rcases near with he | he
          · change hitCount L (r*p) L ≤ _
            omega
          · change hitCount L (r*p) L ≤ _
            split at he <;> omega
      have cover := contain_to_cell (words L) menu q unique sub
      have union := sum_mono menu extra
      rw [sum_const] at union
      exact lower_algebra L n f menu.length p P sparse base lmax
        (Nat.le_trans cover (Nat.add_le_add_left union f))
  exact Nat.le_trans main (Nat.mul_le_mul_left (2*f) pmax)

/-- Probability denominators are (L*U)*K. The fourth field states exact
reciprocal product probability without division, including the empty query.
The last field retains the actual signed change, including its sign, not
merely a bound on the resulting densities. -/
structure LiteralCertificate (menu : List Nat) (edges : List (List Nat)) (coef : List Nat→Int)
    (L h U b eps K : Nat) (weight : Nat→Nat) : Prop where
  positive : 0<K
  normalized : sumNat (words L) weight = (L*U)*K
  density : ∀w∈words L,
    (b-eps)*((L*U)*K) ≤ b*L*weight w ∧ b*L*weight w ≤ (b+eps)*((L*U)*K)
  lowerMoments : ∀q∈legalCells menu h, q.length<h →
    histogramMoment (wordAtoms (words L) (tag menu) weight) q * (product q : Int) =
      (↑((L*U)*K):Int)
  occupied : ∀c∈legalCells menu h,0<cellMass (words L) (tag menu) weight c
  signedCells : ∀c∈legalCells menu h,
    (cellMass (words L) (tag menu) weight c:Int) = (K:Int)*
      (exactMass (calibrated menu h
        (table (legalCells menu h) (fun s => U*fiberSize (words L) (tag menu) s))
        (target U L)) c + effect c coef edges)

/-- End-to-end finite arithmetic hard-law constructor. Its hypotheses only
concern the supplied menu, interval, rational amplitude, and distinct
canonical h-edges. Physical rounding and fiber lower bounds are proved. -/
theorem exists_prime_witness (menu : List Nat) (edges : List (List Nat)) (coef : List Nat→Int)
    (P Q L h U d b eps : Nat) (pPos : 0<P) (uPos : 0<U) (hPos : 0<h)
    (epsSmall : eps<b) (multiple : product menu ∣ U)
    (sparse : 4*menu.length≤P) (alphabet : menu.length+1≤Q) (large : 4*Q^h≤L)
    (cap : 4*L<P^(h+1)) (window : 4*b*Q^h ≤ eps*L)
    (ampScale : 4*b*d*Q^h ≤ eps*(L*U))
    (unique : menu.Nodup) (prime : ∀p∈menu,IsPrime p) (odd : ∀p∈menu,p%2=1)
    (lo : ∀p∈menu,P≤p) (hi : ∀p∈menu,p≤Q) (distinct : edges.Nodup)
    (canonical : ∀e∈edges,e.Sublist menu) (degree : ∀e∈edges,e.length=h)
    (amplitudes : ∀e∈edges,(coef e).natAbs≤d) :
    ∃ K weight, LiteralCertificate menu edges coef L h U b eps K weight := by
  have len : (words L).length=L := by simp [words]
  have positiveQ : 0<Q := by omega
  have pospow := Nat.pow_pos positiveQ (n := h)
  have posL : 0<L := by omega
  have comp := complete_tags menu P L h pPos cap unique prime lo
  have fibers := physical_fiber_lower menu P Q L h pPos sparse alphabet large cap unique prime odd lo hi
  have tot : target U L [] = (↑((words L).length*U):Int) := by simp [target,product,len]
  obtain ⟨K,weight,kpos,norm,density,occ,lows,shift⟩ := calibrated_physical_witness (words L)
    (tag menu) menu edges coef (target U L) h d U b eps Q hPos uPos (by simpa [len] using posL)
    epsSmall alphabet unique distinct canonical degree amplitudes comp
    (fun c hc => by simpa [len] using fibers c hc) (by simpa [len] using window)
    (by simpa [len] using ampScale) tot (rounding_one_unit menu L h U multiple unique prime odd comp)
  rw [len] at norm
  simp only [len] at density
  refine ⟨K,weight,kpos,norm,density,?_,occ,shift⟩
  intro q hq small
  rw [lows q hq small]
  have pscale := product_target menu q U L multiple (legal_info hq).1
  change ((K:Int)*(↑(L*(U/product q)):Int))*(product q:Int) = (↑((L*U)*K):Int)
  rw [Int.mul_assoc, ← Int.natCast_mul,pscale, ← Int.natCast_mul,Nat.mul_comm]

/-- A common scale that exactly represents the paper's specified amplitude
eps/(1000*b*(2P)^h), including when its denominator is not a power of two. -/
def paperScale (menu : List Nat) (P h b : Nat) :=
  product menu * (1000*b*(2*P)^h)

def paperAmplitude (menu : List Nat) (L eps : Nat) := eps*L*product menu

def signedCoefficient (d : Nat) (tagSign : List Nat→Bool) (e : List Nat) : Int :=
  if tagSign e then (d:Int) else -(d:Int)

theorem paper_amplitude_exact (menu : List Nat) (P L h b eps : Nat) :
    paperAmplitude menu L eps * (1000*b*(2*P)^h) = eps*(L*paperScale menu P h b) := by
  unfold paperAmplitude paperScale
  ac_rfl

/-- The signed h-edge construction in the hard-menu paragraph of the natural
window theorem. Any assignment of signs is permitted, hence so are signs
shared by all edges carrying the same tail vertex. -/
theorem paper_signed_family (menu : List Nat) (edges : List (List Nat)) (tagSign : List Nat→Bool)
    (P L h b eps : Nat) (pPos : 0<P) (hPos : 0<h) (epsSmall : eps<b)
    (sparse : 4*menu.length≤P) (cap : 4*L<P^(h+1))
    (calibrationWindow : 1000*b*(2*P)^h ≤ eps*L)
    (unique : menu.Nodup) (prime : ∀p∈menu,IsPrime p) (odd : ∀p∈menu,p%2=1)
    (lo : ∀p∈menu,P≤p) (hi : ∀p∈menu,p≤2*P) (distinct : edges.Nodup)
    (canonical : ∀e∈edges,e.Sublist menu) (degree : ∀e∈edges,e.length=h) :
    ∃ K weight, LiteralCertificate menu edges (signedCoefficient (paperAmplitude menu L eps) tagSign)
      L h (paperScale menu P h b) b eps K weight := by
  let Q := 2*P
  let d := paperAmplitude menu L eps
  let U := paperScale menu P h b
  have bPos : 0<b := by omega
  have powPos : 0<Q^h := Nat.pow_pos (by dsimp [Q]; omega)
  have uPos : 0<U := Nat.mul_pos (product_positive menu odd)
    (Nat.mul_pos (Nat.mul_pos (by decide) bPos) powPos)
  have mult : product menu ∣ U := Nat.dvd_mul_right _ _
  have coeffLe : 4*b*Q^h ≤ 1000*b*Q^h :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  have window : 4*b*Q^h≤eps*L := Nat.le_trans coeffLe calibrationWindow
  have large : 4*Q^h≤L := by
    apply Nat.le_of_mul_le_mul_left _ bPos
    calc
      b*(4*Q^h) = 4*b*Q^h := by ac_rfl
      _ ≤ eps*L := window
      _ ≤ b*L := Nat.mul_le_mul_right L (Nat.le_of_lt epsSmall)
  have ampl : 4*b*d*Q^h≤eps*(L*U) := by
    calc
      _ = d*(4*b*Q^h) := by ac_rfl
      _ ≤ d*(1000*b*Q^h) := Nat.mul_le_mul_left d coeffLe
      _ = _ := paper_amplitude_exact menu P L h b eps
  exact exists_prime_witness menu edges _ P Q L h U d b eps pPos uPos hPos epsSmall mult
    sparse (by dsimp [Q]; omega) large cap window ampl unique prime odd lo hi distinct canonical
    degree (fun e _ => by cases hs : tagSign e <;> simp [signedCoefficient,hs,d])

end Screening.PrimeIntervalWitness

/- Source module: Screening.HardBinRegret -/

/-! Signed prefix survival effects and projected sign inversions in the
hard-menu construction. Positions belonging to other bins may interleave. -/

namespace Screening.HardBinRegret
open Screening.MomentCube Screening.ArithmeticWitness

def avoids [DecidableEq V] (pre cell : List V) : Bool :=
  cell.all (fun v => decide (v∉pre))

def survival [DecidableEq V] (atoms : List (List V × Int)) (pre : List V) : Int :=
  sumOn atoms (fun a => if avoids pre a.1 then a.2 else 0)

private theorem missing [DecidableEq V] (xs ys : List V) (no : ¬xs⊆ys) : ∃v∈xs,v∉ys := by
  induction xs with
  | nil => simp at no
  | cons x xs ih =>
    by_cases hx : x∈ys
    · have tail : ¬xs⊆ys := by
        intro sub; apply no; intro z hz
        rcases List.mem_cons.mp hz with eq|h
        · exact eq ▸ hx
        · exact sub h
      obtain ⟨v,hv,hy⟩ := ih tail
      exact ⟨v,by simp [hv],hy⟩
    · exact ⟨x,by simp,hx⟩

/-- A signed cube changes survival exactly when the prefix includes every
vertex of its edge. Its mass there is the cube coefficient (not a parity sign). -/
theorem cube_survival [DecidableEq V] (edge pre : List V) (d : Int) (unique : edge.Nodup) :
    survival (cubeAtoms edge d) pre = if edge⊆pre then d else 0 := by
  let f := fun c => if avoids pre c then (1:Int) else 0
  have expand : survival (cubeAtoms edge d) pre = d * alternating edge f := by
    unfold survival cubeAtoms alternating
    rw [← sum_factor]
    change (((cells edge).map _).map _).sum = _
    simp only [List.map_map,Function.comp_def]
    apply sum_congr (cells edge)
    intro c _
    cases h : avoids pre c <;> simp [f,h]
  rw [expand]
  by_cases all : edge⊆pre
  · have point (c : List V) (hc : c∈cells edge) :
        (-1:Int)^c.length*f c = if c=[] then 1 else 0 := by
      cases c with
      | nil => simp [f,avoids]
      | cons x xs =>
        have seen : x∈pre := all ((mem_cells.mp hc).subset (by simp))
        simp [f,avoids,seen]
    have emptyCell : [] ∈ cells edge := mem_cells.mpr (by simp)
    have one : alternating edge f=1 := by
      unfold alternating
      rw [sum_congr _ point,sum_pick (cells edge) (fun _ => 1) [] (cells_nodup unique), if_pos emptyCell]
    simp [all,one]
  · obtain ⟨v,he,unseen⟩ := missing edge pre all
    have cancel := free_vertex_cancel edge v he f (by
      intro left right
      simp only [f,avoids,List.all_append,List.all_cons]
      simp only [unseen,not_false_eq_true,decide_true,Bool.true_and])
    simp [all,cancel]

theorem perturbed_survival [DecidableEq V] (base updates : List (List V × Int)) (pre : List V)
    (unique : ∀s∈updates,s.1.Nodup) :
    survival (addCubes base updates) pre =
      survival base pre + sumOn updates (fun s => if s.1⊆pre then s.2 else 0) := by
  induction updates with
  | nil => simp [addCubes,sumOn]
  | cons s ss ih =>
    obtain ⟨e,d⟩ := s
    change sumOn (cubeAtoms e d ++ addCubes base ss) _ =
      survival base pre + ((if e⊆pre then d else 0) + sumOn ss _)
    rw [ArithmeticWitness.sum_append]
    change survival (cubeAtoms e d) pre + survival (addCubes base ss) pre = _
    rw [cube_survival e pre d (unique (e,d) (by simp)), ih (fun s hs => unique s (by simp [hs]))]
    omega

def tailUpdates (anchorSets : List (List V)) (tails : List V) (amp : V→Int) :=
  tails.flatMap (fun i => anchorSets.map (fun a => (a++[i],amp i)))

private theorem constant_sum (xs : List A) (k : Int) : sumOn xs (fun _ => k) = xs.length*k := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    change k+sumOn xs (fun _ => k) = (↑(xs.length+1):Int)*k
    rw [ih,Int.natCast_add,Int.add_mul]; simp [Int.add_comm]

/-- After all anchors have been tested, the impact is linear in the tested
tail signs. The multiplier is the number of supplied anchor subsets. -/
theorem anchor_tail_survival [DecidableEq V] (base : List (List V×Int))
    (anchorSets : List (List V)) (tails pre : List V) (amp : V→Int)
    (anchorsTested : ∀a∈anchorSets,a⊆pre)
    (unique : ∀i∈tails,∀a∈anchorSets,(a++[i]).Nodup) :
    survival (addCubes base (tailUpdates anchorSets tails amp)) pre = survival base pre +
      (anchorSets.length:Int)*sumOn tails (fun i => if i∈pre then amp i else 0) := by
  have un : ∀s∈tailUpdates anchorSets tails amp,s.1.Nodup := by
    intro s hs
    obtain ⟨i,hi,hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact unique i hi a ha
  rw [perturbed_survival _ _ _ un]
  congr 1
  clear un unique
  induction tails with
  | nil => simp [tailUpdates,sumOn]
  | cons i ts ih =>
    change sumOn ((anchorSets.map (fun a => (a++[i],amp i))) ++ tailUpdates anchorSets ts amp) _ =
      (anchorSets.length:Int)*((if i∈pre then amp i else 0)+sumOn ts _)
    rw [ArithmeticWitness.sum_append,ih,Int.mul_add]
    congr 1
    have c : sumOn (anchorSets.map (fun a => (a++[i],amp i)))
        (fun s => if s.1⊆pre then s.2 else 0) =
        sumOn anchorSets (fun _ => if i∈pre then amp i else 0) := by
      simp only [sumOn,List.map_map,Function.comp_def]
      apply sum_congr anchorSets
      intro a ha
      simp [List.append_subset,anchorsTested a ha]
    rw [c,constant_sum]

/-- Positive-before-negative inversions in one bin. -/
def inversions : List Bool→Nat
  | [] => 0
  | false::bs => inversions bs
  | true::bs => bs.count false + inversions bs

private theorem inversion_swap (front back : List Bool) :
    inversions (front++true::false::back) = inversions (front++false::true::back)+1 := by
  induction front with
  | nil => simp [inversions,List.count_cons]; omega
  | cons t ts ih =>
    cases t <;> simp [inversions,List.count_append,List.count_cons,ih] <;> omega

private theorem positive_pair (bs : List Bool) (positive : 0<inversions bs) :
    ∃front back, bs=front++true::false::back := by
  induction bs with
  | nil => contradiction
  | cons t ts ih =>
    by_cases yes : 0<inversions ts
    · obtain ⟨p,s,eq⟩ := ih yes
      exact ⟨t::p,s,by rw [eq];rfl⟩
    · cases t with
      | false => exact False.elim (yes positive)
      | true =>
        have has : false∈ts := List.count_pos_iff.mp (by
          change 0<ts.count false+inversions ts at positive; omega)
        cases ts with
        | nil => simp at has
        | cons y ys =>
          cases y with
          | false => exact ⟨[],ys,rfl⟩
          | true =>
            have hmem : false∈ys := by simpa using has
            have ypos := List.count_pos_iff.mpr hmem
            change ¬ 0<ys.count false+inversions ys at yes
            omega

/-- Order of the signs in one projected bin while all other positions are discarded. -/
@[nospecialize] def view [DecidableEq B] (group : A→B) (sign : A→Bool) (b : B) (xs : List A) :=
  xs.filterMap (fun a => if group a=b then some (sign a) else none)

private theorem view_head [DecidableEq B] (group : A→B) (sign : A→Bool) (b : B)
    (xs : List A) (t : Bool) (ts : List Bool) (showing : view group sign b xs=t::ts) :
    ∃before a rest, xs=before++a::rest ∧ view group sign b before=[] ∧
      group a=b ∧ sign a=t ∧ view group sign b rest=ts := by
  induction xs with
  | nil => simp [view] at showing
  | cons x xs ih =>
    by_cases hx : group x=b
    · simp [view,hx] at showing
      exact ⟨[],x,xs,rfl,rfl,hx,showing.1,showing.2⟩
    · simp only [view,List.filterMap_cons,hx,if_false] at showing
      obtain ⟨p,a,rest,eq,absent,grp,sg,suffix⟩ := ih showing
      exact ⟨x::p,a,rest,by rw [eq];rfl,by simpa [view,hx] using absent,grp,sg,suffix⟩

private theorem lift_adjacent [DecidableEq B] (group : A→B) (sign : A→Bool) (b : B)
    (xs : List A) (front back : List Bool)
    (showing : view group sign b xs=front++true::false::back) :
    ∃ p x middle y s, xs=p++x::(middle++y::s) ∧
      group x=b ∧ group y=b ∧ sign x=true ∧ sign y=false ∧ view group sign b middle=[] := by
  induction front generalizing xs with
  | nil =>
    obtain ⟨p,x,r,ex,_,gx,sx,next⟩ := view_head group sign b xs true (false::back) showing
    obtain ⟨mid,y,s,ey,empty,gy,sy,_⟩ := view_head group sign b r false back next
    exact ⟨p,x,mid,y,s,by rw [ex,ey],gx,gy,sx,sy,empty⟩
  | cons t ts ih =>
    obtain ⟨pre,z,r,eq,_,_,_,next⟩ := view_head group sign b xs t (ts++true::false::back) showing
    obtain ⟨p,x,mid,y,s,er,gx,gy,sx,sy,empty⟩ := ih r next
    exact ⟨pre++z::p,x,mid,y,s,by rw [eq,er];simp,gx,gy,sx,sy,empty⟩

def allInversions [DecidableEq B] (bins : List B) (group : A→B) (sign : A→Bool) (xs : List A) :=
  Screening.CellLift.sumNat bins (fun b => inversions (view group sign b xs))

private theorem positive_bin [DecidableEq B] (bins : List B) (group : A→B) (sign : A→Bool)
    (xs : List A) (pos : 0<allInversions bins group sign xs) :
    ∃b∈bins,0<inversions (view group sign b xs) := by
  induction bins with
  | nil => contradiction
  | cons b bs ih =>
    by_cases localPos : 0<inversions (view group sign b xs)
    · exact ⟨b,by simp,localPos⟩
    · change 0<inversions (view group sign b xs) + allInversions bs group sign xs at pos
      obtain ⟨c,hc,z⟩ := ih (by omega)
      exact ⟨c,by simp [hc],z⟩

private theorem one_weight_change [DecidableEq B] (bins : List B) (b : B) (f g : B→Nat)
    (unique : bins.Nodup) (inside : b∈bins) (atBin : f b=g b+1)
    (other : ∀c,c≠b→f c=g c) :
    Screening.CellLift.sumNat bins f=Screening.CellLift.sumNat bins g+1 := by
  induction bins with
  | nil => simp at inside
  | cons c cs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp unique
    change f c + Screening.CellLift.sumNat cs f = (g c+Screening.CellLift.sumNat cs g)+1
    by_cases eq : c=b
    · subst c
      have same : cs.map f=cs.map g := List.map_congr_left (fun x hx => other x
        (fun he => fresh (he ▸ hx)))
      unfold Screening.CellLift.sumNat
      rw [atBin,same];omega
    · have h := ih tail ((List.mem_cons.mp inside).resolve_left (Ne.symm eq))
      rw [other c eq]; omega

/-- Exchanging neighboring members of a projected bin, even when arbitrary
other bins lie between them, removes one inversion in the global sum. -/
theorem interleaved_drop [DecidableEq B] (bins : List B) (group : A→B) (sign : A→Bool)
    (b : B) (p mid s : List A) (x y : A) (unique : bins.Nodup) (inside : b∈bins)
    (gx : group x=b) (gy : group y=b) (sx : sign x=true) (sy : sign y=false)
    (empty : view group sign b mid=[]) :
    allInversions bins group sign (p++x::(mid++y::s)) =
      allInversions bins group sign (p++y::(mid++x::s))+1 := by
  apply one_weight_change bins b _ _ unique inside
  · have emp := empty
    unfold view at emp
    simpa [view,List.filterMap_append,gx,gy,sx,sy,emp] using
      inversion_swap (view group sign b p) (view group sign b s)
  · intro c diff
    have nx : group x≠c := by rw [gx]; exact Ne.symm diff
    have ny : group y≠c := by rw [gy]; exact Ne.symm diff
    simp [view,List.filterMap_append,nx,ny]

private theorem transposition_perm (p middle s : List A) (x y : A) :
    (p++y::(middle++x::s)).Perm (p++x::(middle++y::s)) := by
  apply List.Perm.append_left
  exact ((List.perm_middle.cons y).trans (List.Perm.swap x y _)).trans
    (List.perm_middle.symm.cons x)

/-- A lower bound of g on each projected adjacent exchange gives regret at
least g times the number of within-bin sign inversions. The cost need only
obey the exchange inequality on permutations of the initial full order. -/
theorem inversion_regret [DecidableEq B] (bins : List B) (group : A→B) (sign : A→Bool)
    (order : List A) (cost : List A→Int) (opt g : Int) (unique : bins.Nodup)
    (lower : ∀xs,xs.Perm order→opt≤cost xs)
    (save : ∀ b∈bins, ∀p x mid y s, (p++x::(mid++y::s)).Perm order →
      group x=b → group y=b → sign x=true → sign y=false → view group sign b mid=[] →
      cost (p++y::(mid++x::s)) + g ≤ cost (p++x::(mid++y::s))) :
    g*(allInversions bins group sign order:Int) ≤ cost order-opt := by
  have bound (n : Nat) : ∀xs : List A, xs.Perm order → allInversions bins group sign xs=n →
      g*(n:Int) ≤ cost xs-opt := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro xs perm count
      by_cases zero : n=0
      · rw [zero,Int.natCast_zero,Int.mul_zero]; have := lower xs perm; omega
      · have pos : 0<allInversions bins group sign xs := by omega
        obtain ⟨b,hb,posb⟩ := positive_bin bins group sign xs pos
        obtain ⟨front,back,showing⟩ := positive_pair _ posb
        obtain ⟨p,x,mid,y,s,rfl,gx,gy,sx,sy,empty⟩ := lift_adjacent group sign b xs front back showing
        let next := p++y::(mid++x::s)
        have newPerm : next.Perm order := (transposition_perm p mid s x y).trans perm
        have one := interleaved_drop bins group sign b p mid s x y unique hb gx gy sx sy empty
        change allInversions bins group sign (p++x::(mid++y::s)) = allInversions bins group sign next+1 at one
        have hprev := ih (allInversions bins group sign next) (by omega) next newPerm rfl
        have delta := save b hb p x mid y s perm gx gy sx sy empty
        have nEq : n=allInversions bins group sign next+1 := by omega
        rw [nEq,Int.natCast_add,Int.mul_add,Int.natCast_one,Int.mul_one]
        change cost next + g ≤ cost (p++x::(mid++y::s)) at delta
        omega
  exact bound _ order (List.Perm.refl _) rfl

/-! Exact average over independent fair tags, one bit for each tested position. -/

open Screening.CellLift

def fairTags : List B → List (List (B×Bool))
  | [] => [[]]
  | b::bs => (fairTags bs).map ((b,false)::·) ++ (fairTags bs).map ((b,true)::·)

theorem fairTags_length (bs : List B) : (fairTags bs).length = 2^bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [fairTags,ih,Nat.pow_succ];omega

def pairs : Nat→Nat
  | 0 => 0
  | n+1 => pairs n+n

theorem twice_pairs (n : Nat) : 2*pairs n=n*(n-1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ k =>
      simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Nat.succ_mul,Nat.mul_succ] at ih ⊢
      rw [pairs,Nat.mul_add]
      simp only [Nat.zero_mul] at *
      omega

private theorem nat_sum_append (xs ys : List A) (f : A→Nat) :
    sumNat (xs++ys) f=sumNat xs f+sumNat ys f := by
  induction xs with
  | nil => simp [sumNat]
  | cons x xs ih =>
    change f x+sumNat (xs++ys) f = (f x+sumNat xs f)+sumNat ys f
    omega

private theorem nat_sum_add (xs : List A) (f g : A→Nat) :
    sumNat xs (fun x => f x+g x)=sumNat xs f+sumNat xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x+g x+sumNat xs (fun z => f z+g z) = (f x+sumNat xs f)+(g x+sumNat xs g)
    omega

private theorem nat_sum_one (xs : List A) : sumNat xs (fun _=>1)=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change 1+sumNat xs (fun _=>1)=xs.length+1; omega

private theorem fair_branch (b : B) (bs : List B) (f : List (B×Bool)→Nat) :
    sumNat (fairTags (b::bs)) f =
      sumNat (fairTags bs) (fun z => f ((b,false)::z)) +
      sumNat (fairTags bs) (fun z => f ((b,true)::z)) := by
  rw [fairTags,nat_sum_append]
  simp [sumNat,List.map_map,Function.comp_def]

private def nBin [DecidableEq B] (b : B) (bs : List B) := bs.countP (fun c => decide (c=b))
private def negs [DecidableEq B] (b : B) (z : List (B×Bool)) :=
  (view Prod.fst Prod.snd b z).count false
private def inv [DecidableEq B] (b : B) (z : List (B×Bool)) :=
  inversions (view Prod.fst Prod.snd b z)

private theorem fair_means [DecidableEq B] (b : B) (bs : List B) :
    2*sumNat (fairTags bs) (negs b) = 2^bs.length*nBin b bs ∧
    4*sumNat (fairTags bs) (inv b) = 2^bs.length*pairs (nBin b bs) := by
  induction bs with
  | nil => simp [fairTags,sumNat,negs,inv,view,inversions,nBin,pairs]
  | cons x xs ih =>
    obtain ⟨ihNeg,ihInv⟩ := ih
    have etaN : sumNat (fairTags xs) (fun z => negs b z) = sumNat (fairTags xs) (negs b) := rfl
    have etaI : sumNat (fairTags xs) (fun z => inv b z) = sumNat (fairTags xs) (inv b) := rfl
    simp only [fair_branch,List.length_cons,Nat.pow_succ]
    by_cases eq : x=b
    · subst x
      have neg0 (z) : negs b ((b,false)::z)=negs b z+1 := by simp [negs,view,List.count_cons]
      have neg1 (z) : negs b ((b,true)::z)=negs b z := by simp [negs,view,List.count_cons]
      have inv0 (z) : inv b ((b,false)::z)=inv b z := by simp [inv,view,inversions]
      have inv1 (z) : inv b ((b,true)::z)=negs b z + inv b z := by simp [inv,negs,view,inversions]
      have bins : nBin b (b::xs)=nBin b xs+1 := by simp [nBin,List.countP_cons]
      simp only [neg0,neg1,inv0,inv1,bins,pairs,nat_sum_add,nat_sum_one,fairTags_length]
      have eqn (u a d : Nat) : u*2*(a+d) = 2*(u*a)+2*(u*d) := by
        rw [Nat.mul_add]; ac_rfl
      rw [eqn,eqn]
      simp only [Nat.mul_one]
      omega
    · have simpN (flag) (z) : negs b ((x,flag)::z)=negs b z := by simp [negs,view,eq]
      have simpI (flag) (z) : inv b ((x,flag)::z)=inv b z := by simp [inv,view,eq]
      have bins : nBin b (x::xs)=nBin b xs := by simp [nBin,List.countP_cons,eq]
      simp only [simpN,simpI,bins]
      have eqn (u a : Nat) : u*2*a=2*(u*a) := by ac_rfl
      rw [eqn,eqn]
      omega

/-- For a frozen order with this list of bin labels, the uniform mean
inversion count is exactly one quarter of its number of within-bin pairs.
The formula is cross-multiplied by the size 2^m of the finite sample space. -/
theorem fair_inversion_mean [DecidableEq B] (bins schedule : List B) :
    4 * sumNat (fairTags schedule) (allInversions bins Prod.fst Prod.snd) =
      2^schedule.length * sumNat bins (fun b => pairs (schedule.countP (fun x => decide (x=b)))) := by
  induction bins with
  | nil =>
    change 4*sumNat (fairTags schedule) (fun _=>0)=2^schedule.length*0
    simp only [Nat.mul_zero]
    induction fairTags schedule with
    | nil => rfl
    | cons z zs ih =>
      change 4*(0+sumNat zs (fun _=>0))=0
      simpa only [Nat.zero_add] using ih
  | cons b bins ih =>
    change 4*sumNat (fairTags schedule) (fun z => inv b z + allInversions bins Prod.fst Prod.snd z) =
      2^schedule.length*(pairs (nBin b schedule)+sumNat bins _)
    rw [nat_sum_add,Nat.mul_add,Nat.mul_add,(fair_means b schedule).2,ih]

end Screening.HardBinRegret

/- Source module: Screening.GlobalOneHit -/

/-! Common whole-menu public priorities and the projection to a fixed pivot.
Labels are natural numbers. A partition is supplied as consecutive blocks in
reference order; the actual record is a single globally labeled first hit. -/
namespace Screening.GlobalOneHit

open Screening.OneHitInversion

def readBits : (labels : List Nat) → (Nat → Bool) → Mask labels.length
  | [],_ => ()
  | i::is,g => (g i,readBits is g)

def writeBit (g : Nat → Bool) (i : Nat) (b : Bool) : Nat → Bool :=
  fun j => if j=i then b else g j

private theorem read_unaffected (xs : List Nat) (g : Nat → Bool) (i : Nat) (b : Bool)
    (h : i ∉ xs) : readBits xs (writeBit g i b) = readBits xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hn : x≠i := by intro e; apply h; simp [e]
    have ht : i∉xs := fun hm => h (by simp [hm])
    simp [readBits,writeBit,hn,ih ht]

/-- Full public sign sum. Each location independently contributes both
public coins and an unassigned location defaults to false. -/
def fair : List Nat → ((Nat → Bool) → Int) → Int
  | [],f => f (fun _ => false)
  | i::is,f => fair is (fun g => f (writeBit g i false)) +
                fair is (fun g => f (writeBit g i true))

private theorem fair_constant (xs : List Nat) (c : Int) :
    fair xs (fun _ => c) = 2^xs.length*c := by
  induction xs with
  | nil => simp [fair]
  | cons x xs ih =>
    have h2 : 2*c=c+c := by omega
    simp only [fair,ih,List.length_cons,Int.pow_succ,Int.mul_assoc,h2,Int.mul_add]

private theorem active_coins (active post : List Nat) (hd : active.Nodup)
    (f : Mask active.length → Int) :
    fair (active++post) (fun g => f (readBits active g)) =
      (2:Int)^post.length*cubeSum active.length f := by
  induction active with
  | nil => simp only [List.nil_append,List.length_nil,readBits,cubeSum,fair_constant]
  | cons i is ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hd
    simp only [List.cons_append,fair,readBits,read_unaffected is _ i _ hn]
    have self (g : Nat→Bool) (b : Bool) : writeBit g i b i = b := by simp [writeBit]
    simp only [self,List.length_cons,cubeSum,Int.mul_add]
    rw [ih ht (fun t => f (false,t)),ih ht (fun t => f (true,t))]

/-- Exact marginal under a uniform global mark mask for any contiguous
window. Every configuration on the window occurs equally often. -/
theorem fair_window (pre active post : List Nat) (hd : (pre++active++post).Nodup)
    (f : Mask active.length → Int) :
    fair (pre++active++post) (fun g => f (readBits active g)) =
      (2:Int)^(pre.length+post.length)*cubeSum active.length f := by
  induction pre with
  | nil =>
    have ha : active.Nodup := (List.pairwise_append.mp (by simpa using hd)).1
    simpa using active_coins active post ha f
  | cons x xs ih =>
    have hh : (x::(xs++active++post)).Nodup := hd
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hh
    have ha : x ∉ active := fun h => hn (by simp [List.mem_append,h])
    change (fair (xs++active++post) (fun g => f (readBits active (writeBit g x false)))) +
      (fair (xs++active++post) (fun g => f (readBits active (writeBit g x true)))) = _
    simp only [read_unaffected active _ x _ ha, ih ht]
    have exp : (x::xs).length+post.length=(xs.length+post.length)+1 := by simp; omega
    rw [exp,Int.pow_succ,Int.mul_assoc]
    have hh : 2*cubeSum active.length f=cubeSum active.length f+cubeSum active.length f := by omega
    rw [hh,Int.mul_add]

def priority (block : List Nat) (mark : Nat → Bool) :=
  block.filter mark ++ block.filter (fun i => !mark i)

def allPriorities (blocks : List (List Nat)) (mark : Nat → Bool) :=
  blocks.flatMap (fun block => priority block mark)

def firstHit (blocks : List (List Nat)) (mark hit : Nat → Bool) : Option Nat :=
  (allPriorities blocks mark).find? hit

/-- The physical location of a fixed j inside one of the two partitions. -/
structure Split where
  before : List (List Nat)
  left : List Nat
  j : Nat
  right : List Nat
  after : List (List Nat)

def Split.blocks (x : Split) := x.before ++ [x.left++[x.j]++x.right] ++ x.after
def Split.pre (x : Split) := x.before.flatten ++ x.left
def Split.post (x : Split) := x.after.flatten
def Split.menu (x : Split) := x.pre ++ (x.j::x.right) ++ x.post

private def tests (labels : List Nat) (mark hit : Nat→Bool) :=
  labels.map fun i => (hit i,mark i)

private def tag (j : Nat) (mark hit : Nat→Bool) (i : Nat) : Test :=
  ⟨i==j,mark i,hit i⟩

private theorem filter_map {α β : Type} (xs : List α) (f : α→β) (p : β→Bool) :
    (xs.map f).filter p = (xs.filter (fun x => p (f x))).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p (f x) <;> simp [List.filter_cons,h,ih]

private theorem mark_map (block : List Nat) (j : Nat) (mark hit : Nat→Bool) :
    (priority block mark).map (tag j mark hit) = markedFirst (block.map (tag j mark hit)) := by
  simp [priority,markedFirst,filter_map,tag]

private theorem scan_tag (xs : List Nat) (j : Nat) (mark hit : Nat→Bool) :
    scan (xs.map (tag j mark hit)) = (xs.find? hit).map (fun i => i==j) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : hit x <;> simp [tag,scan,h,List.find?_cons,ih]

private theorem others (xs : List Nat) (j : Nat) (mark hit : Nat→Bool) (hn : j∉xs) :
    (tests xs mark hit).map ordinary = xs.map (tag j mark hit) := by
  simp only [tests,List.map_map]
  apply List.map_congr_left
  intro x hx
  have hne : x≠j := fun e => hn (e ▸ hx)
  simp [tag,ordinary,Function.comp_def,hne]

private theorem slots_read (xs : List Nat) (mark hit : Nat→Bool) :
    slots xs.length (readBits xs hit) (readBits xs mark) = tests xs mark hit := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [readBits,slots,tests] at ih ⊢; exact ih

private theorem priority_mem (blocks : List (List Nat)) (mark : Nat→Bool) (i : Nat) :
    i ∈ allPriorities blocks mark ↔ i∈blocks.flatten := by
  simp only [allPriorities,priority,List.mem_flatMap,List.mem_flatten,List.mem_append,List.mem_filter]
  constructor
  · rintro ⟨b,hb,h|h⟩ <;> exact ⟨b,hb,h.1⟩
  · rintro ⟨b,hb,hi⟩
    exact ⟨b,hb, by cases he : mark i <;> simp [he,hi]⟩

private theorem clear_tests (xs : List Nat) (mark hit : Nat→Bool) :
    clear (tests xs mark hit) = !xs.any hit := by
  simp [clear,tests,List.any_map,Function.comp_def]

private theorem prior_any (blocks : List (List Nat)) (mark hit : Nat→Bool) :
    (allPriorities blocks mark).any hit = blocks.flatten.any hit := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,priority_mem]

private theorem safety {x : Split} (hd : x.menu.Nodup) :
    x.j∉x.before.flatten ∧ x.j∉x.left ∧ x.j∉x.right ∧ x.j∉x.after.flatten := by
  have h : (x.pre ++ ((x.j::x.right)++x.post)).Nodup := by simpa [Split.menu,List.append_assoc] using hd
  obtain ⟨_,hrest,hdis⟩ := List.pairwise_append.mp h
  have member : x.j ∈ (x.j::x.right)++x.post := by simp
  have hpre : x.j ∉ x.pre := fun h => hdis x.j h x.j member rfl
  have hn : x.j ∉ x.right++x.post := (List.nodup_cons.mp hrest).1
  simp only [Split.pre,List.mem_append,not_or] at hpre
  simp only [Split.post,List.mem_append,not_or] at hn
  exact ⟨hpre.1,hpre.2,hn⟩

/-- Relabeling the globally returned result "is it j?" gives exactly the
local operational stopped scan. The value of no other observation is used. -/
theorem exact_global_log (x : Split) (hd : x.menu.Nodup) (mark hit : Nat→Bool) :
    (firstHit x.blocks mark hit).map (fun i => i==x.j) =
      stopped (tests (allPriorities x.before mark) mark hit)
        (tests x.left mark hit) (tests x.right mark hit)
        (tests (allPriorities x.after mark) mark hit) (hit x.j) (mark x.j) := by
  obtain ⟨hpre,hl,hr,hpost⟩ := safety hd
  have hb : x.j∉allPriorities x.before mark := fun h => hpre ((priority_mem _ _ _).mp h)
  have ha : x.j∉allPriorities x.after mark := fun h => hpost ((priority_mem _ _ _).mp h)
  rw [firstHit,←scan_tag _ x.j mark hit]
  simp only [Split.blocks,allPriorities,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.map_append,mark_map,List.map_cons,List.map_nil]
  unfold stopped
  simp only [allPriorities] at hb ha
  rw [others _ x.j mark hit hb,others _ x.j mark hit hl,others _ x.j mark hit hr,others _ x.j mark hit ha]
  simp [allPriorities,tag,List.append_assoc]

/-- The fixed local row uses the underlying hit bits only. Its natural-minimum
event is independent of all public marks in earlier blocks and before j. -/
def localWord (x : Split) (hit : Nat→Bool) : Word x.right.length :=
  ⟨tests x.before.flatten (fun _ => false) hit,tests x.left (fun _ => false) hit,
   hit x.j,readBits x.right hit,[]⟩

theorem global_negative (x : Split) (hd : x.menu.Nodup) (mark hit : Nat → Bool)
    (negative : mark x.j=false) :
    firstHit x.blocks mark hit = some x.j ↔
      (eligible (localWord x hit) && noPositiveHit (tests x.right mark hit)) = true := by
  have he := exact_global_log x hd mark hit
  rw [negative] at he
  have h := negative_first (tests (allPriorities x.before mark) mark hit)
    (tests x.left mark hit) (tests x.right mark hit)
    (tests (allPriorities x.after mark) mark hit) (hit x.j)
  rw [←he] at h
  simp only [localWord,eligible,clear_tests,prior_any] at h ⊢
  rw [←h]
  cases v : firstHit x.blocks mark hit with
  | none => simp
  | some j => simp [beq_iff_eq]

/-- One table per pivot, evaluated only from the globally returned index,
chosen partition and publicly visible marks. -/
def feature (x : Split) (selected : Bool) (c : Mask x.right.length → Int)
    (coin : Bool) (marks : Nat→Bool) (Y : Option Nat) : Int :=
  linearLog x.right.length c (readBits x.right marks) (coin==selected) (marks x.j)
    (Y.map (fun i => i==x.j))

private theorem flagged (y : Option Nat) (j : Nat) :
    y.map (fun i => i==j) = some true ↔ y=some j := by
  cases y <;> simp [beq_iff_eq]

private theorem proj_negative (x : Split) (hd : x.menu.Nodup) (m h : Nat→Bool)
    (hn : m x.j=false) :
    ((firstHit x.blocks m h).map (fun i => i==x.j) = some true) ↔
      stopped (localWord x h).before (localWord x h).left
        (slots x.right.length (localWord x h).tailHits (readBits x.right m))
        (localWord x h).after (localWord x h).pivotHit false = some true := by
  rw [flagged,global_negative x hd m h hn,negative_first]
  simp only [localWord,eligible,slots_read]

theorem global_feature_eq (x : Split) (hd : x.menu.Nodup) (selected : Bool)
    (plans : Bool→List (List Nat)) (hx : plans selected=x.blocks)
    (h m : Nat→Bool) (c : Mask x.right.length→Int) (coin : Bool) :
    feature x selected c coin m (firstHit (plans coin) m h) =
      linearLog x.right.length c (readBits x.right m) (coin==selected) (m x.j)
        (observed (localWord x h) (fun _ _ => none) (coin==selected) (m x.j) (readBits x.right m)) := by
  unfold feature
  rw [observed_linear,observed_linear]
  by_cases eq : coin=selected
  · subst coin
    cases hn : m x.j with
    | true => simp
    | false =>
      have hg := proj_negative x hd m h hn
      by_cases hglo : (firstHit x.blocks m h).map (fun i => i==x.j) = some true
      · simp [hx,observed,hglo,hg.mp hglo]
      · have hl := fun hl => hglo (hg.mpr hl)
        simp [hx,observed,hglo]; rw [if_neg hl]
  · have beq : (coin==selected)=false := by cases coin <;> cases selected <;> simp_all
    simp [beq]

def globalIntegral (menu : List Nat) (F : Bool → (Nat→Bool) → Int) :=
  fair menu (F false) + fair menu (F true)

private theorem partition_coins (d : Nat) (selected : Bool) (f : Bool→Bool→Mask d→Int) :
    cubeSum (d+1) (fun t => f (false==selected) t.1 t.2) +
    cubeSum (d+1) (fun t => f (true==selected) t.1 t.2) = integrateMarks d f := by
  cases selected <;> simp [cubeSum,integrateMarks,cube_add] <;> ac_rfl

/-- Exact marginalization for *any* integer statistic g of the first-hit
field on a full global record. All assignments on labels outside the
window are summed, not assumed independent after observing the hit. -/
theorem global_projection (x : Split) (hd : x.menu.Nodup) (selected : Bool)
    (plans : Bool → List (List Nat)) (hx : plans selected=x.blocks)
    (hit : Nat→Bool) (c : Mask x.right.length→Int) (g : Int→Int) :
    globalIntegral x.menu (fun coin mark =>
      g (feature x selected c coin mark (firstHit (plans coin) mark hit))) =
    (2:Int)^(x.pre.length+x.post.length)*integrateMarks x.right.length
      (fun a b s => g (linearLog x.right.length c s a b
        (observed (localWord x hit) (fun _ _ => none) a b s))) := by
  let d := x.right.length
  let f := fun a b (s : Mask d) => g (linearLog d c s a b
    (observed (localWord x hit) (fun _ _ => none) a b s))
  have branch (coin : Bool) :
      fair x.menu (fun mark => g (feature x selected c coin mark (firstHit (plans coin) mark hit))) =
      2^(x.pre.length+x.post.length)*cubeSum (d+1) (fun z => f (coin==selected) z.1 z.2) := by
    simp only [global_feature_eq x hd selected plans hx]
    exact fair_window x.pre (x.j::x.right) x.post hd (fun z => f (coin==selected) z.1 z.2)
  rw [globalIntegral,branch,branch,←Int.mul_add,partition_coins]

structure Record where
  partition : Bool
  marks : Nat → Bool
  first : Option Nat

/-- Enumerate both public settings of *every* coordinate of the full menu. -/
def enumerate {α : Type} : List Nat → ((Nat→Bool)→α) → List α
  | [],f => [f (fun _ => false)]
  | i::is,f => enumerate is (fun g => f (writeBit g i false)) ++
      enumerate is (fun g => f (writeBit g i true))

private theorem enumerate_sum {α : Type} (xs : List Nat) (f : (Nat→Bool)→α) (g : α→Int) :
    sumOn (enumerate xs f) g = fair xs (fun m => g (f m)) := by
  induction xs generalizing f with
  | nil => simp [enumerate,fair,sumOn]
  | cons i is ih => rw [enumerate,sum_append,ih,ih,fair]

/-- The full experiment uses one shared sign mask and one partition coin
per word; the data available afterwards contain just one globally labeled hit. -/
def records (menu : List Nat) (plans : Bool→List (List Nat)) (law : List (Nat→Bool)) : List Record :=
  law.flatMap fun hit =>
    let record := fun b m => Record.mk b m (firstHit (plans b) m hit)
    enumerate menu (record false) ++ enumerate menu (record true)

theorem records_sum (menu : List Nat) (plans : Bool→List (List Nat)) (law : List (Nat→Bool))
    (g : Record→Int) :
    sumOn (records menu plans law) g = sumOn law (fun hit => globalIntegral menu
      (fun b m => g ⟨b,m,firstHit (plans b) m hit⟩)) := by
  rw [records,sum_flatMap]
  congr 1; funext hit
  rw [sum_append,enumerate_sum,enumerate_sum,globalIntegral]

private theorem sum_scalar {α : Type} (xs : List α) (k : Int) (f : α→Int) :
    sumOn xs (fun x => k*f x) = k*sumOn xs f := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    change k*f x+sumOn xs _ = k*(f x+sumOn xs _)
    rw [ih,Int.mul_add]

/-- Every pivot's local marginal on the *same* explicitly enumerated full
records agrees with its stopped local construction, including all multiplicities. -/
theorem record_projection (x : Split) (hd : x.menu.Nodup) (selected : Bool)
    (plans : Bool → List (List Nat)) (hx : plans selected=x.blocks)
    (law : List (Nat→Bool)) (c : Mask x.right.length→Int) (g : Int→Int) :
    sumOn (records x.menu plans law) (fun rec =>
      g (feature x selected c rec.partition rec.marks rec.first)) =
    (2:Int)^(x.pre.length+x.post.length)*sumOn law (fun hit => integrateMarks x.right.length
      (fun a b s => g (linearLog x.right.length c s a b
        (observed (localWord x hit) (fun _ _ => none) a b s)))) := by
  rw [records_sum]
  simp only [global_projection x hd selected plans hx,sum_scalar]

/-- Number of joint public partition/mark outcomes. -/
def choices (m : Nat) := 2*2^m

private theorem choices_window (x : Split) :
    choices x.menu.length = 2^(x.pre.length+x.post.length)*(4*2^x.right.length) := by
  unfold choices Split.menu
  simp only [List.length_append,List.length_cons,Nat.pow_add,Nat.pow_one]
  change 2*(2^x.pre.length*(2^x.right.length*2)*2^x.post.length) =
    2^x.pre.length*2^x.post.length*((2*2)*2^x.right.length)
  ac_rfl

private theorem align (d K : Nat) (h : d≤K) : 2^(K-d)*2^d=2^K := by
  rw [← Nat.pow_add]; congr 1; omega

private theorem norm_mean (x : Split) (K : Nat) (hd : x.right.length≤K) :
    (2^(K-x.right.length)*2^(x.pre.length+x.post.length))*(4*4^x.right.length) =
    choices x.menu.length*2^K := by
  let d := x.right.length
  rw [choices_window,←align d K hd,show 4^d=2^d*2^d from Nat.mul_pow 2 2 d]
  ac_rfl

private theorem norm_energy (x : Split) (K : Nat) (hd : x.right.length≤K) (count rest : Nat) :
    (2^(K-x.right.length)*2^(K-x.right.length))*
      (2^(x.pre.length+x.post.length)*(16*count*(2^x.right.length*(4^x.right.length*rest)))) =
    choices x.menu.length*4*(4^K)*count*rest := by
  let d := x.right.length
  rw [choices_window,show 4^K=2^K*2^K from Nat.mul_pow 2 2 K,←align d K hd,
    show 4^d=2^d*2^d from Nat.mul_pow 2 2 d]
  change _*(_*((4*4)*count*(_*(_*rest)))) = _
  ac_rfl

private theorem mapped_sum {α β : Type} (xs : List α) (u : α→β) (v : β→Int) :
    sumOn (xs.map u) v = sumOn xs (fun x => v (u x)) := by
  simp [sumOn,List.map_map,Function.comp_def]

private theorem sum_constant {α : Type} (xs : List α) (c : Int) :
    sumOn xs (fun _ => c) = (xs.length:Int)*c := sum_const xs c

theorem record_size (menu : List Nat) (plans : Bool→List (List Nat)) (law : List (Nat→Bool)) :
    (records menu plans law).length = law.length*choices menu.length := by
  have h := records_sum menu plans law (fun _=>1)
  simp only [sum_constant,Int.mul_one,globalIntegral,fair_constant] at h
  have e : ((records menu plans law).length:Int) = ((law.length*choices menu.length:Nat):Int) := by
    rw [h]
    unfold choices
    simp only [Int.natCast_mul,Int.natCast_pow,Int.cast_ofNat_Int,Int.mul_one]
    congr 1; omega
  omega

private theorem energy_sum (vs : List Int) : (SampleVariance.energy vs : Int)=sumOn vs (fun z=>z*z) := by
  induction vs with
  | nil => rfl
  | cons z zs ih =>
    change ((z.natAbs*z.natAbs+SampleVariance.energy zs:Nat):Int)=z*z+sumOn zs _
    rw [Int.natCast_add,Int.natAbs_mul_self,ih]

private theorem scale_energy {α : Type} (rows : List α) (f : α→Int) (k : Nat) :
    SampleVariance.energy (rows.map (fun r => (k:Int)*f r)) =
    (k*k)*SampleVariance.energy (rows.map f) := by
  induction rows with
  | nil => simp [SampleVariance.energy]
  | cons r rs ih =>
    simp only [List.map_cons,SampleVariance.energy,Int.natAbs_mul,Int.natAbs_ofNat,ih,Nat.mul_add]
    ac_rfl

structure Pivot (menu : List Nat) (plans : Bool→List (List Nat)) where
  window : Split
  selected : Bool
  menu_eq : window.menu=menu
  plan_eq : plans selected=window.blocks

/-- Local values all have the same interpretation after division by 2^K,
even if a menu end shortens some blocks. -/
def value {menu plans} (p : Pivot menu plans) (K h : Nat) (f : Mask p.window.right.length→Int)
    (rec : Record) : Int :=
  ((2^(K-p.window.right.length):Nat):Int) *
  feature p.window p.selected (limited _ h (coefficient _ f)) rec.partition rec.marks rec.first

def minCount (x : Split) (law : List (Nat→Bool)) : Nat :=
  law.countP (fun hit => eligible (localWord x hit))

theorem actual_pivot_mean {menu plans} (p : Pivot menu plans) (hn : menu.Nodup) (K h : Nat)
    (hd : p.window.right.length≤K) (f : Mask p.window.right.length→Int) (law : List (Nat→Bool))
    (hcap : ∀ z ∈ law, eligible (localWord p.window z)=true → weight _ (readBits p.window.right z) ≤ h) :
    sumOn (records menu plans law) (value p K h f) =
    ((choices menu.length*2^K:Nat):Int)*sumOn law (fun hit =>
      if eligible (localWord p.window hit) then f (readBits p.window.right hit) else 0) := by
  let x := p.window
  let d := x.right.length
  let c := limited d h (coefficient d f)
  have hdw : x.menu.Nodup := p.menu_eq ▸ hn
  have local_mean : sumOn law (fun hit => integrateMarks d (fun a b s =>
      linearLog d c s a b (observed (localWord x hit) (fun _ _ => none) a b s))) =
      (4*(4:Int)^d)*sumOn law (fun hit =>
        if eligible (localWord x hit) then f (readBits x.right hit) else 0) := by
    induction law with
    | nil => simp [sumOn]
    | cons z zs ih =>
      change integrateMarks d _ + sumOn zs _ = _*((if eligible (localWord x z) then f (readBits x.right z) else 0)+sumOn zs _)
      rw [show integrateMarks d (fun a b s => linearLog d c s a b
        (observed (localWord x z) (fun _ _ => none) a b s)) = _ from
        capped_when_eligible d h f (localWord x z) (hcap z (by simp)) (fun _ _ => none)]
      rw [ih (fun z hz => hcap z (by simp [hz])),Int.mul_add]
      rfl
  have joined : ∀ z : Int,
      ((2^(K-d):Nat):Int)*((2:Int)^(x.pre.length+x.post.length)*(4*4^d*z)) =
      ((choices menu.length*2^K:Nat):Int)*z := by
    intro z
    rw [←p.menu_eq,←norm_mean x K hd]
    dsimp only [d]; simp only [Int.natCast_mul,Int.natCast_pow,Int.cast_ofNat_Int]; ac_rfl
  have hr := record_projection x hdw p.selected plans p.plan_eq law c id
  have hmenu : x.menu=menu := p.menu_eq
  simp only [id_eq,hmenu] at hr
  unfold value
  rw [sum_scalar]
  change ((2^(K-d):Nat):Int)*sumOn (records menu plans law) (fun r => feature x p.selected c r.partition r.marks r.first) = _
  rw [hr,local_mean,joined]

theorem actual_pivot_energy {menu plans} (p : Pivot menu plans) (hn : menu.Nodup) (K h : Nat)
    (hd : p.window.right.length≤K) (f : Mask p.window.right.length→Int) (hf : ∀ s, (f s).natAbs≤1)
    (law : List (Nat→Bool)) :
    SampleVariance.energy ((records menu plans law).map (value p K h f)) ≤
      choices menu.length*4*4^K*minCount p.window law*(9^h*(K+1)^h) := by
  let x := p.window
  let d := x.right.length
  let c := limited d h (coefficient d f)
  let loc :=  localWord x
  let rows := records menu plans law
  let F := fun r : Record => feature x p.selected c r.partition r.marks r.first
  have hdw : x.menu.Nodup := p.menu_eq ▸ hn
  have hr := record_projection x hdw p.selected plans p.plan_eq law c (fun v => v*v)
  have hmenu : x.menu=menu := p.menu_eq
  rw [hmenu] at hr
  have hb := bounded_population_second_moment d h f hf (law.map loc) (fun _ _ _ => none)
  rw [mapped_sum] at hb
  have ce : (law.map loc).countP eligible = minCount x law := by simp [minCount,loc,List.countP_map,Function.comp_def]
  rw [ce] at hb
  have raw : SampleVariance.energy (rows.map F) ≤
      2^(x.pre.length+x.post.length)*(16*minCount x law*(2^d*(4^d*(9^h*(d+1)^h)))) := by
    apply Int.ofNat_le.mp
    rw [energy_sum,mapped_sum,hr]
    have bound := Int.mul_le_mul_of_nonneg_left hb (Int.pow_nonneg (m:=x.pre.length+x.post.length) (n:=2) (by decide))
    simpa only [Int.natCast_mul,Int.natCast_pow,Int.cast_ofNat_Int,Int.mul_assoc] using bound
  change SampleVariance.energy (rows.map (fun r => ((2^(K-d):Nat):Int)*F r)) ≤ _
  rw [scale_energy]
  apply Nat.le_trans (Nat.mul_le_mul_left _ raw)
  rw [norm_energy x K hd,p.menu_eq]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) h))

theorem weight_read (labels : List Nat) (hit : Nat→Bool) :
    weight labels.length (readBits labels hit) = labels.countP hit := by
  induction labels with
  | nil => rfl
  | cons i is ih =>
    simp only [readBits,List.length_cons,weight,List.countP_cons,ih]

theorem eligible_minimum (x : Split) (hit : Nat → Bool) :
    eligible (localWord x hit) = (!x.pre.any hit && hit x.j) := by
  simp only [eligible,localWord,clear_tests,Split.pre,List.any_append,Bool.not_or]

theorem window_cap {menu plans} (p : Pivot menu plans) (z : Nat → Bool) (h : Nat)
    (cap : menu.countP z ≤ h+1) (emin : eligible (localWord p.window z)=true) :
    weight p.window.right.length (readBits p.window.right z) ≤ h := by
  rw [eligible_minimum] at emin
  have hj : z p.window.j = true := by cases he : z p.window.j <;> simp_all
  rw [←p.menu_eq] at cap
  simp only [Split.menu,List.countP_append,List.countP_cons,hj,if_true] at cap
  rw [weight_read]; omega

/-- Finite scalar prefix specification. Each registered index is the pivot
of its supplied concrete split in the selected partition. -/
structure Fields (menu : List Nat) (plans : Bool→List (List Nat)) where
  live : List Nat
  distinct : live.Nodup
  pivot : Nat → Pivot menu plans
  label : ∀ j ∈ live, (pivot j).window.j=j
  payoff : (j : Nat) → Mask (pivot j).window.right.length → Int
  bounded : ∀ j ∈ live, ∀ z, ((payoff j) z).natAbs ≤ 1

def coordinate {menu plans} (F : Fields menu plans) (K h j : Nat) (r : Record) : Int :=
  value (F.pivot j) K h (F.payoff j) r

def observedScore {menu plans} (F : Fields menu plans) (K h : Nat) (r : Record) : Int :=
  sumOn F.live (fun j => coordinate F K h j r)

def truth {menu plans} (F : Fields menu plans) (hit : Nat→Bool) : Int :=
  sumOn F.live fun j =>
    let x := (F.pivot j).window
    if eligible (localWord x hit) then F.payoff j (readBits x.right hit) else 0

private theorem not_reported {menu plans} (p : Pivot menu plans) (K h : Nat)
    (f : Mask p.window.right.length→Int) (r : Record) (hn : r.first≠some p.window.j) :
    value p K h f r=0 := by
  have hflag := fun hh => hn ((flagged r.first p.window.j).mp hh)
  unfold value feature
  rw [observed_linear]
  simp [hflag,hn]

private theorem coordinate_is_projected {menu plans} (F : Fields menu plans) (K h j : Nat)
    (hj : j∈F.live) (r : Record) :
    projection Record.first (coordinate F K h) j r = coordinate F K h j r := by
  unfold projection
  split
  · rfl
  · rename_i hn
    exact (not_reported _ _ _ _ _ (by rwa [F.label j hj])).symm

private theorem scores_shared {menu plans} (F : Fields menu plans) (K h : Nat) (rs : List Record) :
    sharedTickets rs F.live Record.first (coordinate F K h) = rs.map (observedScore F K h) := by
  unfold sharedTickets observedScore
  apply List.map_congr_left
  intro r _
  unfold sumOn
  congr 1
  apply List.map_congr_left
  intro j hj; exact coordinate_is_projected F K h j hj r

private theorem swap {α β : Type} (xs : List α) (ys : List β) (f : α→β→Int) :
    sumOn xs (fun x => sumOn ys (f x)) = sumOn ys (fun y => sumOn xs (fun x => f x y)) := by
  have add {γ : Type} (us : List γ) (a b : γ→Int) :
      sumOn us (fun z => a z+b z)=sumOn us a+sumOn us b := by
    induction us with
    | nil => rfl
    | cons z zs ih =>
      change a z+b z+sumOn zs _=(a z+sumOn zs a)+(b z+sumOn zs b)
      rw [ih]; ac_rfl
  induction xs with
  | nil => change 0 = sumOn ys (fun _ => 0); rw [sum_constant,Int.mul_zero]
  | cons x xs ih =>
    change sumOn ys (f x)+sumOn xs _ = sumOn ys (fun y=>f x y+sumOn xs _)
    rw [add,ih]

/-- Mean of a whole prefix score on the common full records, using only the
total hit cap on each original word. The common numerator scale is 2^K. -/
theorem actual_prefix_mean {menu plans} (F : Fields menu plans) (hn : menu.Nodup) (K h : Nat)
    (hwidth : ∀ j ∈ F.live, (F.pivot j).window.right.length ≤ K) (law : List (Nat→Bool))
    (cap : ∀ z ∈ law, menu.countP z ≤ h+1) :
    sumOn (records menu plans law) (observedScore F K h) =
      ((choices menu.length*2^K:Nat):Int)*sumOn law (truth F) := by
  unfold observedScore truth
  rw [swap,swap law,←sum_scalar]
  unfold sumOn
  congr 1
  apply List.map_congr_left
  intro j hj
  exact actual_pivot_mean (F.pivot j) hn K h (hwidth j hj) (F.payoff j) law
    (fun z hz => window_cap _ z h (cap z hz))

/-- Full-prefix block concentration from one globally logged label per word.
The sufficient sample inequality uses the frequency Q/law.length, the
number of active minima, and (K+1)^h. It has no assumption about the energy
or unbiasedness of the projections, which were derived above. -/
theorem actual_prefix_block {menu plans} (F : Fields menu plans) (hnodup : menu.Nodup)
    (K h : Nat) (hwidth : ∀ j ∈ F.live, (F.pivot j).window.right.length≤K)
    (law : List (Nat→Bool)) {N Q a D : Nat} (hn : 0<N) (ha : 0<a) (hD : 0<D)
    (hK : 0<law.length) (hq : ∀ j ∈ F.live, minCount (F.pivot j).window law ≤ Q)
    (hsize : 16*D*D*F.live.length*Q*(9^h*(K+1)^h) ≤ law.length*N*a*a) :
    let rs := records menu plans law
    let scores := rs.map (observedScore F K h)
    let blocks := SampleVariance.sampleSums (SampleVariance.centered scores) N
    3*blocks.length ≤ 4*SampleVariance.goodCount blocks (N*(scores.length*(2^K*a))) D := by
  let rs := records menu plans law
  let B := choices menu.length*4*4^K*Q*(9^h*(K+1)^h)
  have hb (j : Nat) (hj : j∈F.live) :
      SampleVariance.energy (rs.map (projection Record.first (coordinate F K h) j)) ≤ B := by
    have hmap : rs.map (projection Record.first (coordinate F K h) j)=rs.map (coordinate F K h j) :=
      List.map_congr_left (fun r _ => coordinate_is_projected F K h j hj r)
    rw [hmap]
    apply Nat.le_trans (actual_pivot_energy (F.pivot j) hnodup K h (hwidth j hj) (F.payoff j)
      (F.bounded j hj) law)
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hq j hj))
  have hr : rs.length = law.length*choices menu.length := record_size _ _ _
  have hrows : 0<rs.length := hr ▸ Nat.mul_pos hK (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
  have hbudget : 4*(D*D*(F.live.length*B)) ≤ rs.length*N*(2^K*a)*(2^K*a) := by
    rw [hr]
    calc _ = (choices menu.length*4^K)*(16*D*D*F.live.length*Q*(9^h*(K+1)^h)) := by
            dsimp only [B]; change (4*_) = (_*((4*4)*_*_*_*_*_)); ac_rfl
         _ ≤ (choices menu.length*4^K)*(law.length*N*a*a) := Nat.mul_le_mul_left _ hsize
         _ = _ := by rw [show 4^K=2^K*2^K from Nat.mul_pow 2 2 K]; ac_rfl
  have result := shared_block_guarantee rs F.live F.distinct Record.first (coordinate F K h)
    hb hrows hn (Nat.mul_pos (Nat.pow_pos (by decide)) ha) hD hbudget
  simpa only [scores_shared F K h rs] using result

/-- Enumerate independent raw records, in the order used by the convolution.
The same block is fed to every candidate prefix. -/
def rawBlocks {α : Type} (law : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => (rawBlocks law n).flatMap fun tail => law.map (fun r=>r::tail)

theorem raw_blocks_sums {α : Type} (law : List α) (f : α→Int) (n : Nat) :
    (rawBlocks law n).map (fun row=>sumOn row f) = SampleVariance.sampleSums (law.map f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rawBlocks,SampleVariance.sampleSums,SampleVariance.convolve,←ih,List.map_flatMap,
      List.flatMap_map,List.map_map,Function.comp_def]
    congr 1
    funext row
    apply List.map_congr_left; intro r _
    exact Int.add_comm _ _

theorem raw_block_length {α : Type} {law : List α} {n : Nat} {row : List α}
    (h : row∈rawBlocks law n) : row.length=n := by
  induction n generalizing row with
  | zero => simpa [rawBlocks] using h
  | succ n ih =>
    obtain ⟨tail,ht,hr⟩ := List.mem_flatMap.mp h
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    simp [ih ht]

private theorem weights_map {α : Type} (rs : List α) (f : α→Int) :
    SampleVariance.weightedSum id (rs.map f)=sumOn rs f := by
  induction rs with
  | nil => rfl
  | cons r rs ih => change f r+SampleVariance.weightedSum id (rs.map f)=f r+sumOn rs f; rw [ih]

/-- The population center occurs only in the accuracy event; the learned
quantity on a raw block is the sum of observable scores. -/
def centeredBlock {α : Type} (rs : List α) (f : α→Int) (block : List α) : Int :=
  (rs.length:Int)*sumOn block f-(block.length:Int)*sumOn rs f

private theorem centered_map {α : Type} (rs : List α) (f : α→Int) (N : Nat) :
    (rawBlocks rs N).map (centeredBlock rs f) =
      SampleVariance.sampleSums (SampleVariance.centered (rs.map f)) N := by
  let centered := fun r => (rs.length:Int)*f r-sumOn rs f
  have hsum (row : List α) : centeredBlock rs f row = sumOn row centered := by
    induction row with
    | nil => simp [centeredBlock,sumOn]
    | cons r row ih =>
      change (rs.length:Int)*(f r+sumOn row f)-(row.length+1:Int)*sumOn rs f =
        centered r+sumOn row centered
      rw [←ih]; unfold centeredBlock centered
      rw [Int.mul_add,Int.add_mul,Int.one_mul]; omega
  have ce : SampleVariance.centered (rs.map f) = rs.map centered := by
    simp [SampleVariance.centered,List.map_map,Function.comp_def,weights_map,centered]
  rw [ce,←raw_blocks_sums]
  exact List.map_congr_left (fun row _ => hsum row)

private theorem good_plus_bad (xs : List Int) (t d : Nat) :
    SampleVariance.goodCount xs t d + SampleVariance.badCount xs t d=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [SampleVariance.goodCount,SampleVariance.badCount,List.countP_cons,decide_eq_true_eq,
      List.length_cons] at ih ⊢
    split <;> split <;> omega

/-- Observable block sum versus its population mean, expressed by exact
integer cross multiplication. -/
def badBlock {menu plans} (rs : List Record) (K h N a D : Nat) (F : Fields menu plans)
    (row : List Record) : Bool :=
  decide (N*(rs.length*(2^K*a)) < D*(centeredBlock rs (observedScore F K h) row).natAbs)

/-- All candidate prefix estimates share both their raw records and their
block partition. The failure fraction is at most `|Fs| 3^s/(2·4^s)`.
In particular s may be selected from a desired failure probability before
seeing the data. -/
theorem simultaneous_raw_prefixes {menu plans} (Fs : List (Fields menu plans))
    (hnodup : menu.Nodup) (K h : Nat)
    (hwidth : ∀ F∈Fs, ∀ j ∈ F.live, (F.pivot j).window.right.length≤K)
    (law : List (Nat→Bool)) {N Q a D : Nat} (hn : 0<N) (ha : 0<a) (hD : 0<D)
    (hK : 0<law.length) (hq : ∀ F∈Fs, ∀ j ∈ F.live, minCount (F.pivot j).window law ≤ Q)
    (hsize : ∀ F∈Fs, 16*D*D*F.live.length*Q*(9^h*(K+1)^h) ≤ law.length*N*a*a)
    (s : Nat) :
    let rs := records menu plans law
    let draws := SampleVariance.iidTuples (rawBlocks rs N) (2*s+1)
    (2*4^s)*draws.countP (fun row => Fs.any fun F =>
        SampleVariance.atLeastBad (badBlock rs K h N a D F) (s+1) row) ≤
      Fs.length*(3^s*draws.length) := by
  let rs := records menu plans law
  let B := rawBlocks rs N
  let pred := badBlock (menu:=menu) (plans:=plans) rs K h N a D
  have quart (F : Fields menu plans) (hf : F∈Fs) : 4*B.countP (pred F) ≤ B.length := by
    let scores := rs.map (observedScore F K h)
    let cx := SampleVariance.sampleSums (SampleVariance.centered scores) N
    have result := actual_prefix_block F hnodup K h (hwidth F hf) law hn ha hD hK (hq F hf) (hsize F hf)
    change 3*cx.length ≤ 4*SampleVariance.goodCount cx (N*(scores.length*(2^K*a))) D at result
    have hc : B.map (centeredBlock rs (observedScore F K h)) = cx := centered_map rs _ N
    have hlen := congrArg List.length hc
    simp only [List.length_map] at hlen
    have count : B.countP (pred F) = SampleVariance.badCount cx (N*(scores.length*(2^K*a))) D := by
      rw [←hc]; simp [SampleVariance.badCount,List.countP_map,Function.comp_def,scores,pred,badBlock]; rfl
    have hp := good_plus_bad cx (N*(scores.length*(2^K*a))) D
    rw [count,hlen]; omega
  have bound := SampleVariance.simultaneous_prefix_bound B (Fs.map pred) (by
    intro g hg; obtain ⟨F,hf,rfl⟩ := List.mem_map.mp hg; exact quart F hf) s
  simpa only [List.any_map,List.length_map,Function.comp_def,pred,B,rs] using bound

/-- Interface for the explicitly clipped consecutive partitions. Only
indices in [0,m) need a valid distinguished label. -/
structure Geometry (m W : Nat) (plans : Bool→List (List Nat)) where
  pivot : Nat → Pivot (List.range m) plans
  label : ∀ j, j<m → (pivot j).window.j=j
  pre : ∀ j, j<m → (pivot j).window.pre=List.range j
  cover : ∀ j, j<m → ∀ i, j<i → i<m → i≤j+2*W → i∈(pivot j).window.right
  width : ∀ j, j<m → (pivot j).window.right.length≤4*W+1

/-- The exact natural-minimum indices that can contribute a prefix error. -/
def liveBand (m W t : Nat) : List Nat := List.range' (t-W) (min m (t+W) - (t-W))

theorem mem_live (m W t j : Nat) : j∈liveBand m W t ↔ j<m ∧ t≤j+W ∧ j<t+W := by
  simp only [liveBand,List.mem_range',Nat.one_mul]
  constructor
  · rintro ⟨i,hi,eq⟩; omega
  · rintro ⟨hm,hl,hu⟩; exact ⟨j-(t-W),by omega,by omega⟩

theorem live_size (m W t : Nat) : (liveBand m W t).length≤2*W := by
  simp only [liveBand,List.length_range']; omega

noncomputable def bandFields {m W plans} (G : Geometry m W plans) (t : Nat) (R : Nat→Bool) :
    Fields (List.range m) plans where
  live := liveBand m W t
  distinct := List.nodup_range' 1
  pivot := G.pivot
  label := fun j hj => G.label j ((mem_live _ _ _ _).mp hj).1
  payoff := fun j => prefixPayoff _ (readBits (G.pivot j).window.right R) (R j) (decide (t≤j))
  bounded := fun _ _ => prefix_payoff_bound _ _ _ _

/-- Ordinary centered survival on the literal full menu. Prefix membership
is supplied by R; the reference probes labels 0 through t−1. -/
def survivalDifference (m t : Nat) (R hit : Nat→Bool) : Int :=
  (if !(List.range m).any (fun i=>hit i && R i) then 1 else 0) -
  (if !(List.range m).any (fun i=>hit i && decide (i<t)) then 1 else 0)

/-- Actual minimum of the original word's hit positions in the menu. -/
def naturalMin (m : Nat) (z : Nat→Bool) : Option Nat := ((List.range m).filter z).min?

theorem natural_min_some {m j : Nat} {z : Nat→Bool} : naturalMin m z=some j ↔
    j<m ∧ z j=true ∧ ∀ i, i<m → z i=true → j≤i := by
  simp only [naturalMin,List.min?_eq_some_iff',List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨⟨hj,hz⟩,hp⟩; exact ⟨hj,hz,fun i hi h => hp i ⟨hi,h⟩⟩
  · rintro ⟨hj,hz,hp⟩; exact ⟨⟨hj,hz⟩,fun i hi => hp i hi.1 hi.2⟩

theorem natural_min_none {m : Nat} {z : Nat→Bool} : naturalMin m z=none ↔ ∀ i, i<m → z i=false := by
  simp only [naturalMin,List.min?_eq_none_iff,List.filter_eq_nil_iff,List.mem_range]
  simp only [Bool.not_eq_true]

theorem eligible_is_min {m W plans} (G : Geometry m W plans) (j : Nat) (hj : j<m) (z : Nat→Bool) :
    eligible (localWord (G.pivot j).window z)=true ↔ naturalMin m z=some j := by
  rw [eligible_minimum,G.pre j hj,G.label j hj,natural_min_some]
  simp only [Bool.and_eq_true,Bool.not_eq_true',List.any_eq_false,List.mem_range]
  constructor
  · rintro ⟨hb,hz⟩; refine ⟨hj,hz,?_⟩
    intro i hmi hi; by_cases hh : i<j
    · have := hb i hh; simp_all
    · omega
  · rintro ⟨_,hz,hm⟩; refine ⟨?_,hz⟩
    intro i hi; cases e : z i with
    | false => decide
    | true => have := hm i (by omega) e; omega

private theorem sum_point (js : List Nat) (hd : js.Nodup) (j : Nat) (f : Nat→Int) :
    sumOn js (fun i => if i=j then f i else 0) = if j∈js then f j else 0 := by
  induction js with
  | nil => simp [sumOn]
  | cons i js ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hd
    change (if i=j then f i else 0)+sumOn js _ = _
    rw [ih ht]; by_cases he : i=j <;> simp_all [List.mem_cons,eq_comm]

private theorem band_truth_min {m W plans} (G : Geometry m W plans) (t : Nat)
    (R z : Nat→Bool) (j : Nat) (h : naturalMin m z=some j) :
    truth (bandFields G t R) z = if j∈liveBand m W t then
      prefixPayoff _ (readBits (G.pivot j).window.right R) (R j) (decide (t≤j))
        (readBits (G.pivot j).window.right z) else 0 := by
  let f := fun i => prefixPayoff _ (readBits (G.pivot i).window.right R) (R i) (decide (t≤i))
    (readBits (G.pivot i).window.right z)
  change sumOn (liveBand m W t) (fun i => if eligible (localWord (G.pivot i).window z) then f i else 0)=_
  rw [←sum_point (liveBand m W t) (List.nodup_range' 1) j f]
  unfold sumOn; congr 1; apply List.map_congr_left
  intro i hi
  have eq := eligible_is_min G i ((mem_live _ _ _ _).mp hi).1 z
  rw [h] at eq
  simp only [Option.some.injEq,eq_comm (a:=j)] at eq
  simp [eq]

private theorem band_truth_empty {m W plans} (G : Geometry m W plans) (t : Nat)
    (R z : Nat→Bool) (h : naturalMin m z=none) : truth (bandFields G t R) z=0 := by
  rw [truth]; change sumOn (liveBand m W t) _=0
  have zero : sumOn (liveBand m W t) (fun _=>0)=0 := by rw [sum_constant,Int.mul_zero]
  apply Eq.trans _ zero; unfold sumOn; congr 1; apply List.map_congr_left
  intro i hi
  have eq := eligible_is_min G i ((mem_live _ _ _ _).mp hi).1 z
  rw [h] at eq
  change (if eligible (localWord (G.pivot i).window z) then _ else 0)=0
  simp [eq]

private theorem selected_any (m : Nat) (z R : Nat→Bool) :
    (List.range m).any (fun i=>z i && R i)=true ↔ ∃i, i<m ∧ z i=true ∧ R i=true := by
  simp only [List.any_eq_true,List.mem_range,Bool.and_eq_true]

private theorem reference_survives {m j} (z : Nat→Bool) (t : Nat) (hm : naturalMin m z=some j) :
    (!(List.range m).any (fun i=>z i && decide (i<t))) = decide (t≤j) := by
  obtain ⟨hj,hz,low⟩ := natural_min_some.mp hm
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',List.any_eq_false,List.mem_range,decide_eq_true_eq]
  constructor
  · intro hzall; by_cases lt : j<t
    · have := hzall j hj; simp [hz,lt] at this
    · omega
  · intro hjt i hi
    cases e : z i with
    | false => simp
    | true => have := low i hi e; simp [show ¬i<t by omega]

private theorem no_local_hits (labels : List Nat) (R z : Nat→Bool) :
    noPositiveHit (slots labels.length (readBits labels z) (readBits labels R)) =
      !labels.any (fun i=>z i && R i) := by
  rw [slots_read]; simp [noPositiveHit,tests,List.any_map,Function.comp_def]

private theorem right_mem_lt {m W plans} (G : Geometry m W plans) (i j : Nat)
    (h : i∈(G.pivot j).window.right) : i<m := by
  apply List.mem_range.mp
  rw [←(G.pivot j).menu_eq]; simp [Split.menu,h]

private theorem global_survives_at {m W plans} (G : Geometry m W plans) (t j : Nat)
    (R z : Nat→Bool) (band : inBand W t R) (live : j∈liveBand m W t)
    (hm : naturalMin m z=some j) :
    (!(List.range m).any (fun i=>z i && R i)) =
      (!R j && !(G.pivot j).window.right.any (fun i=>z i && R i)) := by
  obtain ⟨hj,hz,low⟩ := natural_min_some.mp hm
  obtain ⟨_,prox,_⟩ := (mem_live m W t j).mp live
  have selected : (List.range m).any (fun i=>z i && R i) =
      (R j || (G.pivot j).window.right.any (fun i=>z i && R i)) := by
    apply Bool.eq_iff_iff.mpr
    rw [selected_any]
    simp only [Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true]
    constructor
    · rintro ⟨i,hi,iz,ir⟩
      by_cases eq : i=j
      · exact Or.inl (eq ▸ ir)
      · have ji := low i hi iz
        have upper : i<t+W := by
          by_cases hh : t+W≤i
          · have := band.2 i hh; simp_all
          · omega
        exact Or.inr ⟨i,G.cover j hj i (by omega) hi (by omega),iz,ir⟩
    · rintro (rj|⟨i,ih,iz,ir⟩)
      · exact ⟨j,hj,hz,rj⟩
      · exact ⟨i,right_mem_lt G i j ih,iz,ir⟩
  rw [selected,Bool.not_or]

/-- The constructed scalar field equals the physical prefix-survival
contrast on every word, including a miss. Membership R need only obey the
two forced regions of a W-displaced prefix. -/
theorem band_truth {m W plans} (G : Geometry m W plans) (t : Nat) (R : Nat→Bool)
    (band : inBand W t R) (z : Nat→Bool) :
    truth (bandFields G t R) z=survivalDifference m t R z := by
  cases hm : naturalMin m z with
  | none =>
    rw [band_truth_empty G t R z hm]
    have empty (S : Nat→Bool) : (List.range m).any (fun i=>z i && S i)=false := by
      apply List.any_eq_false.mpr
      intro i hi; simp [(natural_min_none.mp hm) i (List.mem_range.mp hi)]
    simp [survivalDifference,empty]
  | some j =>
    rw [band_truth_min G t R z j hm]
    unfold survivalDifference
    rw [reference_survives z t hm]
    by_cases live : j∈liveBand m W t
    · rw [if_pos live,global_survives_at G t j R z band live hm]
      simp [prefixPayoff,no_local_hits]
    · rw [if_neg live]
      obtain ⟨hj,hz,low⟩ := natural_min_some.mp hm
      by_cases early : j+W<t
      · have found : (List.range m).any (fun i=>z i && R i)=true :=
          (selected_any m z R).mpr ⟨j,hj,hz,band.1 j early⟩
        simp [found,show ¬t≤j by omega]
      · have late : t+W≤j := by rw [mem_live] at live; omega
        have no : (List.range m).any (fun i=>z i && R i)=false := by
          apply List.any_eq_false.mpr
          intro i hi
          cases zi : z i with
          | false => simp
          | true =>
            have := low i (List.mem_range.mp hi) zi
            simp [band.2 i (by omega)]
        simp [no,show t≤j by omega]

/-- Literal reference minima, so a single frequency upper bound Q is
usable before choosing any prefix. -/
theorem band_min_count {m W plans} (G : Geometry m W plans) (j : Nat) (hj : j<m)
    (law : List (Nat→Bool)) : minCount (G.pivot j).window law =
      law.countP (fun z=>decide (naturalMin m z=some j)) := by
  unfold minCount
  congr 1
  funext z
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using eligible_is_min G j hj z

/-- The normalized expected score of a legal prefix is precisely the
centered physical survival probability. Each original word is one ticket. -/
theorem literal_prefix_mean {m W plans} (G : Geometry m W plans) (t : Nat) (R : Nat→Bool)
    (band : inBand W t R) (h : Nat) (law : List (Nat→Bool))
    (cap : ∀ z∈law, (List.range m).countP z≤h+1) :
    sumOn (records (List.range m) plans law) (observedScore (bandFields G t R) (4*W+1) h) =
      ((choices m*2^(4*W+1):Nat):Int)*sumOn law (survivalDifference m t R) := by
  have mean := actual_prefix_mean (bandFields G t R) List.nodup_range (4*W+1) h
    (fun j hj => G.width j ((mem_live m W t j).mp hj).1) law cap
  have hf := funext (band_truth G t R band)
  simpa only [List.length_range,hf] using mean

abbrev Prefix := Nat × (Nat→Bool)

/-- A finite common-sample confidence bound on the entire list of prefix
queries. Q is the largest allowed count of any natural minimum among the
original tickets. For a legal query its population center is exactly the
one in `literal_prefix_mean`.

The block length condition has order D²/a² times q W^(h+1) for fixed h,
where q=Q/law.length and words have at most h+1 hits. The separate cap on
word size is required for the mean identity, and the variance bound holds
even on words with arbitrary additional hits. -/
theorem literal_prefix_confidence {m W plans} (G : Geometry m W plans) (Ps : List Prefix)
    (h : Nat) (law : List (Nat→Bool)) {N Q a D : Nat}
    (hn : 0<N) (ha : 0<a) (hD : 0<D) (hL : 0<law.length)
    (freq : ∀ j, j<m → law.countP (fun z=>decide (naturalMin m z=some j)) ≤ Q)
    (budget : 16*D*D*(2*W)*Q*(9^h*(4*W+2)^h) ≤ law.length*N*a*a) (s : Nat) :
    let rs := records (List.range m) plans law
    let draws := SampleVariance.iidTuples (rawBlocks rs N) (2*s+1)
    (2*4^s)*draws.countP (fun row => Ps.any fun p =>
      SampleVariance.atLeastBad (badBlock rs (4*W+1) h N a D (bandFields G p.1 p.2)) (s+1) row) ≤
      Ps.length*(3^s*draws.length) := by
  let fields := fun (p : Prefix) => bandFields G p.1 p.2
  have pass (p : Prefix) : 16*D*D*(fields p).live.length*Q*(9^h*((4*W+1)+1)^h) ≤ law.length*N*a*a :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right Q
      (Nat.mul_le_mul_left (16*D*D) (live_size m W p.1)))) budget
  have bound := simultaneous_raw_prefixes (Ps.map fields) List.nodup_range (4*W+1) h (by
    intro F hF j hj; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hF
    exact G.width j ((mem_live m W p.1 j).mp hj).1) law hn ha hD hL (Q:=Q) (by
    intro F hF j hj; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hF
    have jm := ((mem_live m W p.1 j).mp hj).1
    change minCount (G.pivot j).window law ≤ Q
    rw [band_min_count G j jm law]; exact freq j jm) (by
    intro F hF; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hF; exact pass p) s
  simpa only [List.any_map,List.length_map,Function.comp_def,fields] using bound

end Screening.GlobalOneHit

/- Source module: Screening.MedianLearner -/

/-! Deterministic steps after joint amplification: select the actual sorted
middle block and minimize the estimated sum over the candidate orders. -/
namespace Screening.MedianLearner

def median (s : Nat) (samples : List Int) : Int :=
  ((samples.mergeSort (fun a b => decide (a ≤ b)))[s]?).getD 0

theorem median_of_majority (samples : List Int) (s : Nat) (lo hi : Int)
    (size : samples.length = 2*s+1)
    (few : samples.countP (fun x => decide (x < lo ∨ hi < x)) ≤ s) :
    lo ≤ median s samples ∧ median s samples ≤ hi := by
  let le := fun a b : Int => decide (a ≤ b)
  let ordered := samples.mergeSort le
  let bad := fun x : Int => decide (x < lo ∨ hi < x)
  have perm := List.mergeSort_perm samples le
  have len : ordered.length = 2*s+1 := perm.length_eq.trans size
  have pos : s < ordered.length := by omega
  have total : ordered.countP bad ≤ s := (List.Perm.countP_eq bad perm) ▸ few
  have sorted : ordered.Pairwise (fun a b => a ≤ b) := by
    have h := List.sorted_mergeSort (le := le)
      (by intro a b c; simp [le]; omega) (by intro a b; simp [le]; omega) samples
    simpa [ordered,le] using h
  have mono (a b : Nat) (ha : a < ordered.length) (hb : b < ordered.length) (hab : a ≤ b) :
      ordered[a] ≤ ordered[b] := by
    by_cases eq : a=b
    · subst b; exact Int.le_refl _
    · exact List.pairwise_iff_getElem.mp sorted a b ha hb (by omega)
  have med : median s samples = ordered[s] := by
    change (ordered[s]?).getD 0 = _
    simp [List.getElem?_eq_getElem pos]
  rw [med]
  constructor
  · apply Int.le_of_not_gt
    intro low
    have nbad : (ordered.take (s+1)).countP bad = (ordered.take (s+1)).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i, h, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [List.getElem_take]
      simp only [List.length_take] at h
      have hle := mono i s (by omega) pos (by omega)
      simp [bad]; omega
    have sub := (List.take_prefix (s+1) ordered).countP_le (p := bad)
    rw [nbad,List.length_take] at sub
    omega
  · apply Int.le_of_not_gt
    intro high
    have nbad : (ordered.drop s).countP bad = (ordered.drop s).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i,h,rfl⟩ := List.mem_iff_getElem.mp hx
      rw [List.getElem_drop]
      simp only [List.length_drop] at h
      have hle := mono s (s+i) pos (by omega) (by omega)
      simp [bad]; omega
    have sub := (List.drop_suffix s ordered).countP_le (p := bad)
    rw [nbad,List.length_drop] at sub
    omega

def best (score : α → Int) (first : α) : List α → α
  | [] => first
  | x :: rest => if score first ≤ score x then best score first rest else best score x rest

theorem best_spec (score : α → Int) (first : α) (rest : List α) :
    best score first rest ∈ first::rest ∧
    ∀ x ∈ first::rest, score (best score first rest) ≤ score x := by
  induction rest generalizing first with
  | nil => simp [best]
  | cons x xs ih =>
    by_cases h : score first ≤ score x
    · rw [best,if_pos h]
      obtain ⟨mem,min⟩ := ih first
      constructor
      · rcases List.mem_cons.mp mem with he | ht
        · simp [he]
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)
      · intro y hy
        rcases (List.mem_cons.mp hy) with rfl|hy
        · exact min _ (by simp)
        rcases (List.mem_cons.mp hy) with rfl|hy
        · exact Int.le_trans (min _ (by simp)) h
        · exact min _ (by simp [hy])
    · rw [best,if_neg h]
      obtain ⟨mem,min⟩ := ih x
      constructor
      · exact List.mem_cons_of_mem _ mem
      · intro y hy
        rcases (List.mem_cons.mp hy) with rfl|hy
        · exact Int.le_trans (min x (by simp)) (by omega)
        · exact min _ hy

theorem selected_regret (score actual : α → Int) (first : α) (rest : List α) (err : Int)
    (uniform : ∀ x ∈ first::rest, actual x - err ≤ score x ∧ score x ≤ actual x + err)
    (competitor : α) (hc : competitor ∈ first::rest) :
    actual (best score first rest) - actual competitor ≤ 2*err := by
  obtain ⟨hm, hmin⟩ := best_spec score first rest
  have lower := (uniform _ hm).1
  have upper := (uniform _ hc).2
  have cmp := hmin _ hc
  omega


open ScreeningCost

def estimated (s : Nat) (blocks : List T → List Int) (order : List T) : Int :=
  ((properPrefixes order).map (fun pre => median s (blocks pre))).sum

private theorem sum_error (prefixes : List (List T)) (truth : List T → Nat)
    (value : List T → Int) (e : Int)
    (each : ∀ p ∈ prefixes, (truth p : Int)-e ≤ value p ∧ value p ≤ (truth p : Int)+e) :
    (total prefixes truth : Int) - (prefixes.length : Int)*e ≤ (prefixes.map value).sum ∧
    (prefixes.map value).sum ≤ (total prefixes truth : Int) + (prefixes.length : Int)*e := by
  induction prefixes with
  | nil => simp [total]
  | cons p ps ih =>
    have a := each p (by simp)
    have b := ih (fun q h => each q (by simp [h]))
    change ((truth p + total ps truth : Nat) : Int) - ((ps.length+1 : Nat) : Int)*e ≤ _ ∧
      _ ≤ ((truth p+total ps truth : Nat):Int) + ((ps.length+1 : Nat):Int)*e
    simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul,
      List.map_cons, List.sum_cons]
    omega

/-- From prefix block-majority guarantees to the scan cost of the order
actually selected by sorting blocks and minimizing the sum of medians.
All candidate full schedules have the same length and fallback mass. -/
theorem median_scan_regret (law : List (X × Nat)) (hit : X → T → Bool)
    (fallback m s : Nat) (e : Int) (blocks : List T → List Int)
    (first : List T) (rest : List (List T)) (competitor : List T)
    (inside : competitor ∈ first::rest)
    (same : ∀ order ∈ first::rest, order.length=m ∧
        survivalMass law hit order = survivalMass law hit first)
    (majorities : ∀ order ∈ first::rest, ∀ p ∈ properPrefixes order,
        (blocks p).length = 2*s+1 ∧
        (blocks p).countP (fun x => decide
          (x < (survivalMass law hit p : Int)-e ∨ (survivalMass law hit p : Int)+e < x)) ≤ s) :
    (populationCost law hit fallback (best (estimated s blocks) first rest) : Int) -
      populationCost law hit fallback competitor ≤ 2*((m:Int)*e) := by
  let common : Int := (fallback * survivalMass law hit first : Nat)
  let actual := fun o => (populationCost law hit fallback o : Int) - common
  have hu (o : List T) (ho : o ∈ first::rest) :
      actual o - (m:Int)*e ≤ estimated s blocks o ∧ estimated s blocks o ≤ actual o + (m:Int)*e := by
    obtain ⟨len, mass⟩ := same o ho
    have a : actual o = (total (properPrefixes o) (survivalMass law hit) : Int) := by
      dsimp only [actual,common]
      rw [populationCost_eq_prefix_survivals,mass,Int.natCast_add]; omega
    have size : (properPrefixes o).length = m := by simp [properPrefixes,len]
    have b := sum_error (properPrefixes o) (survivalMass law hit) (fun p => median s (blocks p)) e
      (fun p hp => median_of_majority _ _ _ _ (majorities o ho p hp).1 (majorities o ho p hp).2)
    rw [size] at b
    simpa only [a,estimated] using b
  have result := selected_regret (estimated s blocks) actual first rest ((m:Int)*e) hu competitor inside
  dsimp only [actual] at result
  omega

end Screening.MedianLearner

/- Source module: Screening.SignedCutoffCounterexample -/

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

/- Source module: Screening.PartitionWindows -/

/-! The two publicly chosen consecutive tilings on the literal finite menu.
Labels are zero-based, so the final label is m−1. Empty end blocks are omitted. -/

namespace Screening.PartitionWindows

open Screening.GlobalOneHit (Split Pivot)

def halfWidth (W : Nat) : Nat := 2 * W + 1
def width (W : Nat) : Nat := 2 * halfWidth W
def offset (W : Nat) (shifted : Bool) : Nat := if shifted then halfWidth W else 0

private theorem width_positive (W : Nat) : 0 < width W := by
  simp [width, halfWidth]

private theorem offset_lt_width (W : Nat) (shifted : Bool) : offset W shifted < width W := by
  cases shifted <;> simp [offset, width, halfWidth] <;> omega

/-- Infinite block index before clipping at the two ends of the menu. -/
def blockIndex (W : Nat) (shifted : Bool) (i : Nat) : Nat :=
  (i + offset W shifted) / width W

/-- A left boundary clipped to the interval from zero through m. -/
def boundary (m W : Nat) (shifted : Bool) (k : Nat) : Nat :=
  min m (k * width W - offset W shifted)

/-- The kth block consists of consecutive, ascending menu labels. -/
def block (m W : Nat) (shifted : Bool) (k : Nat) : List Nat :=
  List.range' (boundary m W shifted k)
    (boundary m W shifted (k + 1) - boundary m W shifted k)

def blockCount (m W : Nat) (shifted : Bool) : Nat :=
  if m = 0 then 0 else blockIndex W shifted (m - 1) + 1

/-- Both tilings are fixed before the current word is observed. -/
def plans (m W : Nat) (shifted : Bool) : List (List Nat) :=
  (List.range (blockCount m W shifted)).map (block m W shifted)

private theorem boundary_le_menu (m W : Nat) (shifted : Bool) (k : Nat) :
    boundary m W shifted k ≤ m := Nat.min_le_left ..

private theorem div_mono {x y d : Nat} (positive : 0 < d) (ordered : x ≤ y) :
    x / d ≤ y / d :=
  (Nat.le_div_iff_mul_le positive).mpr (Nat.le_trans (Nat.div_mul_le_self x d) ordered)

private theorem boundary_monotone (m W : Nat) (shifted : Bool) {a b : Nat} (order : a ≤ b) :
    boundary m W shifted a ≤ boundary m W shifted b := by
  unfold boundary
  have products := Nat.mul_le_mul_right (width W) order
  omega

private theorem boundary_step_le (m W : Nat) (shifted : Bool) (k : Nat) :
    boundary m W shifted (k + 1) ≤ boundary m W shifted k + width W := by
  unfold boundary
  rw [Nat.add_mul, Nat.one_mul]
  omega

private theorem block_index_window {m W i : Nat} {shifted : Bool} (inside : i < m) :
    boundary m W shifted (blockIndex W shifted i) ≤ i ∧
      i < boundary m W shifted (blockIndex W shifted i + 1) := by
  let D := width W
  let o := offset W shifted
  let k := blockIndex W shifted i
  have low : k * D ≤ i + o := Nat.div_mul_le_self (i + o) D
  have high : i + o < (k + 1) * D := by
    apply (Nat.div_lt_iff_lt_mul (width_positive W)).mp
    exact Nat.lt_succ_self k
  change min m (k * D - o) ≤ i ∧ i < min m ((k + 1) * D - o)
  omega

private theorem index_lt_blockCount {m W i : Nat} {shifted : Bool} (inside : i < m) :
    blockIndex W shifted i < blockCount m W shifted := by
  have positive : m ≠ 0 := by omega
  unfold blockCount
  rw [if_neg positive]
  apply Nat.lt_succ_of_le
  unfold blockIndex
  exact div_mono (width_positive W) (by omega)

private theorem boundary_end (m W : Nat) (shifted : Bool) :
    boundary m W shifted (blockCount m W shifted) = m := by
  by_cases empty : m = 0
  · simp [empty, boundary]
  · unfold boundary blockCount
    rw [if_neg empty]
    let k := blockIndex W shifted (m - 1)
    have high : m - 1 + offset W shifted < (k + 1) * width W := by
      apply (Nat.div_lt_iff_lt_mul (width_positive W)).mp
      exact Nat.lt_succ_self k
    change min m ((k + 1) * width W - offset W shifted) = m
    omega

private theorem range_parts {a b c : Nat} (lo : a ≤ b) (hi : b ≤ c) :
    List.range' a (b - a) ++ List.range' b (c - b) = List.range' a (c - a) := by
  have first : a + (b - a) = b := by omega
  have both : (b - a) + (c - b) = c - a := by omega
  simpa only [first, both] using List.range'_append_1 (s := a) (m := b - a) (n := c - b)

private theorem range_append_range' {i j : Nat} (ordered : i ≤ j) :
    List.range i ++ List.range' i (j - i) = List.range j := by
  simpa only [List.range_eq_range', Nat.sub_zero] using range_parts (Nat.zero_le i) ordered

private theorem flatten_blocks_prefix (m W : Nat) (shifted : Bool) (n : Nat) :
    ((List.range n).map (block m W shifted)).flatten =
      List.range (boundary m W shifted n) := by
  induction n with
  | zero => simp [boundary]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact range_append_range' (boundary_monotone m W shifted (Nat.le_succ n))

/-- The two actual block lists partition the entire finite menu in order. -/
theorem plans_flatten (m W : Nat) (shifted : Bool) :
    (plans m W shifted).flatten = List.range m := by
  rw [plans, flatten_blocks_prefix, boundary_end]

/-- Every included block is nonempty, including the clipped end blocks. -/
theorem plans_nonempty_blocks (m W : Nat) (shifted : Bool) :
    ∀ bs ∈ plans m W shifted, 0 < bs.length := by
  intro bs member
  obtain ⟨k, inside, rfl⟩ := List.mem_map.mp member
  have valid := List.mem_range.mp inside
  have nonempty : m ≠ 0 := by
    intro zero
    simp [blockCount, zero] at valid
  have leLast : k ≤ blockIndex W shifted (m - 1) := by
    simp only [blockCount, nonempty, if_false] at valid
    omega
  have beginBound := Nat.mul_le_mul_right (width W) leLast
  have lastBound := Nat.div_mul_le_self (m - 1 + offset W shifted) (width W)
  have lower : k * width W - offset W shifted < m := by
    change (blockIndex W shifted (m - 1)) * width W ≤ m - 1 + offset W shifted at lastBound
    omega
  have positive := width_positive W
  have offsetSmall := offset_lt_width W shifted
  have endpoints : k * width W - offset W shifted < (k + 1) * width W - offset W shifted := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  unfold block boundary
  rw [List.length_range', Nat.min_eq_right (Nat.le_of_lt lower)]
  omega

/-- Membership in a finite shifted block agrees with the integer-line block
index, restricted to the finite menu. -/
theorem mem_block_iff {m W i k : Nat} {shifted : Bool} :
    i ∈ block m W shifted k ↔ i < m ∧ blockIndex W shifted i = k := by
  unfold block
  rw [List.mem_range'_1,
    Nat.add_sub_of_le (boundary_monotone m W shifted (Nat.le_succ k))]
  constructor
  · rintro ⟨lo, hi⟩
    have inside := Nat.lt_of_lt_of_le hi (boundary_le_menu m W shifted (k + 1))
    refine ⟨inside, ?_⟩
    have lo' : k * width W - offset W shifted ≤ i := by
      unfold boundary at lo
      omega
    have hi' : i < (k + 1) * width W - offset W shifted := by
      exact Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
    unfold blockIndex
    have first := (Nat.le_div_iff_mul_le (width_positive W)).mpr
      (show k * width W ≤ i + offset W shifted by omega)
    have last := (Nat.div_lt_iff_lt_mul (width_positive W)).mpr
      (show i + offset W shifted < (k + 1) * width W by omega)
    omega
  · rintro ⟨inside, index⟩
    simpa only [index] using block_index_window (W := W) (shifted := shifted) inside

private theorem blocks_getElem {m W k : Nat} {shifted : Bool}
    (valid : k < (plans m W shifted).length) :
    (plans m W shifted)[k] = block m W shifted k := by
  simp [plans]

private theorem flatten_plans_take {m W k : Nat} {shifted : Bool}
    (valid : k ≤ blockCount m W shifted) :
    ((plans m W shifted).take k).flatten = List.range (boundary m W shifted k) := by
  rw [plans, ← List.map_take, List.take_range, Nat.min_eq_left valid, flatten_blocks_prefix]

/-- Use the unshifted plan when it is suitable, otherwise the shifted plan. -/
def select (W j : Nat) : Bool :=
  decide (blockIndex W false j ≠ blockIndex W false (j + 2 * W))

/-- The selected plan keeps the entire forward interval with the pivot. -/
theorem selected_index_eq (W j i : Nat) (low : j ≤ i) (high : i ≤ j + 2 * W) :
    blockIndex W (select W j) i = blockIndex W (select W j) j := by
  by_cases first : blockIndex W false j = blockIndex W false (j + 2 * W)
  · have selected : select W j = false := by simp [select, first]
    rw [selected]
    have l : blockIndex W false j ≤ blockIndex W false i := div_mono (width_positive W) (by omega)
    have r : blockIndex W false i ≤ blockIndex W false (j + 2 * W) :=
      div_mono (width_positive W) (by omega)
    omega
  · have selected : select W j = true := by simp [select, first]
    rw [selected]
    obtain ⟨o, zero | shifted, covers⟩ := Screening.OneHitInversion.two_shift_cover W j
    · subst o
      have bad := covers (j + 2 * W) (by omega) (by omega)
      exact False.elim (first (by simpa [blockIndex, offset, width, halfWidth] using bad))
    · subst o
      simpa [blockIndex, offset, width, halfWidth] using (covers i low high).symm

def blockStart (m W j : Nat) : Nat :=
  boundary m W (select W j) (blockIndex W (select W j) j)

def blockEnd (m W j : Nat) : Nat :=
  boundary m W (select W j) (blockIndex W (select W j) j + 1)

private def makeSplit (m W j : Nat) : Split where
  before := (plans m W (select W j)).take (blockIndex W (select W j) j)
  left := List.range' (blockStart m W j) (j - blockStart m W j)
  j := j
  right := List.range' (j + 1) (blockEnd m W j - (j + 1))
  after := (plans m W (select W j)).drop (blockIndex W (select W j) j + 1)

private theorem pivot_bounds {m W j : Nat} (inside : j < m) :
    blockStart m W j ≤ j ∧ j < blockEnd m W j :=
  block_index_window inside

private theorem block_at_pivot {m W j : Nat} (inside : j < m) :
    block m W (select W j) (blockIndex W (select W j) j) =
      (makeSplit m W j).left ++ [j] ++ (makeSplit m W j).right := by
  have bounds := pivot_bounds (W := W) inside
  have joinOne : List.range' (blockStart m W j) (j - blockStart m W j) ++ [j] =
      List.range' (blockStart m W j) (j + 1 - blockStart m W j) := by
    have taken := range_parts bounds.1 (Nat.le_succ j)
    have one : j + 1 - j = 1 := by omega
    simpa [one, List.range'] using taken
  change List.range' (blockStart m W j) (blockEnd m W j - blockStart m W j) =
    List.range' (blockStart m W j) (j - blockStart m W j) ++ [j] ++
      List.range' (j + 1) (blockEnd m W j - (j + 1))
  rw [joinOne]
  exact (range_parts (Nat.le_trans bounds.1 (Nat.le_succ j)) bounds.2).symm

private theorem makeSplit_plan {m W j : Nat} (inside : j < m) :
    (makeSplit m W j).blocks = plans m W (select W j) := by
  let a := select W j
  let k := blockIndex W a j
  let bs := plans m W a
  have valid : k < bs.length := by simpa [bs, plans] using index_lt_blockCount (W := W) (shifted := a) inside
  have atIndex : bs[k] = block m W a k := blocks_getElem valid
  have joined := List.take_append_drop k bs
  rw [List.drop_eq_getElem_cons valid, atIndex, block_at_pivot inside] at joined
  change bs.take k ++ [(makeSplit m W j).left ++ [j] ++ (makeSplit m W j).right] ++
    bs.drop (k + 1) = bs
  simpa [List.append_assoc] using joined

private theorem split_menu_eq_flatten (x : Split) : x.blocks.flatten = x.menu := by
  simp [Split.blocks, Split.menu, Split.pre, Split.post, List.flatten_append, List.append_assoc]

/-- The actual pivot decomposition for an in-menu label. -/
noncomputable def pivot (m W j : Nat) (inside : j < m) : Pivot (List.range m) (plans m W) where
  window := makeSplit m W j
  selected := select W j
  menu_eq := by rw [← split_menu_eq_flatten, makeSplit_plan inside, plans_flatten]
  plan_eq := (makeSplit_plan inside).symm

theorem pivot_label (m W j : Nat) (inside : j < m) : (pivot m W j inside).window.j = j := rfl

theorem pivot_pre (m W j : Nat) (inside : j < m) :
    (pivot m W j inside).window.pre = List.range j := by
  have within := index_lt_blockCount (W := W) (shifted := select W j) inside
  change ((plans m W (select W j)).take (blockIndex W (select W j) j)).flatten ++
    List.range' (blockStart m W j) (j - blockStart m W j) = List.range j
  rw [flatten_plans_take (Nat.le_of_lt within)]
  exact range_append_range' (pivot_bounds (W := W) inside).1

theorem pivot_right_eq_segment (m W j : Nat) (inside : j < m) :
    (pivot m W j inside).window.right =
      List.range' (j + 1) (blockEnd m W j - (j + 1)) := rfl

theorem pivot_right_mem_iff (m W j i : Nat) (inside : j < m) :
    i ∈ (pivot m W j inside).window.right ↔ j < i ∧ i < blockEnd m W j := by
  rw [pivot_right_eq_segment, List.mem_range'_1]
  have bounds := pivot_bounds (W := W) inside
  omega

/-- The entire needed forward window survives end clipping. -/
theorem pivot_forward_cover (m W j i : Nat) (inside : j < m)
    (after : j ≤ i) (beforeEnd : i < m) (within : i ≤ j + 2 * W) :
    i ∈ (pivot m W j inside).window.j :: (pivot m W j inside).window.right := by
  rw [pivot_label, List.mem_cons]
  by_cases same : i = j
  · exact Or.inl same
  · have blocks := selected_index_eq W j i after within
    have ib := block_index_window (W := W) (shifted := select W j) beforeEnd
    rw [blocks] at ib
    exact Or.inr ((pivot_right_mem_iff m W j i inside).mpr ⟨by omega, ib.2⟩)

theorem pivot_right_width (m W j : Nat) (inside : j < m) :
    (pivot m W j inside).window.right.length ≤ 4 * W + 1 := by
  rw [pivot_right_eq_segment, List.length_range']
  have bounds := pivot_bounds (W := W) inside
  have widthBound := boundary_step_le m W (select W j) (blockIndex W (select W j) j)
  change blockEnd m W j ≤ blockStart m W j + width W at widthBound
  unfold width halfWidth at widthBound
  omega

/-- A convenient total pivot function for a nonempty menu; labels outside
the menu are assigned the pivot of label zero. -/
noncomputable def pivotOrFirst (m W : Nat) (nonempty : 0 < m) (j : Nat) : Pivot (List.range m) (plans m W) :=
  if inside : j < m then pivot m W j inside else pivot m W 0 nonempty

theorem pivotOrFirst_of_lt (m W : Nat) (nonempty : 0 < m) {j : Nat} (inside : j < m) :
    pivotOrFirst m W nonempty j = pivot m W j inside := by simp [pivotOrFirst, inside]

/-- All the geometric hypotheses of the common whole-menu estimator,
discharged by its two literal public tilings. -/
noncomputable def geometry (m W : Nat) (nonempty : 0 < m) :
    Screening.GlobalOneHit.Geometry m W (plans m W) where
  pivot := pivotOrFirst m W nonempty
  label := by
    intro j inside
    rw [pivotOrFirst_of_lt m W nonempty inside, pivot_label]
  pre := by
    intro j inside
    rw [pivotOrFirst_of_lt m W nonempty inside, pivot_pre]
  cover := by
    intro j inside i after beforeEnd within
    rw [pivotOrFirst_of_lt m W nonempty inside]
    have localMem := pivot_forward_cover m W j i inside (Nat.le_of_lt after) beforeEnd within
    rw [pivot_label, List.mem_cons] at localMem
    exact localMem.resolve_left (Nat.ne_of_gt after)
  width := by
    intro j inside
    rw [pivotOrFirst_of_lt m W nonempty inside]
    exact pivot_right_width m W j inside

end Screening.PartitionWindows

/- Source module: Screening.PositiveCutoff -/

/-! Finite arithmetic behind the relative-cost proposition on positive odd
inputs. Physical probabilities are represented by integer weights and a common
normalizing constant. All bounds below are homogeneous in the weights. -/
namespace Screening.PositiveCutoff

open Screening.IntervalCounts

/-- If an odd modulus hits, it is no larger than the largest positive word.
The one-residue count consequently gives uniform hit probability at most 5/v,
including the case of no hits. -/
theorem modulus_hits_bound (a L v : Nat) (odd : v%2 = 1)
    (cap : ∀ k < L, word a k ≤ 4*L) :
    hitCount a v L * v ≤ 5*L := by
  by_cases zero : hitCount a v L = 0
  · simp [zero]
  have positive : 0 < hitCount a v L := by omega
  obtain ⟨k,mem,hk⟩ := List.countP_pos_iff.mp positive
  have divides : v ∣ word a k := by simpa using hk
  have vle := Nat.le_of_dvd (show 0 < word a k by simp [word]) divides
  have wle := cap k (List.mem_range.mp mem)
  have err := count_error odd a L
  omega

/-- The corresponding bound for *literal simultaneous* proper-prime tests.
Properness need not be assumed for this upper bound. -/
theorem pair_count_bound {a L p r : Nat} (pp : IsPrime p) (rp : IsPrime r)
    (different : p ≠ r) (op : p%2 = 1) (orr : r%2 = 1)
    (cap : ∀ k < L, word a k ≤ 4*L) :
    containmentCount a L [p,r] * (p*r) ≤ 5*L := by
  have unique : [p,r].Nodup := by simp [different]
  have primes : ∀ j ∈ [p,r], IsPrime j := by simpa using And.intro pp rp
  have odd : ∀ j ∈ [p,r], j%2 = 1 := by simpa using And.intro op orr
  rw [containment_eq a L [p,r] unique primes]
  simpa [product] using modulus_hits_bound a L (product [p,r]) (odd_product _ odd) cap

def eventWeight (ks : List Nat) (weight : Nat → Nat) (event : Nat → Bool) : Nat :=
  (ks.map (fun k => if event k then weight k else 0)).sum

private theorem weight_band (ks : List Nat) (weight : Nat → Nat) (event : Nat → Bool)
    (lo hi : Nat) (band : ∀ k ∈ ks, lo ≤ weight k ∧ weight k ≤ hi) :
    lo * ks.countP event ≤ eventWeight ks weight event ∧
    eventWeight ks weight event ≤ hi * ks.countP event := by
  induction ks with
  | nil => simp [eventWeight]
  | cons k ks ih =>
    have hk := band k (by simp)
    have rest := ih (fun i hi => band i (by simp [hi]))
    cases he : event k <;>
      simp [eventWeight,he,List.countP_cons,Nat.mul_add] at rest ⊢ <;> omega

def marginal (a L p : Nat) (w : Nat → Nat) :=
  eventWeight (List.range L) w (fun k => decide (p ∣ word a k))
def pairMass (a L p r : Nat) (w : Nat → Nat) :=
  eventWeight (List.range L) w (fun k => [p,r].all (fun j => decide (j ∣ word a k)))
def mass (L : Nat) (w : Nat → Nat) := eventWeight (List.range L) w (fun _ => true)

private theorem marginal_lower {a L p lo hi : Nat} (w : Nat → Nat) (op : p%2 = 1)
    (band : ∀ k < L, lo ≤ w k ∧ w k ≤ hi) (pos : 0 < marginal a L p w) :
    L*lo ≤ marginal a L p w*(2*p) := by
  have wb := weight_band (List.range L) w (fun k => decide (p ∣ word a k)) lo hi
    (fun k hk => band k (List.mem_range.mp hk))
  change lo * hitCount a p L ≤ marginal a L p w ∧ marginal a L p w ≤ hi * hitCount a p L at wb
  have cnt : hitCount a p L ≠ 0 := by
    intro h
    simp [h] at wb
    omega
  have cntpos : 1 ≤ hitCount a p L := by omega
  have pp := Nat.mul_le_mul_right p cntpos
  have err := count_error op a L
  have lower : L ≤ 2*(hitCount a p L*p) := by simp only [Nat.one_mul] at pp; omega
  calc
    L*lo ≤ (2*(hitCount a p L*p))*lo := Nat.mul_le_mul_right _ lower
    _ = (lo*hitCount a p L)*(2*p) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ wb.1

/-- For two distinct primes with positive hit probabilities, under a rational
word law with per-word weights in [lo,hi], this says
Pr[both] ≤ 20 (hi/lo)^2 Pr[p hits] Pr[r hits] (lo>0).
In particular equal marginals q give a uniform quadratic pair bound. -/
theorem pair_probability_bound {a L p r lo hi : Nat} (w : Nat → Nat)
    (pp : IsPrime p) (rp : IsPrime r) (different : p ≠ r)
    (op : p%2 = 1) (orr : r%2 = 1) (cap : ∀ k < L, word a k ≤ 4*L)
    (band : ∀ k < L, lo ≤ w k ∧ w k ≤ hi)
    (hp : 0 < marginal a L p w) (hr : 0 < marginal a L r w) :
    pairMass a L p r w * mass L w * (lo*lo) ≤
      20*(hi*hi)*(marginal a L p w * marginal a L r w) := by
  have kw := fun k hk => band k (List.mem_range.mp hk)
  have wm := (weight_band (List.range L) w (fun _ => true) lo hi kw).2
  have zbound : mass L w ≤ hi*L := by simpa [mass] using wm
  let cnt := containmentCount a L [p,r]
  have pairbound : pairMass a L p r w ≤ hi*cnt :=
    (weight_band (List.range L) w _ lo hi kw).2
  have capbound : cnt * (p*r) ≤ 5*L := pair_count_bound pp rp different op orr cap
  have psmall := marginal_lower w op band hp
  have rsmall := marginal_lower w orr band hr
  have pq : 0 < p*r := Nat.mul_pos (by have := pp.1; omega) (by have := rp.1; omega)
  apply Nat.le_of_mul_le_mul_right (c := p*r) ?_ pq
  calc
    _ ≤ ((hi*cnt)*(hi*L)*(lo*lo))*(p*r) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul pairbound zbound))
    _ = (hi*hi)*(cnt*(p*r))*(L*(lo*lo)) := by ac_rfl
    _ ≤ (hi*hi)*(5*L)*(L*(lo*lo)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ capbound)
    _ = (5*(hi*hi))*((L*lo)*(L*lo)) := by ac_rfl
    _ ≤ (5*(hi*hi))*((marginal a L p w*(2*p))*(marginal a L r w*(2*r))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul psmall rsmall)
    _ = _ := by
      change _ = ((5*(2*2))*(hi*hi)*(marginal a L p w*marginal a L r w))*(p*r)
      ac_rfl

open Screening.ScreeningCost

/-- Number of unordered pairs of distinct test positions hit on this word. -/
def simultaneousPairs (f : T → Bool) : List T → Nat
  | [] => 0
  | i::xs => (if f i then xs.countP f else 0) + simultaneousPairs f xs

private theorem bonferroni_word (f : T → Bool) (xs : List T) :
    1 ≤ (survives f xs).toNat + xs.countP f ∧
      (survives f xs).toNat + xs.countP f ≤ 1 + simultaneousPairs f xs := by
  induction xs with
  | nil => simp [survives,simultaneousPairs]
  | cons i xs tail =>
    cases hi : f i <;>
      simp [survives,hi,List.countP_cons,simultaneousPairs] at tail ⊢ <;> omega

/-- Two-term Bonferroni for a finite input law. The middle term is the
survival mass plus the sum of the actual hit counts, with no independence
assumption or cap on simultaneous hits. -/
theorem bonferroni_population (law : List (X × Nat)) (hit : X → T → Bool) (xs : List T) :
    let Z := weighted law (fun _ => 1)
    let singles := weighted law (fun x => xs.countP (hit x))
    let pairs := weighted law (fun x => simultaneousPairs (hit x) xs)
    Z ≤ survivalMass law hit xs + singles ∧
      survivalMass law hit xs + singles ≤ Z + pairs := by
  dsimp only
  induction law with
  | nil => simp [weighted,survivalMass,total]
  | cons a law ih =>
    have wordBound := bonferroni_word (hit a.1) xs
    have lo := Nat.mul_le_mul_left a.2 wordBound.1
    have hi := Nat.mul_le_mul_left a.2 wordBound.2
    simp only [Nat.mul_add,Nat.mul_one] at lo hi
    simp only [survivalMass,weighted,total,List.map_cons,List.sum_cons,Nat.mul_one] at ih ⊢
    omega

private def prefixSum (s : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => prefixSum s n + s n

/-- Expected independent-model cost, scaled by its common grid denominator.
The survival masses s(n) are geometric on the lengths under consideration. -/
def modelCost (B : Nat) (s : Nat → Nat) (n : Nat) := prefixSum s n + B*s n

private theorem model_step {s : Nat → Nat} {B den q j : Nat} (hq : q ≤ den)
    (step : den*s (j+1) = (den-q)*s j) :
    den*modelCost B s (j+1) + B*q*s j = den*modelCost B s j + den*s j := by
  have partition : den*s (j+1) + q*s j = den*s j := by
    rw [step, ← Nat.add_mul, Nat.sub_add_cancel hq]
  have scaled := congrArg (B*·) partition
  simp only [Nat.mul_add] at scaled
  simp only [modelCost,prefixSum,Nat.mul_add]
  rw [Nat.mul_comm den (B*s (j+1)), Nat.mul_comm den (B*s j)]
  simp only [Nat.mul_assoc] at scaled ⊢
  rw [Nat.mul_comm (s (j+1)) den, Nat.mul_comm (s j) den]
  omega

/-- The endpoint policy optimizes the entire finite independent curve,
including immediate fallback and the tie Bq=den. -/
theorem independent_cutoff {s : Nat → Nat} {B den q m : Nat} (pos : 0 < den) (hq : q ≤ den)
    (geometric : ∀ j < m, den*s (j+1) = (den-q)*s j) (n : Nat) (hn : n ≤ m) :
    modelCost B s (if den < B*q then m else 0) ≤ modelCost B s n := by
  by_cases active : den < B*q
  · simp only [active, ↓reduceIte]
    have dec (j : Nat) (hj : j < m) : modelCost B s (j+1) ≤ modelCost B s j := by
      have a := model_step (B:=B) hq (geometric j hj)
      have b := Nat.mul_le_mul_right (s j) (Nat.le_of_lt active)
      exact Nat.le_of_mul_le_mul_left (by omega) pos
    have chain (d : Nat) (hd : n+d ≤ m) : modelCost B s (n+d) ≤ modelCost B s n := by
      induction d with
      | zero => exact Nat.le_refl _
      | succ d ih => exact Nat.le_trans (dec (n+d) (by omega)) (ih (by omega))
    simpa [Nat.add_sub_of_le hn] using chain (m-n) (by omega)
  · simp only [active, ↓reduceIte]
    have inc (j : Nat) (hj : j < m) : modelCost B s j ≤ modelCost B s (j+1) := by
      have a := model_step (B:=B) hq (geometric j hj)
      have b := Nat.mul_le_mul_right (s j) (Nat.le_of_not_gt active)
      exact Nat.le_of_mul_le_mul_left (by omega) pos
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih => exact Nat.le_trans (ih (by omega)) (inc n (by omega))

private theorem projected_prefixes (order : List T) (s : Nat → Nat) :
    total (properPrefixes order) (fun xs => s xs.length) = prefixSum s order.length := by
  unfold total properPrefixes
  simp only [List.map_map, Function.comp_def,List.length_take]
  have collapse (n : Nat) :
      ((List.range n).map (fun k => s (min k n))).sum = prefixSum s n := by
    have flat := List.map_congr_left (l:=List.range n)
      (f:=fun k => s (min k n)) (g:=s)
      (fun k hk => congrArg s (Nat.min_eq_left (Nat.le_of_lt (List.mem_range.mp hk))))
    rw [flat]
    clear flat
    induction n with
    | zero => rfl
    | succ n ih =>
      have snoc (xs : List Nat) (v : Nat) : (xs++[v]).sum = xs.sum+v := by
        induction xs with
        | nil => simp
        | cons i xs tail => simp [tail,Nat.add_assoc]
      simp [List.range_succ,prefixSum,snoc,ih]
  exact collapse _

private theorem sum_scaled_le (xs : List T) (f g : T → Nat) (c d : Nat)
    (h : ∀ i ∈ xs, c*f i ≤ d*g i) : c*total xs f ≤ d*total xs g := by
  induction xs with
  | nil => simp [total]
  | cons i xs ih =>
    have head := h i (by simp)
    have tail := ih (fun j hj => h j (by simp [hj]))
    change c*(f i+total xs f) ≤ d*(g i+total xs g)
    simpa [Nat.mul_add] using Nat.add_le_add head tail

private theorem cost_scaled (order : List T) (f g : List T → Nat) (c d B : Nat)
    (pre : ∀ xs ∈ properPrefixes order, c*f xs ≤ d*g xs) (last : c*f order ≤ d*g order) :
    c*(total (properPrefixes order) f+B*f order) ≤
      d*(total (properPrefixes order) g+B*g order) := by
  have a := sum_scaled_le _ f g c d pre
  have b := Nat.mul_le_mul_left B last
  simpa only [Nat.mul_add,Nat.mul_left_comm B c,Nat.mul_left_comm B d] using Nat.add_le_add a b

/-- Turn a common first-order sandwich into a relative comparison. For
example u and v can be actual and independent survival counts; both
survival counts plus the singleton sum k lie in [Z,Z+E]. -/
theorem prefix_ratio {Z E k u v : Nat} (sparse : 2*k ≤ Z)
    (actual : Z ≤ u+k ∧ u+k ≤ Z+E) (model : Z ≤ v+k ∧ v+k ≤ Z+E) :
    Z*u ≤ (Z+2*E)*v := by
  have le : u ≤ v+E := by omega
  have floor : Z ≤ 2*v := by omega
  calc
    Z*u ≤ Z*(v+E) := Nat.mul_le_mul_left _ le
    _ = Z*v+Z*E := Nat.mul_add ..
    _ ≤ Z*v+(2*v)*E := Nat.add_le_add_left (Nat.mul_le_mul_right _ floor) _
    _ = _ := by rw [Nat.add_mul]; ac_rfl

/-- Finite transfer to the *actual* expected scan cost, uniformly in B.
The supplied prefix intervals are the two-term Bonferroni bounds; E is a
common bound for the total pair mass on a prefix. The ratio is at most
(1+2E/Z)^2. Actual and ideal masses use the same grid; q/den is the
common hit probability. Either selected list is compared to any competitor. -/
theorem relative_cutoff_transfer (law : List (X × Nat)) (hit : X → T → Bool)
    (chosen other : List T) (s : Nat → Nat) (B den q m Z E single : Nat)
    (pos : 0 < den) (hq : q ≤ den)
    (geometric : ∀ j < m, den*s (j+1) = (den-q)*s j)
    (endpoint : chosen.length = if den < B*q then m else 0)
    (lengthOther : other.length ≤ m)
    (bounds : ∀ order, order = chosen ∨ order = other → ∀ xs,
      xs ∈ properPrefixes order ∨ xs = order →
      let k := xs.length*single
      2*k ≤ Z ∧
        (Z ≤ survivalMass law hit xs+k ∧ survivalMass law hit xs+k ≤ Z+E) ∧
        (Z ≤ s xs.length+k ∧ s xs.length+k ≤ Z+E)) :
    (Z*Z)*populationCost law hit B chosen ≤
      ((Z+2*E)*(Z+2*E))*populationCost law hit B other := by
  let actual := survivalMass law hit
  let ideal := fun xs : List T => s xs.length
  have left (xs : List T) (hx : xs ∈ properPrefixes chosen ∨ xs = chosen) :
      Z*actual xs ≤ (Z+2*E)*ideal xs := by
    obtain ⟨small,first,second⟩ := bounds chosen (.inl rfl) xs hx
    exact prefix_ratio small first second
  have right (xs : List T) (hx : xs ∈ properPrefixes other ∨ xs = other) :
      Z*ideal xs ≤ (Z+2*E)*actual xs := by
    obtain ⟨small,first,second⟩ := bounds other (.inr rfl) xs hx
    exact prefix_ratio small second first
  have x := cost_scaled chosen actual ideal Z (Z+2*E) B
    (fun a h => left a (.inl h)) (left chosen (.inr rfl))
  have y := cost_scaled other ideal actual Z (Z+2*E) B
    (fun a h => right a (.inl h)) (right other (.inr rfl))
  have opt := independent_cutoff (B:=B) pos hq geometric other.length lengthOther
  rw [← endpoint] at opt
  simp only [actual,ideal,projected_prefixes,←populationCost_eq_prefix_survivals] at x y
  calc
    _ = Z*(Z*populationCost law hit B chosen) := by ac_rfl
    _ ≤ Z*((Z+2*E)*modelCost B s chosen.length) := Nat.mul_le_mul_left _ x
    _ ≤ Z*((Z+2*E)*modelCost B s other.length) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ opt)
    _ = (Z+2*E)*(Z*modelCost B s other.length) := by ac_rfl
    _ ≤ (Z+2*E)*((Z+2*E)*populationCost law hit B other) := Nat.mul_le_mul_left _ y
    _ = _ := by ac_rfl

end Screening.PositiveCutoff

/- Source module: Audit -/

/-! Build-time audit of the transitive dependencies of every project theorem.
The names are read from the environment rather than a hand-maintained sample. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  let mut checked := 0
  let mut used : List Name := []
  for (name, decl) in env.constants.toList do
    if (`Screening).isPrefixOf (privateToUserName name) then
      match decl with
      | .axiomInfo _ => throwError "Project axiom: {name}"
      | .thmInfo _ =>
        checked := checked + 1
        for dep in ← collectAxioms name do
          unless allowed.contains dep do
            throwError "Unexpected axiom in {name}: {dep}"
          unless used.contains dep do used := dep :: used
      | _ => pure ()
  unless checked > 0 do throwError "No project theorems found"
  logInfo m!"Audited {checked} theorem declarations (including auxiliary declarations). Axioms used: {used}"
