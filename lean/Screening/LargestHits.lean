import Std

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
