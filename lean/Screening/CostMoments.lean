import Screening.LargestHits
import Screening.ScreeningCost
import Screening.ClusterCount

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
