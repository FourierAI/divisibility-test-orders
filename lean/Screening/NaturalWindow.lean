import Screening.CostMoments
import Screening.IntervalCounts

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
