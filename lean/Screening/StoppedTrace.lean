import Std

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
