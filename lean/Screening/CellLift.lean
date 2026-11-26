import Std

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
