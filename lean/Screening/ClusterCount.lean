import Screening.LargestHits

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
