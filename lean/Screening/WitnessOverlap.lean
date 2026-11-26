import Std

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
