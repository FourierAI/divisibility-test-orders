import Screening.GlobalOneHit

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
