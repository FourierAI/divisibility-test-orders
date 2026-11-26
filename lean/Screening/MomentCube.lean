import Std

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
