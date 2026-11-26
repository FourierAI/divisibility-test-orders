import Std

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
