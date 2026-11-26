import Std

/-!
First-hit costs for unit-price tests. A miss on the entire order incurs a
fallback charge, including when the order is empty. We give the signed
exchange criterion for integer-weighted finite laws and additive identities
for arbitrary finite weights. All identities also hold separately per outcome.
-/

namespace Screening.ScreeningCost

/-- Operational cost of running the scan on a single outcome. -/
def scan (hit : T → Bool) (fallback : Nat) : List T → Nat
  | [] => fallback
  | i :: tail => if hit i then 1 else 1 + scan hit fallback tail

/-- Whether the scan finds no hit amongst the specified tests. -/
def survives (hit : T → Bool) (tests : List T) : Bool :=
  tests.all (fun i => !(hit i))

/-- Prefixes of lengths 0, 1, ..., n-1, one for each attempted-test position. -/
def properPrefixes (tests : List T) : List (List T) :=
  (List.range tests.length).map (fun k => tests.take k)

private theorem properPrefixes_cons (i : T) (tail : List T) :
    properPrefixes (i :: tail) = [] :: (properPrefixes tail).map (i :: ·) := by
  simp [properPrefixes, List.range_succ_eq_map, List.map_map, Function.comp_def]

def total (xs : List A) (f : A → Nat) : Nat := (xs.map f).sum

private theorem total_cons (a : A) (xs : List A) (f : A → Nat) :
    total (a :: xs) f = f a + total xs f := rfl

private theorem total_zero (xs : List A) : total xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [total_cons, ih]

private theorem total_map (xs : List A) (g : A → B) (f : B → Nat) :
    total (xs.map g) f = total xs (fun x => f (g x)) := by
  simp [total, List.map_map, Function.comp_def]

private theorem total_add (xs : List A) (f g : A → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [total_cons, ih]
    omega

/-- A test costs one precisely when its predecessors have all missed. -/
theorem scan_eq_prefix_survivals (hit : T → Bool) (fallback : Nat) (order : List T) :
    scan hit fallback order =
      total (properPrefixes order) (fun pre => (survives hit pre).toNat) +
      fallback * (survives hit order).toNat := by
  induction order with
  | nil => simp [scan, properPrefixes, total, survives]
  | cons i tail ih =>
    rw [properPrefixes_cons, total_cons, total_map]
    cases hc : hit i with
    | true => simp [scan, survives, hc, total_zero]
    | false =>
      simpa [scan, survives, hc, Nat.add_assoc] using ih

/-- On an arbitrary outcome this event is exactly "i hits and all of pre miss." -/
def newHit (hit : T → Bool) (pre : List T) (i : T) : Nat :=
  (survives hit pre && hit i).toNat

/-- Inserting a test anywhere in a prefix partitions the previously surviving
outcomes into survivors and new hits. This applies separately to each changed
prefix of a nonadjacent exchange. -/
theorem inserted_test_partition (hit : T → Bool) (pre middle : List T) (i : T) :
    (survives hit (pre ++ i :: middle)).toNat + newHit hit (pre ++ middle) i =
      (survives hit (pre ++ middle)).toNat := by
  cases hp : survives hit pre <;> cases hm : survives hit middle <;> cases hi : hit i <;>
    simp [newHit, survives, List.all_append] at hp hm ⊢ <;>
    simp_all

/-- Adjacent interchange, expressed in naturals without truncated subtraction. -/
theorem swap_balance (hit : T → Bool) (fallback : Nat) (pre suf : List T) (i j : T) :
    scan hit fallback (pre ++ i :: j :: suf) + newHit hit pre i =
      scan hit fallback (pre ++ j :: i :: suf) + newHit hit pre j := by
  induction pre with
  | nil =>
    cases hi : hit i <;> cases hj : hit j <;>
      simp [scan, newHit, survives, hi, hj]
  | cons k pre ih =>
    cases hk : hit k with
    | true => simp [scan, newHit, survives, hk]
    | false =>
      simpa [scan, newHit, survives, hk, Nat.add_assoc] using ih

/-- Sum over an explicitly weighted finite population, permitting repeats. -/
def weighted (law : List (X × Nat)) (f : X → Nat) : Nat :=
  total law (fun atom => atom.2 * f atom.1)

private theorem weighted_add (law : List (X × Nat)) (f g : X → Nat) :
    weighted law (fun x => f x + g x) = weighted law f + weighted law g := by
  simp only [weighted, Nat.mul_add, total_add]

private theorem weighted_mul (law : List (X × Nat)) (c : Nat) (f : X → Nat) :
    weighted law (fun x => c * f x) = c * weighted law f := by
  induction law with
  | nil => simp [weighted, total]
  | cons atom law ih =>
    change atom.2 * (c * f atom.1) + weighted law (fun x => c * f x) =
      c * (atom.2 * f atom.1 + weighted law f)
    rw [ih, Nat.mul_add, Nat.mul_left_comm atom.2 c]

private theorem weighted_total (law : List (X × Nat)) (ys : List A) (f : X → A → Nat) :
    weighted law (fun x => total ys (f x)) =
      total ys (fun y => weighted law (fun x => f x y)) := by
  induction ys with
  | nil =>
    change total law (fun atom => atom.2 * 0) = 0
    simpa only [Nat.mul_zero] using total_zero law
  | cons y ys ih =>
    simp only [total_cons, weighted_add, ih]

def populationCost (law : List (X × Nat)) (hit : X → T → Bool)
    (fallback : Nat) (order : List T) : Nat :=
  weighted law (fun x => scan (hit x) fallback order)

def survivalMass (law : List (X × Nat)) (hit : X → T → Bool) (pre : List T) : Nat :=
  weighted law (fun x => (survives (hit x) pre).toNat)

def newHitMass (law : List (X × Nat)) (hit : X → T → Bool) (pre : List T) (i : T) : Nat :=
  weighted law (fun x => newHit (hit x) pre i)

/-- Prefixwise replacement identity for the nonadjacent precedence argument.
Here pre and middle contain precisely the tests common to the two prefixes. -/
theorem survival_replacement (law : List (X × Nat)) (hit : X → T → Bool)
    (pre middle : List T) (i j : T) :
    (survivalMass law hit (pre ++ j :: middle) : Int) -
      survivalMass law hit (pre ++ i :: middle) =
      (newHitMass law hit (pre ++ middle) i : Int) - newHitMass law hit (pre ++ middle) j := by
  have part (a : T) := congrArg (weighted law) (funext
    (fun x => inserted_test_partition (hit x) pre middle a))
  have hi := part i
  have hj := part j
  simp only [weighted_add] at hi hj
  unfold survivalMass newHitMass
  omega

/-- Exact finite-population identity, including the fallback on no-hit inputs. -/
theorem populationCost_eq_prefix_survivals (law : List (X × Nat))
    (hit : X → T → Bool) (fallback : Nat) (order : List T) :
    populationCost law hit fallback order =
      total (properPrefixes order) (survivalMass law hit) +
      fallback * survivalMass law hit order := by
  unfold populationCost survivalMass
  simp only [scan_eq_prefix_survivals, weighted_add, weighted_total, weighted_mul]

/-- Saving from exchanging j,i for i,j equals the difference in their
new-hit masses after exactly the same prefix. Arbitrary suffix and fallback. -/
theorem population_adjacent_exchange (law : List (X × Nat)) (hit : X → T → Bool)
    (fallback : Nat) (pre suf : List T) (i j : T) :
    (populationCost law hit fallback (pre ++ j :: i :: suf) : Int) -
      populationCost law hit fallback (pre ++ i :: j :: suf) =
      (newHitMass law hit pre i : Int) - newHitMass law hit pre j := by
  have balance := congrArg (weighted law) (funext
    (fun x => swap_balance (hit x) fallback pre suf i j))
  simp only [weighted_add] at balance
  change populationCost law hit fallback (pre ++ i :: j :: suf) + newHitMass law hit pre i =
    populationCost law hit fallback (pre ++ j :: i :: suf) + newHitMass law hit pre j at balance
  omega

/-- A comparison of the two hazards is necessary and sufficient for the
corresponding strict local improvement. -/
theorem adjacent_strict_iff (law : List (X × Nat)) (hit : X → T → Bool)
    (fallback : Nat) (pre suf : List T) (i j : T) :
    populationCost law hit fallback (pre ++ i :: j :: suf) <
      populationCost law hit fallback (pre ++ j :: i :: suf) ↔
      newHitMass law hit pre j < newHitMass law hit pre i := by
  have h := population_adjacent_exchange law hit fallback pre suf i j
  omega

section ArbitraryWeights

/-! These additive identities also apply to finite laws with irrational
weights. Only addition of weights and multiplication by a natural count are
needed. The instances below are the standard commutative-monoid identities. -/

variable {M : Type} [Add M] [Zero M]
  [Std.Associative (fun a b : M => a + b)]
  [Std.Commutative (fun a b : M => a + b)]
  [Std.LawfulIdentity (fun a b : M => a + b) 0]

def copies (v : M) : Nat → M
  | 0 => 0
  | n + 1 => v + copies v n

def massIntegral (law : List (X × M)) (f : X → Nat) : M :=
  (law.map (fun a => copies a.2 (f a.1))).sum

omit [Std.Commutative (fun a b : M => a + b)] in
private theorem copies_add (v : M) (n k : Nat) :
    copies v (n + k) = copies v n + copies v k := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, copies]
    exact (Std.LawfulLeftIdentity.left_id (op := fun a b : M => a + b) _).symm
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [copies, ih]
    exact (Std.Associative.assoc (op := fun a b : M => a + b) _ _ _).symm

private theorem integral_add (law : List (X × M)) (f g : X → Nat) :
    massIntegral law (fun x => f x + g x) = massIntegral law f + massIntegral law g := by
  induction law with
  | nil =>
    exact (Std.LawfulLeftIdentity.left_id (op := fun a b : M => a + b) 0).symm
  | cons a law ih =>
    change copies a.2 (f a.1 + g a.1) + massIntegral law (fun x => f x + g x) =
      (copies a.2 (f a.1) + massIntegral law f) + (copies a.2 (g a.1) + massIntegral law g)
    rw [copies_add, ih]
    ac_rfl

omit [Std.Associative (fun a b : M => a + b)] [Std.Commutative (fun a b : M => a + b)] in
private theorem integral_zero (law : List (X × M)) :
    massIntegral law (fun _ => 0) = 0 := by
  induction law with
  | nil => rfl
  | cons a law ih =>
    change 0 + massIntegral law (fun _ => 0) = 0
    rw [ih]
    exact Std.LawfulLeftIdentity.left_id (op := fun a b : M => a + b) 0

private theorem integral_scale (law : List (X × M)) (f : X → Nat) (k : Nat) :
    massIntegral law (fun x => k * f x) = copies (massIntegral law f) k := by
  induction k with
  | zero => simpa only [Nat.zero_mul, copies] using integral_zero law
  | succ k ih =>
    simp only [Nat.succ_mul, integral_add, copies, ih]
    exact Std.Commutative.comm (op := fun a b : M => a + b) _ _

private theorem integral_total (law : List (X × M)) (xs : List A) (f : X → A → Nat) :
    massIntegral law (fun x => total xs (f x)) =
      (xs.map (fun i => massIntegral law (fun x => f x i))).sum := by
  induction xs with
  | nil => exact integral_zero law
  | cons i xs ih => simp only [total_cons, integral_add, List.map_cons, List.sum_cons, ih]

theorem any_weights_prefix_cost (law : List (X × M)) (hit : X → T → Bool)
    (fallback : Nat) (order : List T) :
    massIntegral law (fun x => scan (hit x) fallback order) =
      ((properPrefixes order).map (fun pre =>
        massIntegral law (fun x => (survives (hit x) pre).toNat))).sum +
      copies (massIntegral law (fun x => (survives (hit x) order).toNat)) fallback := by
  simp only [scan_eq_prefix_survivals, integral_add, integral_total, integral_scale]

theorem any_weights_adjacent_exchange (law : List (X × M)) (hit : X → T → Bool)
    (fallback : Nat) (pre suf : List T) (i j : T) :
    massIntegral law (fun x => scan (hit x) fallback (pre ++ i :: j :: suf)) +
      massIntegral law (fun x => newHit (hit x) pre i) =
    massIntegral law (fun x => scan (hit x) fallback (pre ++ j :: i :: suf)) +
      massIntegral law (fun x => newHit (hit x) pre j) := by
  have balance := congrArg (massIntegral law) (funext
    (fun x => swap_balance (hit x) fallback pre suf i j))
  simpa only [integral_add] using balance

end ArbitraryWeights

end Screening.ScreeningCost
