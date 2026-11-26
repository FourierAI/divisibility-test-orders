import Screening.IntervalCounts
import Screening.ScreeningCost

/-! Finite arithmetic behind the relative-cost proposition on positive odd
inputs. Physical probabilities are represented by integer weights and a common
normalizing constant. All bounds below are homogeneous in the weights. -/
namespace Screening.PositiveCutoff

open Screening.IntervalCounts

/-- If an odd modulus hits, it is no larger than the largest positive word.
The one-residue count consequently gives uniform hit probability at most 5/v,
including the case of no hits. -/
theorem modulus_hits_bound (a L v : Nat) (odd : v%2 = 1)
    (cap : ∀ k < L, word a k ≤ 4*L) :
    hitCount a v L * v ≤ 5*L := by
  by_cases zero : hitCount a v L = 0
  · simp [zero]
  have positive : 0 < hitCount a v L := by omega
  obtain ⟨k,mem,hk⟩ := List.countP_pos_iff.mp positive
  have divides : v ∣ word a k := by simpa using hk
  have vle := Nat.le_of_dvd (show 0 < word a k by simp [word]) divides
  have wle := cap k (List.mem_range.mp mem)
  have err := count_error odd a L
  omega

/-- The corresponding bound for *literal simultaneous* proper-prime tests.
Properness need not be assumed for this upper bound. -/
theorem pair_count_bound {a L p r : Nat} (pp : IsPrime p) (rp : IsPrime r)
    (different : p ≠ r) (op : p%2 = 1) (orr : r%2 = 1)
    (cap : ∀ k < L, word a k ≤ 4*L) :
    containmentCount a L [p,r] * (p*r) ≤ 5*L := by
  have unique : [p,r].Nodup := by simp [different]
  have primes : ∀ j ∈ [p,r], IsPrime j := by simpa using And.intro pp rp
  have odd : ∀ j ∈ [p,r], j%2 = 1 := by simpa using And.intro op orr
  rw [containment_eq a L [p,r] unique primes]
  simpa [product] using modulus_hits_bound a L (product [p,r]) (odd_product _ odd) cap

def eventWeight (ks : List Nat) (weight : Nat → Nat) (event : Nat → Bool) : Nat :=
  (ks.map (fun k => if event k then weight k else 0)).sum

private theorem weight_band (ks : List Nat) (weight : Nat → Nat) (event : Nat → Bool)
    (lo hi : Nat) (band : ∀ k ∈ ks, lo ≤ weight k ∧ weight k ≤ hi) :
    lo * ks.countP event ≤ eventWeight ks weight event ∧
    eventWeight ks weight event ≤ hi * ks.countP event := by
  induction ks with
  | nil => simp [eventWeight]
  | cons k ks ih =>
    have hk := band k (by simp)
    have rest := ih (fun i hi => band i (by simp [hi]))
    cases he : event k <;>
      simp [eventWeight,he,List.countP_cons,Nat.mul_add] at rest ⊢ <;> omega

def marginal (a L p : Nat) (w : Nat → Nat) :=
  eventWeight (List.range L) w (fun k => decide (p ∣ word a k))
def pairMass (a L p r : Nat) (w : Nat → Nat) :=
  eventWeight (List.range L) w (fun k => [p,r].all (fun j => decide (j ∣ word a k)))
def mass (L : Nat) (w : Nat → Nat) := eventWeight (List.range L) w (fun _ => true)

private theorem marginal_lower {a L p lo hi : Nat} (w : Nat → Nat) (op : p%2 = 1)
    (band : ∀ k < L, lo ≤ w k ∧ w k ≤ hi) (pos : 0 < marginal a L p w) :
    L*lo ≤ marginal a L p w*(2*p) := by
  have wb := weight_band (List.range L) w (fun k => decide (p ∣ word a k)) lo hi
    (fun k hk => band k (List.mem_range.mp hk))
  change lo * hitCount a p L ≤ marginal a L p w ∧ marginal a L p w ≤ hi * hitCount a p L at wb
  have cnt : hitCount a p L ≠ 0 := by
    intro h
    simp [h] at wb
    omega
  have cntpos : 1 ≤ hitCount a p L := by omega
  have pp := Nat.mul_le_mul_right p cntpos
  have err := count_error op a L
  have lower : L ≤ 2*(hitCount a p L*p) := by simp only [Nat.one_mul] at pp; omega
  calc
    L*lo ≤ (2*(hitCount a p L*p))*lo := Nat.mul_le_mul_right _ lower
    _ = (lo*hitCount a p L)*(2*p) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ wb.1

/-- For two distinct primes with positive hit probabilities, under a rational
word law with per-word weights in [lo,hi], this says
Pr[both] ≤ 20 (hi/lo)^2 Pr[p hits] Pr[r hits] (lo>0).
In particular equal marginals q give a uniform quadratic pair bound. -/
theorem pair_probability_bound {a L p r lo hi : Nat} (w : Nat → Nat)
    (pp : IsPrime p) (rp : IsPrime r) (different : p ≠ r)
    (op : p%2 = 1) (orr : r%2 = 1) (cap : ∀ k < L, word a k ≤ 4*L)
    (band : ∀ k < L, lo ≤ w k ∧ w k ≤ hi)
    (hp : 0 < marginal a L p w) (hr : 0 < marginal a L r w) :
    pairMass a L p r w * mass L w * (lo*lo) ≤
      20*(hi*hi)*(marginal a L p w * marginal a L r w) := by
  have kw := fun k hk => band k (List.mem_range.mp hk)
  have wm := (weight_band (List.range L) w (fun _ => true) lo hi kw).2
  have zbound : mass L w ≤ hi*L := by simpa [mass] using wm
  let cnt := containmentCount a L [p,r]
  have pairbound : pairMass a L p r w ≤ hi*cnt :=
    (weight_band (List.range L) w _ lo hi kw).2
  have capbound : cnt * (p*r) ≤ 5*L := pair_count_bound pp rp different op orr cap
  have psmall := marginal_lower w op band hp
  have rsmall := marginal_lower w orr band hr
  have pq : 0 < p*r := Nat.mul_pos (by have := pp.1; omega) (by have := rp.1; omega)
  apply Nat.le_of_mul_le_mul_right (c := p*r) ?_ pq
  calc
    _ ≤ ((hi*cnt)*(hi*L)*(lo*lo))*(p*r) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul pairbound zbound))
    _ = (hi*hi)*(cnt*(p*r))*(L*(lo*lo)) := by ac_rfl
    _ ≤ (hi*hi)*(5*L)*(L*(lo*lo)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ capbound)
    _ = (5*(hi*hi))*((L*lo)*(L*lo)) := by ac_rfl
    _ ≤ (5*(hi*hi))*((marginal a L p w*(2*p))*(marginal a L r w*(2*r))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul psmall rsmall)
    _ = _ := by
      change _ = ((5*(2*2))*(hi*hi)*(marginal a L p w*marginal a L r w))*(p*r)
      ac_rfl

open Screening.ScreeningCost

/-- Number of unordered pairs of distinct test positions hit on this word. -/
def simultaneousPairs (f : T → Bool) : List T → Nat
  | [] => 0
  | i::xs => (if f i then xs.countP f else 0) + simultaneousPairs f xs

private theorem bonferroni_word (f : T → Bool) (xs : List T) :
    1 ≤ (survives f xs).toNat + xs.countP f ∧
      (survives f xs).toNat + xs.countP f ≤ 1 + simultaneousPairs f xs := by
  induction xs with
  | nil => simp [survives,simultaneousPairs]
  | cons i xs tail =>
    cases hi : f i <;>
      simp [survives,hi,List.countP_cons,simultaneousPairs] at tail ⊢ <;> omega

/-- Two-term Bonferroni for a finite input law. The middle term is the
survival mass plus the sum of the actual hit counts, with no independence
assumption or cap on simultaneous hits. -/
theorem bonferroni_population (law : List (X × Nat)) (hit : X → T → Bool) (xs : List T) :
    let Z := weighted law (fun _ => 1)
    let singles := weighted law (fun x => xs.countP (hit x))
    let pairs := weighted law (fun x => simultaneousPairs (hit x) xs)
    Z ≤ survivalMass law hit xs + singles ∧
      survivalMass law hit xs + singles ≤ Z + pairs := by
  dsimp only
  induction law with
  | nil => simp [weighted,survivalMass,total]
  | cons a law ih =>
    have wordBound := bonferroni_word (hit a.1) xs
    have lo := Nat.mul_le_mul_left a.2 wordBound.1
    have hi := Nat.mul_le_mul_left a.2 wordBound.2
    simp only [Nat.mul_add,Nat.mul_one] at lo hi
    simp only [survivalMass,weighted,total,List.map_cons,List.sum_cons,Nat.mul_one] at ih ⊢
    omega

private def prefixSum (s : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => prefixSum s n + s n

/-- Expected independent-model cost, scaled by its common grid denominator.
The survival masses s(n) are geometric on the lengths under consideration. -/
def modelCost (B : Nat) (s : Nat → Nat) (n : Nat) := prefixSum s n + B*s n

private theorem model_step {s : Nat → Nat} {B den q j : Nat} (hq : q ≤ den)
    (step : den*s (j+1) = (den-q)*s j) :
    den*modelCost B s (j+1) + B*q*s j = den*modelCost B s j + den*s j := by
  have partition : den*s (j+1) + q*s j = den*s j := by
    rw [step, ← Nat.add_mul, Nat.sub_add_cancel hq]
  have scaled := congrArg (B*·) partition
  simp only [Nat.mul_add] at scaled
  simp only [modelCost,prefixSum,Nat.mul_add]
  rw [Nat.mul_comm den (B*s (j+1)), Nat.mul_comm den (B*s j)]
  simp only [Nat.mul_assoc] at scaled ⊢
  rw [Nat.mul_comm (s (j+1)) den, Nat.mul_comm (s j) den]
  omega

/-- The endpoint policy optimizes the entire finite independent curve,
including immediate fallback and the tie Bq=den. -/
theorem independent_cutoff {s : Nat → Nat} {B den q m : Nat} (pos : 0 < den) (hq : q ≤ den)
    (geometric : ∀ j < m, den*s (j+1) = (den-q)*s j) (n : Nat) (hn : n ≤ m) :
    modelCost B s (if den < B*q then m else 0) ≤ modelCost B s n := by
  by_cases active : den < B*q
  · simp only [active, ↓reduceIte]
    have dec (j : Nat) (hj : j < m) : modelCost B s (j+1) ≤ modelCost B s j := by
      have a := model_step (B:=B) hq (geometric j hj)
      have b := Nat.mul_le_mul_right (s j) (Nat.le_of_lt active)
      exact Nat.le_of_mul_le_mul_left (by omega) pos
    have chain (d : Nat) (hd : n+d ≤ m) : modelCost B s (n+d) ≤ modelCost B s n := by
      induction d with
      | zero => exact Nat.le_refl _
      | succ d ih => exact Nat.le_trans (dec (n+d) (by omega)) (ih (by omega))
    simpa [Nat.add_sub_of_le hn] using chain (m-n) (by omega)
  · simp only [active, ↓reduceIte]
    have inc (j : Nat) (hj : j < m) : modelCost B s j ≤ modelCost B s (j+1) := by
      have a := model_step (B:=B) hq (geometric j hj)
      have b := Nat.mul_le_mul_right (s j) (Nat.le_of_not_gt active)
      exact Nat.le_of_mul_le_mul_left (by omega) pos
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih => exact Nat.le_trans (ih (by omega)) (inc n (by omega))

private theorem projected_prefixes (order : List T) (s : Nat → Nat) :
    total (properPrefixes order) (fun xs => s xs.length) = prefixSum s order.length := by
  unfold total properPrefixes
  simp only [List.map_map, Function.comp_def,List.length_take]
  have collapse (n : Nat) :
      ((List.range n).map (fun k => s (min k n))).sum = prefixSum s n := by
    have flat := List.map_congr_left (l:=List.range n)
      (f:=fun k => s (min k n)) (g:=s)
      (fun k hk => congrArg s (Nat.min_eq_left (Nat.le_of_lt (List.mem_range.mp hk))))
    rw [flat]
    clear flat
    induction n with
    | zero => rfl
    | succ n ih =>
      have snoc (xs : List Nat) (v : Nat) : (xs++[v]).sum = xs.sum+v := by
        induction xs with
        | nil => simp
        | cons i xs tail => simp [tail,Nat.add_assoc]
      simp [List.range_succ,prefixSum,snoc,ih]
  exact collapse _

private theorem sum_scaled_le (xs : List T) (f g : T → Nat) (c d : Nat)
    (h : ∀ i ∈ xs, c*f i ≤ d*g i) : c*total xs f ≤ d*total xs g := by
  induction xs with
  | nil => simp [total]
  | cons i xs ih =>
    have head := h i (by simp)
    have tail := ih (fun j hj => h j (by simp [hj]))
    change c*(f i+total xs f) ≤ d*(g i+total xs g)
    simpa [Nat.mul_add] using Nat.add_le_add head tail

private theorem cost_scaled (order : List T) (f g : List T → Nat) (c d B : Nat)
    (pre : ∀ xs ∈ properPrefixes order, c*f xs ≤ d*g xs) (last : c*f order ≤ d*g order) :
    c*(total (properPrefixes order) f+B*f order) ≤
      d*(total (properPrefixes order) g+B*g order) := by
  have a := sum_scaled_le _ f g c d pre
  have b := Nat.mul_le_mul_left B last
  simpa only [Nat.mul_add,Nat.mul_left_comm B c,Nat.mul_left_comm B d] using Nat.add_le_add a b

/-- Turn a common first-order sandwich into a relative comparison. For
example u and v can be actual and independent survival counts; both
survival counts plus the singleton sum k lie in [Z,Z+E]. -/
theorem prefix_ratio {Z E k u v : Nat} (sparse : 2*k ≤ Z)
    (actual : Z ≤ u+k ∧ u+k ≤ Z+E) (model : Z ≤ v+k ∧ v+k ≤ Z+E) :
    Z*u ≤ (Z+2*E)*v := by
  have le : u ≤ v+E := by omega
  have floor : Z ≤ 2*v := by omega
  calc
    Z*u ≤ Z*(v+E) := Nat.mul_le_mul_left _ le
    _ = Z*v+Z*E := Nat.mul_add ..
    _ ≤ Z*v+(2*v)*E := Nat.add_le_add_left (Nat.mul_le_mul_right _ floor) _
    _ = _ := by rw [Nat.add_mul]; ac_rfl

/-- Finite transfer to the *actual* expected scan cost, uniformly in B.
The supplied prefix intervals are the two-term Bonferroni bounds; E is a
common bound for the total pair mass on a prefix. The ratio is at most
(1+2E/Z)^2. Actual and ideal masses use the same grid; q/den is the
common hit probability. Either selected list is compared to any competitor. -/
theorem relative_cutoff_transfer (law : List (X × Nat)) (hit : X → T → Bool)
    (chosen other : List T) (s : Nat → Nat) (B den q m Z E single : Nat)
    (pos : 0 < den) (hq : q ≤ den)
    (geometric : ∀ j < m, den*s (j+1) = (den-q)*s j)
    (endpoint : chosen.length = if den < B*q then m else 0)
    (lengthOther : other.length ≤ m)
    (bounds : ∀ order, order = chosen ∨ order = other → ∀ xs,
      xs ∈ properPrefixes order ∨ xs = order →
      let k := xs.length*single
      2*k ≤ Z ∧
        (Z ≤ survivalMass law hit xs+k ∧ survivalMass law hit xs+k ≤ Z+E) ∧
        (Z ≤ s xs.length+k ∧ s xs.length+k ≤ Z+E)) :
    (Z*Z)*populationCost law hit B chosen ≤
      ((Z+2*E)*(Z+2*E))*populationCost law hit B other := by
  let actual := survivalMass law hit
  let ideal := fun xs : List T => s xs.length
  have left (xs : List T) (hx : xs ∈ properPrefixes chosen ∨ xs = chosen) :
      Z*actual xs ≤ (Z+2*E)*ideal xs := by
    obtain ⟨small,first,second⟩ := bounds chosen (.inl rfl) xs hx
    exact prefix_ratio small first second
  have right (xs : List T) (hx : xs ∈ properPrefixes other ∨ xs = other) :
      Z*ideal xs ≤ (Z+2*E)*actual xs := by
    obtain ⟨small,first,second⟩ := bounds other (.inr rfl) xs hx
    exact prefix_ratio small second first
  have x := cost_scaled chosen actual ideal Z (Z+2*E) B
    (fun a h => left a (.inl h)) (left chosen (.inr rfl))
  have y := cost_scaled other ideal actual Z (Z+2*E) B
    (fun a h => right a (.inl h)) (right other (.inr rfl))
  have opt := independent_cutoff (B:=B) pos hq geometric other.length lengthOther
  rw [← endpoint] at opt
  simp only [actual,ideal,projected_prefixes,←populationCost_eq_prefix_survivals] at x y
  calc
    _ = Z*(Z*populationCost law hit B chosen) := by ac_rfl
    _ ≤ Z*((Z+2*E)*modelCost B s chosen.length) := Nat.mul_le_mul_left _ x
    _ ≤ Z*((Z+2*E)*modelCost B s other.length) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ opt)
    _ = (Z+2*E)*(Z*modelCost B s other.length) := by ac_rfl
    _ ≤ (Z+2*E)*((Z+2*E)*populationCost law hit B other) := Nat.mul_le_mul_left _ y
    _ = _ := by ac_rfl

end Screening.PositiveCutoff
