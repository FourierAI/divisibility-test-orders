import Std

/-! Finite iid sampling on rational laws. A list of equiprobable signed
integer tickets represents a distribution, and repetitions represent mass. -/
namespace Screening.SampleVariance

def weightedSum (f : Int → Int) : List Int → Int
  | [] => 0
  | x :: xs => f x + weightedSum f xs

def energy : List Int → Nat
  | [] => 0
  | x :: xs => x.natAbs*x.natAbs + energy xs

private theorem energy_cast (xs : List Int) :
    (energy xs : Int) = weightedSum (fun x => x*x) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [energy, weightedSum, Int.natCast_add, Int.natAbs_mul_self, ih]

private theorem weighted_append (f : Int → Int) (xs ys : List Int) :
    weightedSum f (xs++ys) = weightedSum f xs + weightedSum f ys := by
  induction xs with
  | nil => simp [weightedSum]
  | cons x xs ih => simp only [List.cons_append,weightedSum,ih,Int.add_assoc]

private theorem weighted_add (f g : Int → Int) (xs : List Int) :
    weightedSum (fun x => f x+g x) xs = weightedSum f xs + weightedSum g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [weightedSum,ih]; ac_rfl

private theorem weighted_const (c : Int) (xs : List Int) :
    weightedSum (fun _ => c) xs = (xs.length : Int)*c := by
  induction xs with
  | nil => simp [weightedSum]
  | cons x xs ih =>
    simp only [weightedSum,ih,List.length_cons,Int.natCast_succ,Int.add_mul,Int.one_mul]
    ac_rfl

private theorem weighted_factor (c : Int) (f : Int → Int) (xs : List Int) :
    weightedSum (fun x => c*f x) xs = c*weightedSum f xs := by
  induction xs with
  | nil => simp [weightedSum]
  | cons x xs ih => simp [weightedSum,ih,Int.mul_add]

private theorem weighted_map (f g : Int → Int) (xs : List Int) :
    weightedSum f (xs.map g) = weightedSum (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,weightedSum,ih]

/-- Each pair of tickets is enumerated once. This includes multiplicities,
so indices of identical values remain independent choices. -/
def convolve (xs ys : List Int) : List Int := xs.flatMap (fun x => ys.map (x+·))

def sampleSums (law : List Int) : Nat → List Int
  | 0 => [0]
  | n+1 => convolve (sampleSums law n) law

private theorem convolve_length (xs ys : List Int) :
    (convolve xs ys).length = xs.length*ys.length := by
  induction xs with
  | nil => simp [convolve]
  | cons x xs ih =>
    change ((ys.map (x+·))++convolve xs ys).length = (xs.length+1)*ys.length
    simp [ih,Nat.add_mul,Nat.add_comm]

theorem sample_length (law : List Int) (n : Nat) :
    (sampleSums law n).length = law.length^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sampleSums,convolve_length,ih,Nat.pow_succ]

/-- Integer centering of any ticket law. Division by its positive length
recovers the usual centered observation x − E[X]. -/
def centered (law : List Int) : List Int :=
  law.map (fun x => (law.length : Int)*x - weightedSum id law)

theorem centered_mean_zero (law : List Int) : weightedSum id (centered law) = 0 := by
  have line : weightedSum (fun x => (law.length : Int)*x) law =
      (law.length : Int)*weightedSum id law := weighted_factor _ id _
  simp only [centered,weighted_map,id_eq,Int.sub_eq_add_neg]
  rw [weighted_add,weighted_const,line,Int.mul_neg,Int.add_right_neg]

private theorem convolve_centered_mean (xs law : List Int) (hc : weightedSum id law = 0) :
    weightedSum id (convolve xs law) = (law.length : Int)*weightedSum id xs := by
  induction xs with
  | nil => simp [convolve,weightedSum]
  | cons x xs ih =>
    change weightedSum id (law.map (x+·) ++ convolve xs law) = _
    have shift : weightedSum id (law.map (x+·)) = (law.length : Int)*x := by
      rw [weighted_map]
      change weightedSum (fun y => x + id y) law = _
      rw [weighted_add,weighted_const,hc,Int.add_zero]
    rw [weighted_append,shift,ih]
    simp only [weightedSum,id_eq,Int.mul_add]

theorem iid_mean_zero (law : List Int) (hc : weightedSum id law = 0) (n : Nat) :
    weightedSum id (sampleSums law n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sampleSums,convolve_centered_mean _ _ hc,ih,Int.mul_zero]

/-- The mixed terms in the square sum vanish because the next independent
ticket has mean zero. No zero-mean assumption on the existing partial sums. -/
private theorem shifted_square (s : Int) (law : List Int) (hc : weightedSum id law = 0) :
    weightedSum (fun x => x*x) (law.map (s+·)) =
      (law.length : Int)*(s*s) + weightedSum (fun x => x*x) law := by
  rw [weighted_map]
  have poly : (fun x : Int => (s+x)*(s+x)) =
      (fun x => ((s*s+s*x)+s*x)+x*x) := by
    funext x
    simp only [Int.add_mul,Int.mul_add]
    ac_rfl
  have cross : weightedSum (fun x => s*x) law = 0 := calc
    _ = s*weightedSum id law := weighted_factor s id law
    _ = 0 := by rw [hc,Int.mul_zero]
  rw [poly,weighted_add,weighted_add,weighted_add,weighted_const,cross]
  simp

private theorem convolve_square (xs law : List Int) (hc : weightedSum id law = 0) :
    weightedSum (fun x => x*x) (convolve xs law) =
      (law.length : Int)*weightedSum (fun x => x*x) xs +
      (xs.length : Int)*weightedSum (fun x => x*x) law := by
  induction xs with
  | nil => simp [convolve,weightedSum]
  | cons x xs ih =>
    change weightedSum _ (law.map (x+·) ++ convolve xs law) = _
    rw [weighted_append,shifted_square x law hc,ih]
    simp only [weightedSum,List.length_cons,Int.natCast_succ,Int.add_mul,Int.one_mul,Int.mul_add]
    ac_rfl

private theorem convolve_energy (xs law : List Int) (hc : weightedSum id law = 0) :
    energy (convolve xs law) = law.length*energy xs + xs.length*energy law := by
  have h := convolve_square xs law hc
  rw [← energy_cast, ← energy_cast, ← energy_cast] at h
  omega

/-- After dividing by the positive ticket counts, this gives
E[(X₁+...+Xₙ)²] = n E[X₁²] for a centered law. -/
theorem iid_variance (law : List Int) (hc : weightedSum id law = 0) (n : Nat) :
    law.length*energy (sampleSums law n) = n*(sampleSums law n).length*energy law := by
  induction n with
  | zero => simp [sampleSums,energy]
  | succ n ih =>
    rw [sampleSums,convolve_energy _ law hc,convolve_length]
    rw [Nat.mul_add,ih,Nat.add_mul,Nat.add_mul]
    simp only [Nat.one_mul]
    ac_rfl

/-- For rational threshold a/d, bad tickets are those with
|sum|/n > a/d. The event test below is division-free. -/
def badCount (xs : List Int) (t d : Nat) : Nat :=
  xs.countP (fun s => decide (t < d*s.natAbs))

def goodCount (xs : List Int) (t d : Nat) : Nat :=
  xs.countP (fun s => decide (d*s.natAbs ≤ t))

private theorem sum_square_markov (xs : List Int) (t d : Nat) :
    t*t*badCount xs t d ≤ d*d*energy xs := by
  induction xs with
  | nil => simp [badCount,energy]
  | cons x xs ih =>
    change t*t*(List.countP _ (x::xs)) ≤ d*d*(x.natAbs*x.natAbs+energy xs)
    rw [List.countP_cons, Nat.mul_add, Nat.mul_add]
    change t*t*badCount xs t d + _ ≤ _
    by_cases h : t < d*x.natAbs
    · have hsq := Nat.mul_le_mul (Nat.le_of_lt h) (Nat.le_of_lt h)
      have one : t*t ≤ d*d*(x.natAbs*x.natAbs) := by
        calc t*t ≤ (d*x.natAbs)*(d*x.natAbs) := hsq
             _ = d*d*(x.natAbs*x.natAbs) := by ac_rfl
      simp only [h,decide_true,if_true,Nat.mul_one]
      omega
    · simp only [h,decide_false,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero]
      omega

/-- Chebyshev for an arbitrary finite rational ticket law and N>0:
P(|sample mean|>a/d) ≤ d² E[X²]/(N a²), written by cross multiplication. -/
theorem chebyshev (law : List Int) (hc : weightedSum id law = 0)
    {n : Nat} (hn : 0 < n) (a d : Nat) :
    (law.length*n*a*a)*badCount (sampleSums law n) (n*a) d ≤
      (d*d*energy law)*(sampleSums law n).length := by
  let ys := sampleSums law n
  have hv := iid_variance law hc n
  change law.length*energy ys = n*ys.length*energy law at hv
  have raw := sum_square_markov ys (n*a) d
  apply Nat.le_of_mul_le_mul_left (c:=n) _ hn
  calc n*((law.length*n*a*a)*badCount ys (n*a) d)
        = law.length*((n*a)*(n*a)*badCount ys (n*a) d) := by ac_rfl
       _ ≤ law.length*(d*d*energy ys) := Nat.mul_le_mul_left law.length raw
       _ = d*d*(law.length*energy ys) := by ac_rfl
       _ = d*d*(n*ys.length*energy law) := by rw [hv]
       _ = n*((d*d*energy law)*ys.length) := by ac_rfl

private theorem count_partition (xs : List Int) (t d : Nat) :
    goodCount xs t d + badCount xs t d = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [goodCount,badCount,List.countP_cons,decide_eq_true_eq,List.length_cons] at ih ⊢
    split <;> split <;> omega

/-- Block success probability is at least 3/4 provided
n*(a/d)² ≥ 4 E[X²]. Both sides are exact ticket counts. -/
theorem block_three_quarters (law : List Int) (hc : weightedSum id law = 0)
    {n a d : Nat} (hK : 0 < law.length) (hn : 0 < n) (ha : 0 < a) (_hd : 0 < d)
    (hsize : 4*(d*d*energy law) ≤ law.length*n*a*a) :
    3*(sampleSums law n).length ≤ 4*goodCount (sampleSums law n) (n*a) d := by
  let ys := sampleSums law n
  let c := law.length*n*a*a
  have cpos : 0 < c := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hK hn) ha) ha
  have h := chebyshev law hc hn a d
  have bad : 4*badCount ys (n*a) d ≤ ys.length := by
    apply Nat.le_of_mul_le_mul_left (c:=c) _ cpos
    calc c*(4*badCount ys (n*a) d) = 4*(c*badCount ys (n*a) d) := by ac_rfl
         _ ≤ 4*((d*d*energy law)*ys.length) := Nat.mul_le_mul_left 4 h
         _ = (4*(d*d*energy law))*ys.length := by ac_rfl
         _ ≤ c*ys.length := Nat.mul_le_mul_right _ hsize
  have total := count_partition ys (n*a) d
  change 3*ys.length ≤ 4*goodCount ys (n*a) d
  omega

/-- Specialization to one fixed prefix and the tolerance u/(3m) in
Proposition active-one-hit. For nonintegral u, the generic theorem also
allows arbitrary positive rational threshold a/d. -/
theorem prefix_block (law : List Int) (hc : weightedSum id law = 0)
    {n m u : Nat} (hK : 0 < law.length) (hn : 0 < n) (hm : 0 < m) (hu : 0 < u)
    (hsize : 4*((3*m)*(3*m)*energy law) ≤ law.length*n*u*u) :
    3*(sampleSums law n).length ≤ 4*goodCount (sampleSums law n) (n*u) (3*m) :=
  block_three_quarters law hc hK hn hu (by omega) hsize

/-! Independent repetitions and a union over prefixes on the same data. -/

/-- Every possible ordered sample, retaining repeated tickets. There is no
assumption that different predicates on the same ticket are independent. -/
def iidTuples {α : Type} (law : List α) : Nat → List (List α)
  | 0 => [[]]
  | k+1 => law.flatMap (fun x => (iidTuples law k).map (x::·))

private def mass {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + mass f xs

private theorem mass_append {α : Type} (f : α → Nat) (xs ys : List α) :
    mass f (xs++ys) = mass f xs + mass f ys := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simp [mass,ih,Nat.add_assoc]

private theorem mass_map {α β : Type} (f : β → Nat) (g : α → β) (xs : List α) :
    mass f (xs.map g) = mass (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mass,ih]

private theorem mass_flatMap {α β : Type} (f : β → Nat) (g : α → List β) (xs : List α) :
    mass f (xs.flatMap g) = mass (fun x => mass f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mass,List.flatMap_cons,mass_append,ih]

private theorem mass_factor {α : Type} (f : α → Nat) (c : Nat) (xs : List α) :
    mass (fun x => c*f x) xs = c*mass f xs := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simp [mass,ih,Nat.mul_add]

private theorem mass_right {α : Type} (f : α → Nat) (c : Nat) (xs : List α) :
    mass (fun x => f x*c) xs = mass f xs*c := by
  simpa only [Nat.mul_comm c] using mass_factor f c xs

private def tupleWeight {α : Type} (f : α → Nat) : List α → Nat
  | [] => 1
  | x :: xs => f x * tupleWeight f xs

private theorem product_mass {α : Type} (f : α → Nat) (law : List α) (k : Nat) :
    mass (tupleWeight f) (iidTuples law k) = (mass f law)^k := by
  induction k with
  | zero => simp [iidTuples,mass,tupleWeight]
  | succ k ih =>
    rw [iidTuples,mass_flatMap]
    simp only [mass_map,tupleWeight,mass_factor,ih,mass_right,Nat.pow_succ]
    ac_rfl

private theorem mass_one {α : Type} (xs : List α) :
    mass (fun _ => 1) xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mass,ih,Nat.add_comm]

private theorem ones_tuple {α : Type} (xs : List α) :
    tupleWeight (fun _ => 1) xs = 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [tupleWeight,ih]

theorem iidTuples_length {α : Type} (law : List α) (k : Nat) :
    (iidTuples law k).length = law.length^k := by
  have h := product_mass (fun _ => 1) law k
  have f : tupleWeight (fun _ : α => 1) = fun _ => 1 := funext ones_tuple
  simpa only [f,mass_one] using h

private def tilt {α : Type} (bad : α → Bool) (x : α) := if bad x then 3 else 1

private theorem one_tilt {α : Type} (bad : α → Bool) (law : List α) :
    mass (tilt bad) law = law.length+2*law.countP bad := by
  induction law with
  | nil => rfl
  | cons x xs ih =>
    simp only [mass,tilt,List.countP_cons,List.length_cons,ih]
    cases bad x <;> simp <;> omega

private theorem tuple_tilt {α : Type} (bad : α → Bool) (xs : List α) :
    tupleWeight (tilt bad) xs = 3^(xs.countP bad) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [tupleWeight,tilt,List.countP_cons,ih]
    cases bad x <;> simp [Nat.pow_succ,Nat.mul_comm]

/-- Number of bad-block indicators in a tuple is at least t. -/
def atLeastBad {α : Type} (bad : α → Bool) (t : Nat) (xs : List α) : Bool :=
  decide (t ≤ xs.countP bad)

private theorem tilted_markov {α : Type} (bad : α → Bool) (t : Nat) (rows : List (List α)) :
    3^t*rows.countP (atLeastBad bad t) ≤ mass (tupleWeight (tilt bad)) rows := by
  induction rows with
  | nil => simp [mass]
  | cons x xs ih =>
    simp only [mass,List.countP_cons,atLeastBad,decide_eq_true_eq,Nat.mul_add] at *
    by_cases h : t ≤ x.countP bad
    · have hv := Nat.pow_le_pow_right (n:=3) (by decide) h
      simp only [h,if_true,Nat.mul_one,tuple_tilt]
      omega
    · simp only [h,if_false,Nat.mul_zero,Nat.add_zero]
      omega

/-- The generating function at 3, evaluated on the actual product
enumeration, gives an exponential failure bound. -/
theorem exponential_tail {α : Type} (law : List α) (bad : α → Bool)
    (hb : 4*law.countP bad ≤ law.length) (k t : Nat) :
    (2^k*3^t)*(iidTuples law k).countP (atLeastBad bad t) ≤
      3^k*(iidTuples law k).length := by
  have h := tilted_markov bad t (iidTuples law k)
  rw [product_mass,one_tilt] at h
  rw [iidTuples_length]
  calc (2^k*3^t)*(iidTuples law k).countP (atLeastBad bad t)
          = 2^k*(3^t*(iidTuples law k).countP (atLeastBad bad t)) := Nat.mul_assoc _ _ _
       _ ≤ 2^k*(law.length+2*law.countP bad)^k := Nat.mul_le_mul_left _ h
       _ = (2*(law.length+2*law.countP bad))^k := (Nat.mul_pow _ _ _).symm
       _ ≤ (3*law.length)^k := Nat.pow_le_pow_left (by omega) k
       _ = 3^k*law.length^k := Nat.mul_pow _ _ _

/-- For 2s+1 independent blocks, failure of a strict good majority has
probability at most (1/2)(3/4)^s. -/
theorem majority_amplification {α : Type} (law : List α) (bad : α → Bool)
    (hb : 4*law.countP bad ≤ law.length) (s : Nat) :
    (2*4^s)*(iidTuples law (2*s+1)).countP (atLeastBad bad (s+1)) ≤
      3^s*(iidTuples law (2*s+1)).length := by
  have h := exponential_tail law bad hb (2*s+1) (s+1)
  have h2 : 2^(2*s+1) = 2*4^s := by
    rw [Nat.pow_succ,Nat.pow_mul]
    change 4^s*2 = 2*4^s
    exact Nat.mul_comm _ _
  have h3 : 3^(2*s+1) = 3^(s+1)*3^s := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h2,h3] at h
  apply Nat.le_of_mul_le_mul_left (c:=3^(s+1)) _ (Nat.pow_pos (by decide))
  calc 3^(s+1)*(2*4^s*(iidTuples law (2*s+1)).countP (atLeastBad bad (s+1)))
          = (2*4^s*3^(s+1))*(iidTuples law (2*s+1)).countP (atLeastBad bad (s+1)) := by ac_rfl
       _ ≤ _ := h
       _ = _ := Nat.mul_assoc _ _ _

private theorem count_or_le {α : Type} (f g : α → Bool) (xs : List α) :
    xs.countP (fun x => f x || g x) ≤ xs.countP f + xs.countP g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons]
    cases f x <;> cases g x <;> simp <;> omega

/-- Simultaneous union bound. Every predicate is evaluated on the same
independent block tuple. Correlations among different prefixes are allowed. -/
theorem simultaneous_prefix_bound {α : Type} (law : List α) (prefixes : List (α → Bool))
    (hb : ∀ f ∈ prefixes, 4*law.countP f ≤ law.length) (s : Nat) :
    (2*4^s)*(iidTuples law (2*s+1)).countP
      (fun row => prefixes.any (fun f => atLeastBad f (s+1) row)) ≤
      prefixes.length*(3^s*(iidTuples law (2*s+1)).length) := by
  let rows := iidTuples law (2*s+1)
  induction prefixes with
  | nil => simp
  | cons f fs ih =>
    have hhead := majority_amplification law f (hb f (by simp)) s
    have hrest := ih (fun g hg => hb g (by simp [hg]))
    simp only [List.any_cons,List.length_cons]
    calc 2*4^s*rows.countP (fun row =>
             atLeastBad f (s+1) row || fs.any (fun g => atLeastBad g (s+1) row))
          ≤ 2*4^s*(rows.countP (atLeastBad f (s+1)) +
             rows.countP (fun row => fs.any (fun g => atLeastBad g (s+1) row))) :=
              Nat.mul_le_mul_left _ (count_or_le _ _ _)
         _ ≤ 3^s*rows.length + fs.length*(3^s*rows.length) := by
           rw [Nat.mul_add]
           exact Nat.add_le_add hhead hrest
         _ = (fs.length+1)*(3^s*rows.length) := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]

/-- Concrete composition: Chebyshev on each fresh sample block, followed
by independent majority amplification. -/
theorem block_means_amplified (law : List Int) (hc : weightedSum id law = 0)
    {n a d : Nat} (hK : 0 < law.length) (hn : 0 < n) (ha : 0 < a) (hd : 0 < d)
    (hsize : 4*(d*d*energy law) ≤ law.length*n*a*a) (s : Nat) :
    let blocks := sampleSums law n
    let bad := fun x : Int => decide (n*a < d*x.natAbs)
    (2*4^s)*(iidTuples blocks (2*s+1)).countP (atLeastBad bad (s+1)) ≤
      3^s*(iidTuples blocks (2*s+1)).length := by
  have hg := block_three_quarters law hc hK hn ha hd hsize
  have hp := count_partition (sampleSums law n) (n*a) d
  apply majority_amplification
  change 4*badCount (sampleSums law n) (n*a) d ≤ (sampleSums law n).length
  omega

end Screening.SampleVariance
