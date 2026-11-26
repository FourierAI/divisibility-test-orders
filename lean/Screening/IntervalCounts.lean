import Std

/-! Counting literal divisible words among L consecutive odd integers. -/
namespace Screening.IntervalCounts

def word (a k : Nat) := 2*(a+k)+1

def hitCount (a q L : Nat) : Nat :=
  (List.range L).countP (fun k => decide (q ∣ word a k))

/-- The literal congruence is a single residue class of the odd-word index;
the shift q/2+1 is determined by q. -/
theorem odd_index_congruence {q : Nat} (hodd : q%2 = 1) (u : Nat) :
    q ∣ 2*u+1 ↔ q ∣ u+q/2+1 := by
  have hg : q.gcd 2 = 1 := by rw [Nat.gcd_comm q 2, Nat.gcd_rec, hodd]; decide
  have heq : 2*(u+q/2+1) = (2*u+1)+q := by omega
  calc q ∣ 2*u+1 ↔ q ∣ (2*u+1)+q := Nat.dvd_add_iff_left (Nat.dvd_refl q)
       _ ↔ q ∣ 2*(u+q/2+1) := by rw [heq]
       _ ↔ q ∣ u+q/2+1 := by
          simpa [hg] using (Nat.dvd_gcd_mul_iff_dvd_mul (k:=q) (n:=2) (m:=u+q/2+1)).symm

/-- Exact prefix difference in a form that avoids truncated subtraction. -/
theorem prefix_identity {q : Nat} (hodd : q%2 = 1) (a L : Nat) :
    (a+q/2)/q + hitCount a q L = (a+q/2+L)/q := by
  induction L with
  | zero => simp [hitCount]
  | succ L ih =>
    have step : hitCount a q (L+1) =
        hitCount a q L + (if q ∣ a+q/2+L+1 then 1 else 0) := by
      simp only [hitCount, List.range_succ, List.countP_append, List.countP_singleton,
        decide_eq_true_eq]
      have h := odd_index_congruence hodd (a+L)
      simp only [word, Nat.add_right_comm a L (q/2), h]
    rw [step, ← Nat.add_assoc, ih]
    simpa only [Nat.add_assoc] using (Nat.succ_div (a:=a+q/2+L) (b:=q)).symm

theorem exact_hit_count {q : Nat} (hodd : q%2 = 1) (a L : Nat) :
    hitCount a q L = (a+q/2+L)/q - (a+q/2)/q := by
  have := prefix_identity hodd a L
  omega

/-- Ceiling of L/q for positive q, including the exact multiple case. -/
def ceilingQuotient (L q : Nat) := L/q + if L%q = 0 then 0 else 1

theorem floor_or_ceiling {q : Nat} (hodd : q%2 = 1) (a L : Nat) :
    hitCount a q L = L/q ∨ hitCount a q L = ceilingQuotient L q := by
  have hq : 0 < q := by omega
  have h := prefix_identity hodd a L
  rw [Nat.add_div (a:=a+q/2) (b:=L) hq] at h
  have hmod := Nat.mod_lt (a+q/2) hq
  unfold ceilingQuotient
  split at h <;> split <;> omega

/-- Fractions need not be in lowest terms. At positive denominators these
are the ordinary absolute difference and strict comparison of fractions. -/
structure Fraction where
  num : Nat
  den : Nat

def Fraction.absDifference (x y : Fraction) : Fraction :=
  ⟨max (x.num*y.den - y.num*x.den) (y.num*x.den - x.num*y.den), x.den*y.den⟩

def Fraction.less (x y : Fraction) := x.num*y.den < y.num*x.den

theorem count_error {q : Nat} (hodd : q%2 = 1) (a L : Nat) :
    max (hitCount a q L*q-L) (L-hitCount a q L*q) < q := by
  have hq : 0 < q := by omega
  have remainder := Nat.div_add_mod L q
  rw [Nat.mul_comm q] at remainder
  have small := Nat.mod_lt L hq
  rcases floor_or_ceiling hodd a L with h|h
  · rw [h]; omega
  · rw [h]; unfold ceilingQuotient
    split <;> simp only [Nat.add_zero, Nat.add_mul, Nat.one_mul] <;> omega

/-- For L>0 this is |hitCount/L − 1/q| < 1/L, using cross multiplication
over natural numbers, with positive denominators. -/
theorem normalized_probability_error {q L : Nat} (hodd : q%2 = 1) (hL : 0 < L) (a : Nat) :
    (Fraction.absDifference ⟨hitCount a q L,L⟩ ⟨1,q⟩).less ⟨1,L⟩ := by
  have result := Nat.mul_lt_mul_of_pos_right (count_error hodd a L) hL
  simpa only [Fraction.less, Fraction.absDifference, Nat.one_mul, Nat.mul_comm q L] using result

def product : List Nat → Nat
  | [] => 1
  | p :: ps => p * product ps

/-- Elementary divisor definition of primality, using only the standard library. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

private theorem prime_gcd {p r : Nat} (hp : IsPrime p) (hr : IsPrime r) (hne : p ≠ r) :
    p.gcd r = 1 := by
  rcases hp.2 _ (Nat.gcd_dvd_left p r) with done | heq
  · exact done
  · have hpr := Nat.gcd_dvd_right p r
    rw [heq] at hpr
    rcases hr.2 p hpr with h | h
    · have := hp.1; omega
    · exact False.elim (hne h)

private theorem coprime_product (p : Nat) (ps : List Nat)
    (h : ∀ q ∈ ps, p.gcd q = 1) : p.gcd (product ps) = 1 := by
  induction ps with
  | nil => simp [product]
  | cons q qs ih =>
    have hq := h q (by simp)
    have hrest := ih (fun r hr => h r (by simp [hr]))
    apply Nat.eq_one_of_dvd_one
    simpa only [product, hq, hrest, Nat.one_mul] using
      (Nat.gcd_mul_dvd_mul_gcd p q (product qs))

theorem product_dvd_iff (ps : List Nat) (hd : ps.Nodup) (hp : ∀ p ∈ ps, IsPrime p) (n : Nat) :
    product ps ∣ n ↔ ∀ p ∈ ps, p ∣ n := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hd
    have htail := fun q (hq : q ∈ ps) => hp q (by simp [hq])
    have hcop := coprime_product p ps (fun q hq =>
      prime_gcd (hp p (by simp)) (htail q hq) (fun heq => hnot (heq ▸ hq)))
    have hlcm := Nat.gcd_mul_lcm p (product ps)
    rw [hcop,Nat.one_mul] at hlcm
    constructor
    · intro h q hq
      rcases List.mem_cons.mp hq with e | hmem
      · subst q; exact Nat.dvd_trans (Nat.dvd_mul_right p (product ps)) h
      · exact (ih hnodup htail).mp (Nat.dvd_trans (Nat.dvd_mul_left (product ps) p) h) q hmem
    · intro h
      change p * product ps ∣ n
      rw [← hlcm]
      exact Nat.lcm_dvd (h p (by simp)) ((ih hnodup htail).mpr (fun q hq => h q (by simp [hq])))

theorem odd_product (ps : List Nat) (ho : ∀ p ∈ ps, p%2 = 1) : product ps % 2 = 1 := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    rw [product, Nat.mul_mod, ho p (by simp), ih (fun q hq => ho q (by simp [hq]))]

/-- Literal containment count from testing every selected prime separately. -/
def containmentCount (a L : Nat) (ps : List Nat) : Nat :=
  (List.range L).countP (fun k => ps.all (fun p => decide (p ∣ word a k)))

theorem containment_eq (a L : Nat) (ps : List Nat) (hd : ps.Nodup)
    (hp : ∀ p ∈ ps, IsPrime p) : containmentCount a L ps = hitCount a (product ps) L := by
  apply List.countP_congr
  intro k _
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact (product_dvd_iff ps hd hp _).symm

theorem uniform_containment_error {L : Nat} (hL : 0 < L) (a : Nat)
    (ps : List Nat) (hd : ps.Nodup) (hp : ∀ p ∈ ps, IsPrime p) (ho : ∀ p ∈ ps, p%2 = 1) :
    (Fraction.absDifference ⟨containmentCount a L ps,L⟩ ⟨1,product ps⟩).less ⟨1,L⟩ := by
  rw [containment_eq a L ps hd hp]
  exact normalized_probability_error (odd_product ps ho) hL a

private theorem power_le_product (P : Nat) (ps : List Nat) (h : ∀ p ∈ ps, P ≤ p) :
    P^ps.length ≤ product ps := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    have ht := ih (fun q hq => h q (by simp [hq]))
    simp only [List.length_cons, Nat.pow_succ, product, Nat.mul_comm p (product ps)]
    exact Nat.mul_le_mul ht (h p (by simp))

/-- The actual number of hits among distinct menu primes cannot exceed h on
the paper's interval [2L,4L) when 4L < P^(h+1). -/
theorem natural_window_hit_cap {L P h k : Nat} (hk : k < L) (hP : 0 < P)
    (hwindow : 4*L < P^(h+1)) (ps : List Nat) (hd : ps.Nodup)
    (hp : ∀ p ∈ ps, IsPrime p) (hlo : ∀ p ∈ ps, P ≤ p) :
    (ps.filter (fun p => decide (p ∣ word L k))).length ≤ h := by
  let selected := ps.filter (fun p => decide (p ∣ word L k))
  have hm {p} (hs : p ∈ selected) : p ∈ ps ∧ p ∣ word L k := by
    simpa [selected] using hs
  have hprod := (product_dvd_iff selected (List.Pairwise.filter _ hd)
    (fun p hs => hp p (hm hs).1) (word L k)).mpr (fun _ hs => (hm hs).2)
  have hpositive : 0 < word L k := by simp [word]
  have word_lt : word L k < 4*L := by unfold word; omega
  have product_bound := Nat.le_of_dvd hpositive hprod
  have power_bound := power_le_product P selected (fun p hs => hlo p (hm hs).1)
  change selected.length ≤ h
  apply Nat.le_of_not_gt
  intro hmuch
  have hfinal := Nat.pow_le_pow_right hP (show h+1 ≤ selected.length by omega)
  omega

end Screening.IntervalCounts
