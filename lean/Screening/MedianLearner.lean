import Screening.ScreeningCost
import Std

/-! Deterministic steps after joint amplification: select the actual sorted
middle block and minimize the estimated sum over the candidate orders. -/
namespace Screening.MedianLearner

def median (s : Nat) (samples : List Int) : Int :=
  ((samples.mergeSort (fun a b => decide (a ≤ b)))[s]?).getD 0

theorem median_of_majority (samples : List Int) (s : Nat) (lo hi : Int)
    (size : samples.length = 2*s+1)
    (few : samples.countP (fun x => decide (x < lo ∨ hi < x)) ≤ s) :
    lo ≤ median s samples ∧ median s samples ≤ hi := by
  let le := fun a b : Int => decide (a ≤ b)
  let ordered := samples.mergeSort le
  let bad := fun x : Int => decide (x < lo ∨ hi < x)
  have perm := List.mergeSort_perm samples le
  have len : ordered.length = 2*s+1 := perm.length_eq.trans size
  have pos : s < ordered.length := by omega
  have total : ordered.countP bad ≤ s := (List.Perm.countP_eq bad perm) ▸ few
  have sorted : ordered.Pairwise (fun a b => a ≤ b) := by
    have h := List.sorted_mergeSort (le := le)
      (by intro a b c; simp [le]; omega) (by intro a b; simp [le]; omega) samples
    simpa [ordered,le] using h
  have mono (a b : Nat) (ha : a < ordered.length) (hb : b < ordered.length) (hab : a ≤ b) :
      ordered[a] ≤ ordered[b] := by
    by_cases eq : a=b
    · subst b; exact Int.le_refl _
    · exact List.pairwise_iff_getElem.mp sorted a b ha hb (by omega)
  have med : median s samples = ordered[s] := by
    change (ordered[s]?).getD 0 = _
    simp [List.getElem?_eq_getElem pos]
  rw [med]
  constructor
  · apply Int.le_of_not_gt
    intro low
    have nbad : (ordered.take (s+1)).countP bad = (ordered.take (s+1)).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i, h, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [List.getElem_take]
      simp only [List.length_take] at h
      have hle := mono i s (by omega) pos (by omega)
      simp [bad]; omega
    have sub := (List.take_prefix (s+1) ordered).countP_le (p := bad)
    rw [nbad,List.length_take] at sub
    omega
  · apply Int.le_of_not_gt
    intro high
    have nbad : (ordered.drop s).countP bad = (ordered.drop s).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i,h,rfl⟩ := List.mem_iff_getElem.mp hx
      rw [List.getElem_drop]
      simp only [List.length_drop] at h
      have hle := mono s (s+i) pos (by omega) (by omega)
      simp [bad]; omega
    have sub := (List.drop_suffix s ordered).countP_le (p := bad)
    rw [nbad,List.length_drop] at sub
    omega

def best (score : α → Int) (first : α) : List α → α
  | [] => first
  | x :: rest => if score first ≤ score x then best score first rest else best score x rest

theorem best_spec (score : α → Int) (first : α) (rest : List α) :
    best score first rest ∈ first::rest ∧
    ∀ x ∈ first::rest, score (best score first rest) ≤ score x := by
  induction rest generalizing first with
  | nil => simp [best]
  | cons x xs ih =>
    by_cases h : score first ≤ score x
    · rw [best,if_pos h]
      obtain ⟨mem,min⟩ := ih first
      constructor
      · rcases List.mem_cons.mp mem with he | ht
        · simp [he]
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)
      · intro y hy
        rcases (List.mem_cons.mp hy) with rfl|hy
        · exact min _ (by simp)
        rcases (List.mem_cons.mp hy) with rfl|hy
        · exact Int.le_trans (min _ (by simp)) h
        · exact min _ (by simp [hy])
    · rw [best,if_neg h]
      obtain ⟨mem,min⟩ := ih x
      constructor
      · exact List.mem_cons_of_mem _ mem
      · intro y hy
        rcases (List.mem_cons.mp hy) with rfl|hy
        · exact Int.le_trans (min x (by simp)) (by omega)
        · exact min _ hy

theorem selected_regret (score actual : α → Int) (first : α) (rest : List α) (err : Int)
    (uniform : ∀ x ∈ first::rest, actual x - err ≤ score x ∧ score x ≤ actual x + err)
    (competitor : α) (hc : competitor ∈ first::rest) :
    actual (best score first rest) - actual competitor ≤ 2*err := by
  obtain ⟨hm, hmin⟩ := best_spec score first rest
  have lower := (uniform _ hm).1
  have upper := (uniform _ hc).2
  have cmp := hmin _ hc
  omega


open ScreeningCost

def estimated (s : Nat) (blocks : List T → List Int) (order : List T) : Int :=
  ((properPrefixes order).map (fun pre => median s (blocks pre))).sum

private theorem sum_error (prefixes : List (List T)) (truth : List T → Nat)
    (value : List T → Int) (e : Int)
    (each : ∀ p ∈ prefixes, (truth p : Int)-e ≤ value p ∧ value p ≤ (truth p : Int)+e) :
    (total prefixes truth : Int) - (prefixes.length : Int)*e ≤ (prefixes.map value).sum ∧
    (prefixes.map value).sum ≤ (total prefixes truth : Int) + (prefixes.length : Int)*e := by
  induction prefixes with
  | nil => simp [total]
  | cons p ps ih =>
    have a := each p (by simp)
    have b := ih (fun q h => each q (by simp [h]))
    change ((truth p + total ps truth : Nat) : Int) - ((ps.length+1 : Nat) : Int)*e ≤ _ ∧
      _ ≤ ((truth p+total ps truth : Nat):Int) + ((ps.length+1 : Nat):Int)*e
    simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul,
      List.map_cons, List.sum_cons]
    omega

/-- From prefix block-majority guarantees to the scan cost of the order
actually selected by sorting blocks and minimizing the sum of medians.
All candidate full schedules have the same length and fallback mass. -/
theorem median_scan_regret (law : List (X × Nat)) (hit : X → T → Bool)
    (fallback m s : Nat) (e : Int) (blocks : List T → List Int)
    (first : List T) (rest : List (List T)) (competitor : List T)
    (inside : competitor ∈ first::rest)
    (same : ∀ order ∈ first::rest, order.length=m ∧
        survivalMass law hit order = survivalMass law hit first)
    (majorities : ∀ order ∈ first::rest, ∀ p ∈ properPrefixes order,
        (blocks p).length = 2*s+1 ∧
        (blocks p).countP (fun x => decide
          (x < (survivalMass law hit p : Int)-e ∨ (survivalMass law hit p : Int)+e < x)) ≤ s) :
    (populationCost law hit fallback (best (estimated s blocks) first rest) : Int) -
      populationCost law hit fallback competitor ≤ 2*((m:Int)*e) := by
  let common : Int := (fallback * survivalMass law hit first : Nat)
  let actual := fun o => (populationCost law hit fallback o : Int) - common
  have hu (o : List T) (ho : o ∈ first::rest) :
      actual o - (m:Int)*e ≤ estimated s blocks o ∧ estimated s blocks o ≤ actual o + (m:Int)*e := by
    obtain ⟨len, mass⟩ := same o ho
    have a : actual o = (total (properPrefixes o) (survivalMass law hit) : Int) := by
      dsimp only [actual,common]
      rw [populationCost_eq_prefix_survivals,mass,Int.natCast_add]; omega
    have size : (properPrefixes o).length = m := by simp [properPrefixes,len]
    have b := sum_error (properPrefixes o) (survivalMass law hit) (fun p => median s (blocks p)) e
      (fun p hp => median_of_majority _ _ _ _ (majorities o ho p hp).1 (majorities o ho p hp).2)
    rw [size] at b
    simpa only [a,estimated] using b
  have result := selected_regret (estimated s blocks) actual first rest ((m:Int)*e) hu competitor inside
  dsimp only [actual] at result
  omega

end Screening.MedianLearner
