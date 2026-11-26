import Screening.CellLift
import Screening.MomentCube
import Screening.WitnessOverlap

/-! Arithmetic hard-source construction, with rational masses on one common
scale. The reference slack and physical fiber occupancy are explicit inputs.
The signed exact-cell perturbation, its overlap bound, and the resulting
physical-word law are constructed rather than assumed. -/

namespace Screening.ArithmeticWitness
open Screening.MomentCube
open Screening.CellLift

def exactMass [DecidableEq V] (atoms : List (List V × Int)) (c : List V) : Int :=
  sumOn atoms (fun a => if a.1 = c then a.2 else 0)

def table (labels : List (List V)) (a : List V → Nat) : List (List V × Int) :=
  labels.map (fun c => (c, (a c : Int)))

def specs (edges : List (List V)) (coef : List V → Int) : List (List V × Int) :=
  edges.map (fun e => (e,coef e))

def source (base : List (List V × Int)) (edges : List (List V)) (coef : List V → Int) :=
  addCubes base (specs edges coef)

def effect [DecidableEq V] (c : List V) (coef : List V → Int) : List (List V) → Int
  | [] => 0
  | e :: es => (if c.Sublist e then coef e * (-1 : Int)^c.length else 0) + effect c coef es

theorem sum_congr (xs : List A) {f g : A → Int} (h : ∀ x ∈ xs, f x = g x) :
    sumOn xs f = sumOn xs g := congrArg List.sum (List.map_congr_left h)

theorem sum_append (xs ys : List A) (f : A → Int) :
    sumOn (xs++ys) f = sumOn xs f + sumOn ys f := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    change f a + sumOn (xs++ys) f = (f a + sumOn xs f) + sumOn ys f
    rw [ih, Int.add_assoc]

private theorem sum_zero (xs : List A) : sumOn xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change 0 + sumOn xs (fun _ => 0) = 0; omega

private theorem sum_plus (xs : List A) (f g : A → Int) :
    sumOn xs (fun x => f x + g x) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change f a + g a + sumOn xs (fun x => f x + g x) =
      (f a + sumOn xs f) + (g a + sumOn xs g)
    omega

theorem sum_factor (xs : List A) (k : Int) (f : A → Int) :
    sumOn xs (fun x => k*f x) = k * sumOn xs f := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    change k*f a + sumOn xs (fun x => k*f x) = k*(f a+sumOn xs f)
    rw [ih, Int.mul_add]

theorem sum_pick [DecidableEq A] (xs : List A) (g : A → Int) (c : A)
    (unique : xs.Nodup) :
    sumOn xs (fun a => if a=c then g a else 0) = if c ∈ xs then g c else 0 := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    change (if a=c then g a else 0) + sumOn xs (fun z => if z=c then g z else 0) = _
    rw [ih tail]
    by_cases h : a=c
    · subst a; simp [fresh]
    · simp [List.mem_cons, h, Ne.symm h]

theorem exact_cube [DecidableEq V] (edge c : List V) (d : Int) (hd : edge.Nodup) :
    exactMass (cubeAtoms edge d) c = if c.Sublist edge then d * (-1 : Int)^c.length else 0 := by
  unfold exactMass cubeAtoms
  simp only [sumOn, List.map_map, Function.comp_def]
  have picked := sum_pick (cells edge) (fun x => d * (-1 : Int)^x.length) c (cells_nodup hd)
  simpa only [sumOn, mem_cells] using picked

theorem exact_table [DecidableEq V] (labels : List (List V)) (a : List V → Nat) (c : List V)
    (hd : labels.Nodup) (hc : c ∈ labels) : exactMass (table labels a) c = (a c : Int) := by
  unfold exactMass table
  simpa only [sumOn, List.map_map, Function.comp_def, if_pos hc] using
    sum_pick labels (fun z => (a z : Int)) c hd

theorem exact_source [DecidableEq V] (base : List (List V × Int)) (edges : List (List V))
    (coef : List V → Int) (c : List V) (hd : ∀ e ∈ edges, e.Nodup) :
    exactMass (source base edges coef) c = exactMass base c + effect c coef edges := by
  induction edges with
  | nil => simp [source, specs, addCubes, effect]
  | cons e es ih =>
    change sumOn (cubeAtoms e (coef e) ++ source base es coef) _ = _
    rw [sum_append]
    change exactMass (cubeAtoms e (coef e)) c + exactMass (source base es coef) c = _
    rw [exact_cube e c _ (hd e (by simp)), ih (fun z hz => hd z (by simp [hz]))]
    simp only [effect]
    omega

private theorem sign_abs (j : Nat) : ((-1 : Int)^j).natAbs = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [Int.pow_succ, Int.natAbs_mul, ih]

private theorem effect_count [DecidableEq V] (edges : List (List V)) (coef : List V → Int)
    (c : List V) (d : Nat) (amp : ∀ e ∈ edges, (coef e).natAbs ≤ d) :
    (effect c coef edges).natAbs ≤ d * edges.countP (fun e => decide (c.Sublist e)) := by
  induction edges with
  | nil => simp [effect]
  | cons e es ih =>
    have hi := ih (fun t ht => amp t (by simp [ht]))
    by_cases h : c.Sublist e
    · simp only [effect, h, if_true, List.countP_cons, decide_true, Nat.mul_add, Nat.mul_one]
      have hd := amp e (by simp)
      have := Int.natAbs_add_le (coef e * (-1:Int)^c.length) (effect c coef es)
      simp only [Int.natAbs_mul, sign_abs, Nat.mul_one] at this
      omega
    · simpa [effect, h, List.countP_cons] using hi

/-- A j-cell changes by at most d*m^(h−j) integer numerator units,
uniformly over all choices of coefficient signs. -/
theorem exact_perturbation_bound [DecidableEq V] (base : List (List V × Int))
    (menu c : List V) (edges : List (List V)) (coef : List V → Int) (h d : Nat)
    (menuUnique : menu.Nodup) (distinct : edges.Nodup)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (degree : ∀ e ∈ edges, e.length=h)
    (amp : ∀ e ∈ edges, (coef e).natAbs ≤ d) :
    (exactMass (source base edges coef) c - exactMass base c).natAbs ≤
      d * menu.length^(h-c.length) := by
  rw [exact_source _ _ _ _ (fun e he => (canonical e he).nodup menuUnique)]
  rw [show exactMass base c + effect c coef edges - exactMass base c = effect c coef edges by omega]
  exact Nat.le_trans (effect_count edges coef c d amp) (Nat.mul_le_mul_left d
    (Screening.WitnessOverlap.overlap_bound menu c edges h menuUnique distinct canonical degree))

def legalCells (menu : List V) (h : Nat) :=
  (cells menu).filter (fun c => decide (c.length ≤ h))

theorem legal_unique (menu : List V) (h : Nat) (unique : menu.Nodup) :
    (legalCells menu h).Nodup := (cells_nodup unique).filter _

private theorem covers_source (menu : List V) (h : Nat) (base : List (List V × Int))
    (edges : List (List V)) (coef : List V → Int)
    (covered : ∀ a ∈ base, a.1 ∈ legalCells menu h)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (degree : ∀ e ∈ edges, e.length≤h) :
    ∀ a ∈ source base edges coef, a.1 ∈ legalCells menu h := by
  induction edges with
  | nil => exact covered
  | cons e es ih =>
    intro a ha
    change a ∈ cubeAtoms e (coef e) ++ source base es coef at ha
    rcases List.mem_append.mp ha with hleft | hright
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hleft
      have inside := mem_cells.mp hc
      have sz := inside.length_le
      have fit := Nat.le_trans sz (degree e (by simp))
      exact List.mem_filter.mpr ⟨mem_cells.mpr (inside.trans (canonical e (by simp))), by simpa⟩
    · exact ih (fun z hz => canonical z (by simp [hz])) (fun z hz => degree z (by simp [hz])) a hright

private theorem regroup [DecidableEq V] (atoms : List (List V × Int))
    (labels : List (List V)) (q : List V) (unique : labels.Nodup)
    (covered : ∀ a ∈ atoms, a.1 ∈ labels) :
    histogramMoment atoms q = sumOn labels (fun c => if q ⊆ c then exactMass atoms c else 0) := by
  induction atoms with
  | nil =>
    have z := sum_zero labels
    simpa [histogramMoment, exactMass, sumOn] using z.symm
  | cons a xs ih =>
    obtain ⟨z,v⟩ := a
    have inside : z ∈ labels := covered (z,v) (by simp)
    have hrest := ih (fun a ha => covered a (by simp [ha]))
    let entry := fun c => if c=z then (if q ⊆ z then v else 0) else 0
    let remainder := fun c => if q ⊆ c then exactMass xs c else 0
    have split :
        sumOn labels (fun c => if q ⊆ c then exactMass ((z,v)::xs) c else 0) =
        sumOn labels entry + sumOn labels remainder := by
      rw [← sum_plus]
      apply sum_congr
      intro c _
      change (if q ⊆ c then (if z=c then v else 0) + exactMass xs c else 0) = _
      by_cases eq : c=z
      · subst c; by_cases hq : q ⊆ z <;> simp [entry, remainder, hq]
      · by_cases hq : q ⊆ c <;> simp [entry,remainder,hq,eq,Ne.symm eq]
    have single := sum_pick labels (fun _ => if q ⊆ z then v else 0) z unique
    rw [if_pos inside] at single
    change (if q ⊆ z then v else 0) + histogramMoment xs q = _
    change sumOn labels entry = (if q ⊆ z then v else 0) at single
    rw [split, ← hrest, single]

private theorem sum_cast (labels : List A) (a : A → Nat) :
    sumOn labels (fun c => (a c : Int)) = (sumNat labels a : Int) := by
  induction labels with
  | nil => rfl
  | cons c cs ih =>
    change (a c : Int) + sumOn cs (fun x => (a x : Int)) = (↑(a c + sumNat cs a) : Int)
    rw [ih, Int.natCast_add]

def wordAtoms (words : List W) (tag : W → List V) (weight : W → Nat) :=
  words.map (fun w => (tag w, (weight w : Int)))

private theorem words_exact [DecidableEq V] (words : List W) (tag : W → List V)
    (weight : W → Nat) (c : List V) :
    exactMass (wordAtoms words tag weight) c = (cellMass words tag weight c : Int) := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    change (if tag w = c then (weight w : Int) else 0) + exactMass (wordAtoms ws tag weight) c =
      (↑((if tag w = c then weight w else 0) + cellMass ws tag weight c) : Int)
    rw [ih,Int.natCast_add]
    by_cases h : tag w=c <;> simp [h]

private theorem table_covered (labels : List (List V)) (a : List V → Nat) :
    ∀ t ∈ table labels a, t.1 ∈ labels := by
  intro t ht
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
  exact hc

private theorem preserve_low [DecidableEq V] (base : List (List V × Int))
    (edges : List (List V)) (coef : List V → Int) (q : List V) (h : Nat)
    (unique : ∀ e ∈ edges, e.Nodup) (degree : ∀ e ∈ edges, e.length=h)
    (low : q.length<h) : histogramMoment (source base edges coef) q = histogramMoment base q := by
  apply superposition_preserves_lower
  · intro s hs
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
    exact unique e he
  · intro s hs
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
    simpa [degree e he] using low

/-- A coarse reference cell provides enough room on both sides for its
signed update. The updated numerator is strictly positive, and the bounds
on the *updated* cell are conclusions. -/
theorem guarded_numerator (x : Int) (a cap factor low high : Nat)
    (positiveLower : 0 < low) (discrepancy : (x - (a:Int)).natAbs ≤ cap)
    (left : low + factor*cap ≤ factor*a) (right : factor*a + factor*cap ≤ high) :
    0 < x ∧ low ≤ factor*x.toNat ∧ factor*x.toNat ≤ high := by
  have inside : cap < a := Nat.lt_of_mul_lt_mul_left (by omega : factor*cap < factor*a)
  have linear := Int.natAbs_eq (x-(a:Int))
  have xpos : 0 < x := by rcases linear with hp|hp <;> omega
  have lower : a ≤ x.toNat + cap := by rcases linear with hp|hp <;> omega
  have upper : x.toNat ≤ a + cap := by rcases linear with hp|hp <;> omega
  have hl := Nat.mul_le_mul_left factor lower
  have hr := Nat.mul_le_mul_left factor upper
  rw [Nat.mul_add] at hl hr
  exact ⟨xpos,by omega,by omega⟩

/-- Reference error and perturbation can share the allowed relative-density
error budget. This concrete sufficient condition allocates half to each.
All integers are on the common rational scale used in the physical lift. -/
theorem half_slack (L n a cap D b e : Nat) (eps : e ≤ b)
    (refError : 2 * ((↑(b*L*a) : Int) - (↑(b*D*n):Int)).natAbs ≤ e*D*n)
    (cubeError : 2*(b*L*cap) ≤ e*D*n) :
    (b-e)*D*n + b*L*cap ≤ b*L*a ∧ b*L*a + b*L*cap ≤ (b+e)*D*n := by
  have range := Nat.mul_le_mul_right n (Nat.mul_le_mul_right D eps)
  simp only [Nat.sub_mul, Nat.add_mul]
  have cases := Int.natAbs_eq ((↑(b*L*a):Int) - (↑(b*D*n):Int))
  rcases cases with hc|hc <;> omega

/-- A single amplitude condition suffices for every cell once the physical
fiber has size at least L/(2*Q^j). In the paper Q=2P and m≤Q. -/
theorem scalar_amplitude_budget (m Q L n b D eps d h j : Nat)
    (degree : j≤h) (sparse : m≤Q) (fiberLower : L ≤ 2*n*Q^j)
    (amp : 4*b*d*Q^h ≤ eps*D) :
    2 * (b*L*(d*m^(h-j))) ≤ eps*D*n := by
  have qbound : m^(h-j) ≤ Q^(h-j) := Nat.pow_le_pow_left sparse _
  have qexp : Q^j * Q^(h-j) = Q^h := by rw [← Nat.pow_add, Nat.add_sub_of_le degree]
  calc
    _ ≤ 2 * (b*(2*n*Q^j)*(d*Q^(h-j))) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul_left b fiberLower)
        (Nat.mul_le_mul_left d qbound))
    _ = 4*b*d*(Q^j*Q^(h-j))*n := by
      change 2 * (b*((2*n)*Q^j)*(d*Q^(h-j))) = (2*2)*b*d*(Q^j*Q^(h-j))*n
      ac_rfl
    _ = 4*b*d*Q^h*n := by rw [qexp]
    _ ≤ _ := Nat.mul_le_mul_right n amp

private theorem table_total [DecidableEq V] (labels : List (List V)) (ref : List V → Nat) :
    histogramMoment (table labels ref) [] = (sumNat labels ref : Int) := by
  simpa [histogramMoment, table, sumOn, List.map_map, Function.comp_def] using sum_cast labels ref

/-- Realization of the signed hard laws on a tagged integer population.

The reference masses are ref(c)/D and uniform physical masses are n(c)/L.
The two error premises allocate half the relative allowance eps/b to the
reference discrepancy and half to the cube perturbations, respectively.
They concern the unperturbed reference, the independently supplied amplitude
bound, and actual fiber counts. The conclusion constructs a new physical law
for every choice of signs; none of its probabilities are inputs. -/
theorem physical_witness [DecidableEq V] (words : List Nat) (tag : Nat → List V)
    (menu : List V) (edges : List (List V)) (coef : List V → Int)
    (ref : List V → Nat) (h d D b eps : Nat)
    (degreePos : 0<h) (denPos : 0<D) (epsSmall : eps<b)
    (menuUnique : menu.Nodup) (distinct : edges.Nodup)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (degree : ∀ e ∈ edges, e.length=h)
    (amp : ∀ e ∈ edges, (coef e).natAbs ≤ d)
    (complete : ∀ w ∈ words, tag w ∈ legalCells menu h)
    (occupied : ∀ c ∈ legalCells menu h, 0 < fiberSize words tag c)
    (normalized : sumNat (legalCells menu h) ref = D)
    (referenceError : ∀ c ∈ legalCells menu h,
      2 * ((↑(b*words.length*ref c):Int) - (↑(b*D*fiberSize words tag c):Int)).natAbs ≤
        eps*D*fiberSize words tag c)
    (perturbationBudget : ∀ c ∈ legalCells menu h,
      2 * (b*words.length*(d*menu.length^(h-c.length))) ≤ eps*D*fiberSize words tag c) :
    ∃ K : Nat, ∃ weight : Nat → Nat,
      0<K ∧ sumNat words weight = D*K ∧
      (∀ w ∈ words,
        (b-eps)*(D*K) ≤ b*words.length*weight w ∧
        b*words.length*weight w ≤ (b+eps)*(D*K)) ∧
      (∀ c ∈ legalCells menu h,
        0 < cellMass words tag weight c ∧
        (cellMass words tag weight c : Int) =
          (K:Int)*exactMass (source (table (legalCells menu h) ref) edges coef) c) ∧
      (∀ q : List V, q.length<h →
        histogramMoment (wordAtoms words tag weight) q =
          (K:Int)*histogramMoment (table (legalCells menu h) ref) q) := by
  let labels := legalCells menu h
  let base := table labels ref
  let updated := source base edges coef
  let num := fun c => (exactMass updated c).toNat
  have unique : labels.Nodup := legal_unique menu h menuUnique
  have unE : ∀ e ∈ edges, e.Nodup := fun e he => (canonical e he).nodup menuUnique
  have cov : ∀ t ∈ updated, t.1 ∈ labels :=
    covers_source menu h base edges coef (table_covered labels ref) canonical
      (fun e he => Nat.le_of_eq (degree e he))
  have cal (c : List V) (hc : c ∈ labels) :
      0 < exactMass updated c ∧
      (b-eps)*D*fiberSize words tag c ≤ b*words.length*num c ∧
      b*words.length*num c ≤ (b+eps)*D*fiberSize words tag c := by
    have bound := exact_perturbation_bound base menu c edges coef h d menuUnique distinct canonical degree amp
    have baseEq : exactMass base c = (ref c:Int) := exact_table labels ref c unique hc
    rw [baseEq] at bound
    obtain ⟨lo,hi⟩ := half_slack words.length (fiberSize words tag c) (ref c)
      (d*menu.length^(h-c.length)) D b eps (Nat.le_of_lt epsSmall)
      (referenceError c hc) (perturbationBudget c hc)
    exact guarded_numerator (exactMass updated c) (ref c) _ (b*words.length) _ _
      (Nat.mul_pos (Nat.mul_pos (by omega) denPos) (occupied c hc)) bound lo hi
  have repr (c : List V) (hc : c ∈ labels) : (num c:Int)=exactMass updated c :=
    Int.toNat_of_nonneg (Int.le_of_lt (cal c hc).1)
  have totalEq : (sumNat labels num:Int) = (D:Int) := by
    calc
      _ = sumOn labels (fun c => (num c:Int)) := (sum_cast labels num).symm
      _ = sumOn labels (exactMass updated) := sum_congr labels repr
      _ = histogramMoment updated [] := by simpa using (regroup updated labels [] unique cov).symm
      _ = histogramMoment base [] := preserve_low base edges coef [] h unE degree degreePos
      _ = (sumNat labels ref:Int) := table_total labels ref
      _ = _ := by rw [normalized]
  obtain ⟨K,weight,Kpos,_,total,recovers,_,denBounds⟩ :=
    lift_rational_cell_law words labels tag num D b (b-eps) (b+eps) denPos (by omega)
      unique complete occupied (Int.ofNat_inj.mp totalEq) (fun c hc => (cal c hc).2)
  have cellEq (c : List V) (hc : c ∈ labels) : (cellMass words tag weight c:Int) =
      (K:Int)*exactMass updated c := by
    rw [recovers c hc, Int.natCast_mul, repr c hc]
  have wordCov : ∀ a ∈ wordAtoms words tag weight, a.1 ∈ labels := by
    intro a ha
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact complete w hw
  refine ⟨K,weight,Kpos,total,denBounds,?_,?_⟩
  · intro c hc
    have npos : 0 < num c := by
      have := (cal c hc).1
      have := repr c hc
      omega
    exact ⟨by rw [recovers c hc]; exact Nat.mul_pos Kpos npos, cellEq c hc⟩
  · intro q size
    calc
      _ = sumOn labels (fun c => if q ⊆ c then exactMass (wordAtoms words tag weight) c else 0) :=
        regroup _ _ _ unique wordCov
      _ = sumOn labels (fun c => (K:Int) * (if q ⊆ c then exactMass updated c else 0)) := by
        apply sum_congr
        intro c hc
        by_cases sub : q ⊆ c <;> simp [sub, words_exact, cellEq c hc]
      _ = (K:Int)*histogramMoment updated q := by
        rw [sum_factor, ← regroup updated labels q unique cov]
      _ = _ := by rw [show histogramMoment updated q = histogramMoment base q from
          preserve_low base edges coef q h unE degree size]

def correction [DecidableEq V] (base : List (List V × Int)) (target : List V → Int) (e : List V) :=
  (-1:Int)^e.length * (target e - histogramMoment base e)

def calibrated [DecidableEq V] (menu : List V) (h : Nat) (base : List (List V × Int))
    (target : List V → Int) := source base (legalCells menu h) (correction base target)

private theorem legal_info {menu c : List V} {h : Nat} (hc : c ∈ legalCells menu h) :
    c.Sublist menu ∧ c.length ≤ h := by simpa [legalCells, mem_cells] using hc

private theorem sign_squared (n : Nat) : (-1:Int)^n * (-1:Int)^n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Int.pow_succ, Int.neg_mul, Int.mul_neg, ih]

/-- Möbius calibration corrects all legal containment moments simultaneously,
including the empty query. The target may be the scaled reciprocal products.
This is an exact identity for the constructed signed table, before positivity. -/
theorem calibrated_moment [DecidableEq V] (menu : List V) (h : Nat) (base : List (List V×Int))
    (target : List V → Int) (q : List V) (unique : menu.Nodup) (legal : q∈legalCells menu h) :
    histogramMoment (calibrated menu h base target) q = target q := by
  let labels := legalCells menu h
  let corr := correction base target
  have hd : ∀ s ∈ specs labels corr, s.1.Nodup := by
    intro s hs
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
    exact (legal_info he).1.nodup unique
  have calcMom := histogram_superposition base (specs labels corr) q hd
  have sumEq : sumOn (specs labels corr) (fun s =>
      if s.1 ⊆ q ∧ q ⊆ s.1 then s.2 * (-1:Int)^s.1.length else 0) =
      sumOn labels (fun e => if e=q then target e-histogramMoment base e else 0) := by
    change (((labels.map _).map _).sum) = _
    simp only [List.map_map, Function.comp_def]
    apply sum_congr labels
    intro e he
    have seteq : (e ⊆ q ∧ q ⊆ e) ↔ e=q := by
      constructor
      · intro both
        exact Screening.WitnessOverlap.canonical_ext unique (legal_info he).1
          (legal_info legal).1 both.1 both.2
      · rintro rfl; simp
    by_cases eq : e=q
    · rw [if_pos (seteq.mpr eq),if_pos eq]
      change ((-1:Int)^e.length*(target e-histogramMoment base e))*(-1:Int)^e.length = _
      calc
        _ = ((-1:Int)^e.length*(-1:Int)^e.length)*(target e-histogramMoment base e) := by ac_rfl
        _ = _ := by rw [sign_squared,Int.one_mul]
    · simp [seteq,eq]
  rw [sumEq, sum_pick _ _ _ (legal_unique menu h unique), if_pos legal] at calcMom
  change histogramMoment (addCubes base (specs labels corr)) q = _
  omega

/-- If each count on its common numerator scale differs from the desired
containment by at most U, the reference adjustment on a j-cell is at most
U*(m+1)^(h−j). The count includes all correction degrees rather than h alone. -/
theorem calibration_discrepancy [DecidableEq V] (menu c : List V) (h U : Nat)
    (base : List (List V×Int)) (target : List V→Int) (unique : menu.Nodup)
    (rounding : ∀ e ∈ legalCells menu h, (target e-histogramMoment base e).natAbs ≤ U) :
    (exactMass (calibrated menu h base target) c - exactMass base c).natAbs ≤
      U*(menu.length+1)^(h-c.length) := by
  let labels := legalCells menu h
  let corr := correction base target
  have hd := fun e (he : e ∈ labels) => (legal_info he).1.nodup unique
  have a : ∀ e ∈ labels, (corr e).natAbs ≤ U := by
    intro e he
    simpa [corr,correction,Int.natAbs_mul,sign_abs] using rounding e he
  change (exactMass (source base labels corr) c - exactMass base c).natAbs ≤ _
  rw [exact_source _ _ _ _ hd]
  rw [show exactMass base c + effect c corr labels - exactMass base c = effect c corr labels by omega]
  exact Nat.le_trans (effect_count labels corr c U a)
    (Nat.mul_le_mul_left U (Screening.WitnessOverlap.bounded_degree_overlap menu c labels h
      unique (legal_unique menu h unique) (fun e he => (legal_info he).1)
      (fun e he => (legal_info he).2)))

private theorem positive_table_moment [DecidableEq V] (atoms : List (List V×Int))
    (labels : List (List V)) (q : List V) (unique : labels.Nodup)
    (cover : ∀ a ∈ atoms, a.1∈labels) (positive : ∀ c∈labels, 0≤exactMass atoms c) :
    histogramMoment (table labels (fun c => (exactMass atoms c).toNat)) q =
      histogramMoment atoms q := by
  rw [regroup _ labels q unique (table_covered _ _),regroup atoms labels q unique cover]
  apply sum_congr
  intro c hc
  rw [exact_table _ _ c unique hc,Int.toNat_of_nonneg (positive c hc)]

/-- Uniform integer words first receive small rounding corrections at every
degree, after which the signed h-cubes encode the hard instance. This result
starts from the physical uniform cell counts; it produces and calibrates the
reference as part of the proof. Q=2P in the interval application. -/
theorem calibrated_physical_witness [DecidableEq V] (words : List Nat) (tag : Nat → List V)
    (menu : List V) (edges : List (List V)) (coef : List V → Int)
    (target : List V → Int) (h d U b eps Q : Nat)
    (degreePos : 0<h) (uPos : 0<U) (wordsPos : 0<words.length) (epsSmall : eps<b)
    (sparse : menu.length+1 ≤ Q) (menuUnique : menu.Nodup) (distinct : edges.Nodup)
    (canonical : ∀ e ∈ edges, e.Sublist menu) (degree : ∀ e ∈ edges, e.length=h)
    (amp : ∀ e ∈ edges, (coef e).natAbs ≤ d)
    (complete : ∀ w∈words, tag w∈legalCells menu h)
    (fiberLower : ∀ c∈legalCells menu h, words.length ≤ 2*fiberSize words tag c*Q^c.length)
    (intervalSize : 4*b*Q^h ≤ eps*words.length)
    (amplitude : 4*b*d*Q^h ≤ eps*(words.length*U))
    (targetTotal : target [] = (↑(words.length*U):Int))
    (rounding : ∀ c∈legalCells menu h,
      (target c - histogramMoment
        (table (legalCells menu h) (fun s => U*fiberSize words tag s)) c).natAbs ≤ U) :
    ∃ K : Nat, ∃ weight : Nat → Nat, 0<K ∧
      sumNat words weight = (words.length*U)*K ∧
      (∀ w∈words,
        (b-eps)*((words.length*U)*K) ≤ b*words.length*weight w ∧
        b*words.length*weight w ≤ (b+eps)*((words.length*U)*K)) ∧
      (∀ c∈legalCells menu h, 0<cellMass words tag weight c) ∧
      (∀ q∈legalCells menu h, q.length<h →
        histogramMoment (wordAtoms words tag weight) q = (K:Int)*target q) ∧
      (∀ c∈legalCells menu h,
        (cellMass words tag weight c : Int) =
          (K:Int)*(exactMass
            (calibrated menu h (table (legalCells menu h) (fun s => U*fiberSize words tag s)) target)
            c + effect c coef edges)) := by
  let labels := legalCells menu h
  let D := words.length*U
  let a0 := fun c => U*fiberSize words tag c
  let start := table labels a0
  let base := calibrated menu h start target
  let ref := fun c => (exactMass base c).toNat
  have unique := legal_unique menu h menuUnique
  have dp : 0 < D := Nat.mul_pos wordsPos uPos
  have occupied (c : List V) (hc : c∈labels) : 0 < fiberSize words tag c := by
    have hl := fiberLower c hc
    by_cases z : fiberSize words tag c=0
    · simp only [z,Nat.mul_zero,Nat.zero_mul] at hl
      omega
    · omega
  have scalar : 4*b*U*Q^h ≤ eps*D := by
    calc
      _ = (4*b*Q^h)*U := by ac_rfl
      _ ≤ (eps*words.length)*U := Nat.mul_le_mul_right U intervalSize
      _ = _ := by dsimp [D]; ac_rfl
  have refControl (c : List V) (hc : c∈labels) :
      0<exactMass base c ∧
      2*((↑(b*words.length*ref c):Int)-(↑(b*D*fiberSize words tag c):Int)).natAbs ≤
        eps*D*fiberSize words tag c := by
    let cap := U*(menu.length+1)^(h-c.length)
    let n := fiberSize words tag c
    let F := b*words.length
    have lim : 2*(F*cap) ≤ eps*D*n :=
      scalar_amplitude_budget (menu.length+1) Q words.length n b D eps U h c.length
        (legal_info hc).2 sparse (fiberLower c hc) scalar
    have center : F*a0 c=b*D*n := by dsimp [F,a0,D,n]; ac_rfl
    have delta : (exactMass base c - (↑(a0 c):Int)).natAbs ≤ cap := by
      have r := calibration_discrepancy menu c h U start target menuUnique rounding
      rw [show exactMass start c = (a0 c:Int) from exact_table labels a0 c unique hc] at r
      exact r
    have zeroError : 2*((↑(F*a0 c):Int)-(↑(b*D*n):Int)).natAbs ≤ eps*D*n := by
      simp [center]
    obtain ⟨lo,hi⟩ := half_slack words.length n (a0 c) cap D b eps
      (Nat.le_of_lt epsSmall) zeroError lim
    have positive := (guarded_numerator (exactMass base c) (a0 c) cap F _ _
      (Nat.mul_pos (Nat.mul_pos (by omega) dp) (occupied c hc)) delta lo hi).1
    refine ⟨positive,?_⟩
    have ra : (ref c : Int)=exactMass base c := Int.toNat_of_nonneg (Int.le_of_lt positive)
    change 2*((↑(F*ref c):Int)-(↑(b*D*n):Int)).natAbs ≤ _
    rw [← center,Int.natCast_mul F (ref c),Int.natCast_mul F (a0 c),ra, ← Int.mul_sub,
      Int.natAbs_mul,Int.natAbs_ofNat]
    exact Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left F delta)) lim
  have coverBase : ∀ t∈base,t.1∈labels := covers_source menu h start labels
    (correction start target) (table_covered labels a0) (fun e he => (legal_info he).1)
    (fun e he => (legal_info he).2)
  have moments (q : List V) (hq : q∈labels) :
      histogramMoment (table labels ref) q = target q :=
    (positive_table_moment base labels q unique coverBase
      (fun c hc => Int.le_of_lt (refControl c hc).1)).trans
      (calibrated_moment menu h start target q menuUnique hq)
  have emptyLegal : []∈labels := by simp [labels,legalCells,mem_cells]
  have norm : sumNat labels ref=D := by
    apply Int.ofNat_inj.mp
    exact (table_total labels ref).symm.trans ((moments [] emptyLegal).trans targetTotal)
  have budget (c : List V) (hc : c∈labels) :
      2*(b*words.length*(d*menu.length^(h-c.length))) ≤ eps*D*fiberSize words tag c :=
    scalar_amplitude_budget menu.length Q words.length _ b D eps d h c.length
      (legal_info hc).2 (by omega) (fiberLower c hc) amplitude
  obtain ⟨K,weight,kpos,tot,dens,cell,low⟩ :=
    physical_witness words tag menu edges coef ref h d D b eps degreePos dp epsSmall
      menuUnique distinct canonical degree amp complete occupied norm (fun c hc => (refControl c hc).2)
      budget
  refine ⟨K,weight,kpos,tot,dens,fun c hc => (cell c hc).1,?_,?_⟩
  · intro q hq small
    exact (low q small).trans (congrArg ((K:Int)*·) (moments q hq))
  · intro c hc
    rw [(cell c hc).2,exact_source _ _ _ _ (fun e he => (canonical e he).nodup menuUnique),
      exact_table _ _ c unique hc]
    change (K:Int)*((↑(ref c):Int) + _) = _
    rw [show (↑(ref c):Int)=exactMass base c from Int.toNat_of_nonneg (Int.le_of_lt (refControl c hc).1)]

private theorem uniform_exact_count [DecidableEq V] (words : List Nat) (tag : Nat→List V)
    (U : Nat) (c : List V) :
    exactMass (wordAtoms words tag (fun _ => U)) c = (↑(U*fiberSize words tag c):Int) := by
  induction words with
  | nil => simp [exactMass,wordAtoms,sumOn,fiberSize]
  | cons w ws ih =>
    change (if tag w=c then (U:Int) else 0) + exactMass (wordAtoms ws tag (fun _ => U)) c = _
    rw [ih]
    by_cases he : tag w=c <;>
      simp [fiberSize,List.filter_cons,he,Nat.mul_succ,Int.natCast_add,Int.add_comm]

/-- The histogram of uniform fiber counts is exactly U times the literal
number of physical words on which all members of the query hit. -/
theorem uniform_table_count [DecidableEq V] (words : List Nat) (tag : Nat→List V)
    (labels : List (List V)) (U : Nat) (q : List V) (unique : labels.Nodup)
    (complete : ∀ w∈words, tag w∈labels) :
    histogramMoment (table labels (fun s => U*fiberSize words tag s)) q =
      (↑(U*words.countP (fun w => decide (q⊆tag w))):Int) := by
  have covered : ∀ t∈wordAtoms words tag (fun _ => U), t.1∈labels := by
    intro t ht
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
    exact complete w hw
  calc
    _ = histogramMoment (wordAtoms words tag (fun _ => U)) q := by
      rw [regroup _ labels q unique (table_covered _ _),regroup _ labels q unique covered]
      apply sum_congr
      intro c hc
      rw [exact_table _ _ c unique hc,uniform_exact_count]
    _ = _ := by
      clear complete covered
      induction words with
      | nil => simp [histogramMoment,wordAtoms,sumOn]
      | cons w ws ih =>
        change (if q⊆tag w then (U:Int) else 0) + histogramMoment (wordAtoms ws tag (fun _ => U)) q = _
        rw [ih]
        by_cases hc : q⊆tag w <;>
          simp [List.countP_cons,hc,Nat.mul_add,Nat.mul_succ,Int.natCast_add,Int.add_comm]

end Screening.ArithmeticWitness
