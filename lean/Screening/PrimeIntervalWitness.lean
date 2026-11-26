import Screening.ArithmeticWitness
import Screening.IntervalCounts

/-! Specialization of the calibrated hard law to the actual odd integers in
[2L,4L). All divisibility predicates are computed on the corresponding word.
The prime menu is an input, so its existence need not be an axiom. -/

namespace Screening.PrimeIntervalWitness
open Screening.IntervalCounts Screening.ArithmeticWitness Screening.CellLift Screening.MomentCube

def words (L : Nat) := (List.range L).map (word L)
def tag (menu : List Nat) (w : Nat) := menu.filter (fun p => decide (p ∣ w))
def count (ws : List Nat) (menu query : List Nat) :=
  ws.countP (fun w => decide (query ⊆ tag menu w))

theorem words_nodup (L : Nat) : (words L).Nodup := by
  apply List.pairwise_map.mpr
  exact (List.nodup_range (n := L)).imp (by
    intro x y ne eq
    unfold word at eq
    omega)

theorem mem_words (L w : Nat) :
    w∈words L ↔ 2*L ≤ w ∧ w < 4*L ∧ w%2=1 := by
  constructor
  · intro inside
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp inside
    have := List.mem_range.mp hk
    unfold word
    omega
  · rintro ⟨lower,upper,odd⟩
    apply List.mem_map.mpr
    refine ⟨w/2-L,List.mem_range.mpr (by omega),?_⟩
    unfold word
    omega

private theorem legal_info {menu c : List Nat} {h : Nat} (hc : c∈legalCells menu h) :
    c.Sublist menu ∧ c.length≤h := by simpa [legalCells,mem_cells] using hc

theorem complete_tags (menu : List Nat) (P L h : Nat) (positive : 0<P)
    (cap : 4*L < P^(h+1)) (unique : menu.Nodup) (prime : ∀p∈menu, IsPrime p)
    (lo : ∀p∈menu,P≤p) : ∀w∈words L,tag menu w∈legalCells menu h := by
  intro w hw
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hw
  have kfit := List.mem_range.mp hk
  exact List.mem_filter.mpr ⟨mem_cells.mpr List.filter_sublist,
    by simpa [tag] using natural_window_hit_cap kfit positive cap menu unique prime lo⟩

theorem literal_count (menu query : List Nat) (L : Nat) (inside : query ⊆ menu) :
    count (words L) menu query = containmentCount L L query := by
  unfold count words containmentCount
  rw [List.countP_map]
  apply List.countP_congr
  intro k _
  simp only [Function.comp_apply,decide_eq_true_eq,List.all_eq_true]
  constructor
  · intro hall x hx
    exact of_decide_eq_true (List.mem_filter.mp (hall hx)).2
  · intro hall x hx
    exact List.mem_filter.mpr ⟨inside hx,decide_eq_true (hall x hx)⟩

private theorem product_sub_dvd {xs ys : List Nat} (sub : xs.Sublist ys) :
    product xs ∣ product ys := by
  induction sub with
  | slnil => simp [product]
  | cons a _ ih => exact Nat.dvd_trans ih (Nat.dvd_mul_left _ a)
  | cons₂ a _ ih => exact Nat.mul_dvd_mul_left a ih

/-- On denominator L*U with U any multiple of the full menu product,
the target for q has numerator L*(U/product(q)). -/
def target (U L : Nat) (q : List Nat) : Int := (↑(L*(U/product q)):Int)

theorem product_target (menu c : List Nat) (U L : Nat) (multiple : product menu ∣ U)
    (sub : c.Sublist menu) : (L*(U/product c))*product c = L*U := by
  rw [Nat.mul_assoc,Nat.div_mul_cancel (Nat.dvd_trans (product_sub_dvd sub) multiple)]

theorem rounding_one_unit (menu : List Nat) (L h U : Nat) (multiple : product menu ∣ U)
    (unique : menu.Nodup)
    (prime : ∀p∈menu, IsPrime p) (odd : ∀p∈menu,p%2=1)
    (complete : ∀w∈words L,tag menu w∈legalCells menu h)
    (c : List Nat) (hc : c∈legalCells menu h) :
    (target U L c - histogramMoment
      (table (legalCells menu h) (fun s => U*fiberSize (words L) (tag menu) s)) c).natAbs ≤ U := by
  obtain ⟨sub,_⟩ := legal_info hc
  have cop := containment_eq L L c (sub.nodup unique) (fun p hp => prime p (sub.subset hp))
  have raw := count_error (odd_product c (fun p hp => odd p (sub.subset hp))) L L
  rw [← cop,← literal_count menu c L sub.subset] at raw
  let p := product c
  let n := count (words L) menu c
  let k := U/p
  have iden : k*p=U := Nat.div_mul_cancel (Nat.dvd_trans (product_sub_dvd sub) multiple)
  have dist : ((L:Int)-(↑(n*p):Int)).natAbs ≤ p := by
    change max (n*p-L) (L-n*p) < p at raw
    have s := Int.natAbs_eq ((L:Int)-(↑(n*p):Int))
    rcases s with h|h <;> omega
  rw [uniform_table_count _ _ _ _ _ (legal_unique menu h unique) complete]
  change ((↑(L*k):Int)-(↑(U*n):Int)).natAbs ≤ _
  have ident : (↑(L*k):Int)-(↑(U*n):Int) = (k:Int)*((L:Int)-(↑(n*p):Int)) := by
    rw [Int.mul_sub,← Int.natCast_mul,← Int.natCast_mul]
    rw [← iden]
    congr 2 <;> ac_rfl
  rw [ident,Int.natAbs_mul,Int.natAbs_ofNat]
  exact Nat.le_trans (Nat.mul_le_mul_left k dist) (Nat.le_of_eq iden)

private theorem count_sum (ws : List A) (f : A → Bool) :
    ws.countP f = sumNat ws (fun x => (f x).toNat) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (a::ws).countP f = (f a).toNat + sumNat ws (fun x => (f x).toNat)
    cases e : f a <;> simp [List.countP_cons,e,ih,Nat.add_comm]

private theorem sum_add (xs : List A) (f g : A → Nat) :
    sumNat xs (fun x => f x+g x) = sumNat xs f + sumNat xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x + g x + sumNat xs (fun z => f z+g z) = (f x+sumNat xs f)+(g x+sumNat xs g)
    omega

private theorem sum_const (xs : List A) (k : Nat) : sumNat xs (fun _ => k) = xs.length*k := by
  induction xs with
  | nil => simp [sumNat]
  | cons x xs ih => change k + sumNat xs (fun _ => k) = (xs.length+1)*k; rw [ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_mono (xs : List A) {f g : A → Nat} (le : ∀x∈xs, f x≤g x) :
    sumNat xs f≤sumNat xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.add_le_add (le x (by simp)) (ih (fun z hz => le z (by simp [hz])))

private theorem sum_swap (xs : List A) (ys : List B) (f : A→B→Nat) :
    sumNat xs (fun x => sumNat ys (f x)) = sumNat ys (fun y => sumNat xs (fun x => f x y)) := by
  induction xs with
  | nil => simpa [sumNat] using (sum_const ys 0).symm
  | cons x xs ih =>
    change sumNat ys (f x) + sumNat xs (fun x => sumNat ys (f x)) =
      sumNat ys (fun y => f x y + sumNat xs (fun x => f x y))
    rw [sum_add,ih]

private theorem member_le_sum (xs : List A) (f : A → Nat) (x : A) (mem : x∈xs) :
    f x ≤ sumNat xs f := by
  induction xs with
  | nil => simp at mem
  | cons z xs ih =>
    change f x ≤ f z + sumNat xs f
    rcases List.mem_cons.mp mem with eq|h
    · subst x; omega
    · have := ih h; omega

private theorem failed_subset (xs ys : List Nat) (no : ¬xs⊆ys) : ∃x∈xs,x∉ys := by
  induction xs with
  | nil => simp at no
  | cons z xs ih =>
    by_cases hz : z∈ys
    · have tail : ¬xs⊆ys := by
        intro hs
        apply no
        intro k hk
        rcases List.mem_cons.mp hk with he|hm
        · exact he ▸ hz
        · exact hs hm
      obtain ⟨k,hk,hn⟩ := ih tail
      exact ⟨k,by simp [hk],hn⟩
    · exact ⟨z,by simp,hz⟩

def extraCount (ws menu q : List Nat) (p : Nat) :=
  if p∈q then 0 else count ws menu (p::q)

/-- Union bound with exact physical meanings. A word containing q either
has exactly q as hits or also contains some new menu prime. -/
theorem contain_to_cell (ws menu q : List Nat) (unique : menu.Nodup) (sub : q.Sublist menu) :
    count ws menu q ≤ fiberSize ws (tag menu) q + sumNat menu (extraCount ws menu q) := by
  let row := fun w p => if p∈q then 0 else (decide (p::q ⊆ tag menu w)).toNat
  let mask := fun w => (decide (tag menu w=q)).toNat
  have each (w : Nat) : (decide (q⊆tag menu w)).toNat ≤ mask w + sumNat menu (row w) := by
    by_cases contains : q⊆tag menu w
    · by_cases eq : tag menu w=q
      · simp [mask,eq]
      · have ext : ¬tag menu w ⊆ q := fun h =>
          eq (Screening.WitnessOverlap.canonical_ext unique List.filter_sublist sub h contains)
        obtain ⟨p,hp,hq⟩ := failed_subset _ _ ext
        have union : p::q ⊆ tag menu w := by
          intro i hi
          rcases List.mem_cons.mp hi with he|hm
          · exact he ▸ hp
          · exact contains hm
        have bound := member_le_sum menu (row w) p (List.filter_sublist.subset hp)
        simp only [row,hq,if_false,union,decide_true,Bool.toNat_true] at bound
        simp only [contains,decide_true,Bool.toNat_true]
        exact Nat.le_trans bound (Nat.le_add_left _ _)
    · simp [contains]
  have fiber : sumNat ws mask = fiberSize ws (tag menu) q := by
    rw [← count_sum, List.countP_eq_length_filter]
    rfl
  have extra (p : Nat) : sumNat ws (fun w => row w p) = extraCount ws menu q p := by
    by_cases hp : p∈q
    · simp [row,extraCount,hp,sum_const]
    · simpa [row,extraCount,hp,count] using (count_sum ws (fun w => decide (p::q⊆tag menu w))).symm
  calc
    _ = sumNat ws (fun w => (decide (q⊆tag menu w)).toNat) := count_sum _ _
    _ ≤ sumNat ws (fun w => mask w+sumNat menu (row w)) := sum_mono ws (fun w _ => each w)
    _ = _ := by rw [sum_add, fiber, sum_swap]; simp only [extra]

/-- At full degree containment equals exact membership, with an arbitrary
menu order, provided the recorded tags respect the h-hit cap. -/
theorem full_cell_count (ws menu q : List Nat) (h : Nat) (unique : menu.Nodup)
    (sub : q.Sublist menu) (size : q.length=h) (cap : ∀w∈ws,(tag menu w).length ≤ h) :
    count ws menu q = fiberSize ws (tag menu) q := by
  unfold count fiberSize
  rw [← List.countP_eq_length_filter]
  apply List.countP_congr
  intro w hw
  simp only [decide_eq_true_eq]
  constructor
  · intro inc
    apply Screening.WitnessOverlap.canonical_ext unique List.filter_sublist sub _ inc
    intro p hp
    by_cases inside : p∈q
    · exact inside
    · have extra : p::q⊆tag menu w := by
        intro x hx
        rcases List.mem_cons.mp hx with he|hx
        · exact he ▸ hp
        · exact inc hx
      have nodes := Screening.WitnessOverlap.length_le_of_subset
        (List.nodup_cons.mpr ⟨inside,sub.nodup unique⟩) extra
      have limit := cap w hw
      simp only [List.length_cons] at nodes
      omega
  · rintro rfl; simp

private theorem product_upper (ps : List Nat) (Q : Nat) (hi : ∀ p∈ps,p≤Q) :
    product ps ≤ Q^ps.length := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    rw [product,List.length_cons,Nat.pow_succ,Nat.mul_comm p]
    exact Nat.mul_le_mul (ih (fun x hx => hi x (by simp [hx]))) (hi p (by simp))

private theorem product_positive (q : List Nat) (odd : ∀p∈q,p%2=1) : 0<product q := by
  have h := odd_product q odd
  omega

private theorem lower_algebra (L n f m p P : Nat) (sparse : 4*m ≤ P)
    (rounding : L ≤ n*p+p) (small : 4*((m+1)*p) ≤ L)
    (cover : n ≤ f + m*(L/(P*p)+1)) : L ≤ 2*f*p := by
  let k := L/(P*p)
  have gain1 : 4*(m*k*p) ≤ L := by
    calc
      _ = (4*m)*(k*p) := by ac_rfl
      _ ≤ P*(k*p) := Nat.mul_le_mul_right _ sparse
      _ = k*(P*p) := by ac_rfl
      _ ≤ _ := Nat.div_mul_le_self _ _
  have cover' := Nat.mul_le_mul_right p cover
  change n*p ≤ (f + m*(k+1))*p at cover'
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at cover' small
  simp only [Nat.one_mul] at small
  rw [Nat.mul_assoc]
  omega

/-- All actual exact cells, including the empty cell and every h-cell, have
at least L/(2 Q^j) words. For smaller cells this uses a union bound over one
extra menu prime. Full h-cells use the literal no-(h+1)-hits interval cap. -/
theorem physical_fiber_lower (menu : List Nat) (P Q L h : Nat)
    (positive : 0<P) (sparse : 4*menu.length≤P) (alphabet : menu.length+1≤Q)
    (large : 4*Q^h≤L) (cap : 4*L<P^(h+1)) (unique : menu.Nodup)
    (prime : ∀p∈menu,IsPrime p) (odd : ∀p∈menu,p%2=1)
    (lo : ∀p∈menu,P≤p) (hi : ∀p∈menu,p≤Q)
    (q : List Nat) (legal : q∈legalCells menu h) :
    L ≤ 2*fiberSize (words L) (tag menu) q*Q^q.length := by
  obtain ⟨sub,size⟩ := legal_info legal
  have inM {p : Nat} (hp : p∈q) := sub.subset hp
  let n := count (words L) menu q
  let f := fiberSize (words L) (tag menu) q
  let p := product q
  have ppos : 0<p := product_positive q (fun z hz => odd z (inM hz))
  have pmax : p≤Q^q.length := product_upper q Q (fun z hz => hi z (inM hz))
  have qpos : 0<Q := by omega
  have raw := count_error (odd_product q (fun z hz => odd z (inM hz))) L L
  rw [← containment_eq L L q (sub.nodup unique) (fun z hz => prime z (inM hz)),
    ← literal_count menu q L sub.subset] at raw
  change max (n*p-L) (L-n*p)<p at raw
  have base : L≤n*p+p := by omega
  have main : L≤2*f*p := by
    by_cases full : q.length=h
    · have allCap := complete_tags menu P L h positive cap unique prime lo
      have eq : n=f := full_cell_count (words L) menu q h unique sub full
        (fun w hw => (legal_info (allCap w hw)).2)
      have a : 4*p≤L := by rw [← full] at large; exact Nat.le_trans (Nat.mul_le_mul_left 4 pmax) large
      rw [eq] at base
      rw [Nat.mul_assoc]
      omega
    · have smaller : q.length+1≤h := by omega
      have lmax : 4*((menu.length+1)*p)≤L := by
        have top := Nat.pow_le_pow_right qpos smaller
        rw [Nat.pow_succ,Nat.mul_comm (Q^q.length) Q] at top
        exact Nat.le_trans (Nat.mul_le_mul_left 4 (Nat.le_trans (Nat.mul_le_mul alphabet pmax) top)) large
      have extra (r : Nat) (hr : r∈menu) : extraCount (words L) menu q r ≤ L/(P*p)+1 := by
        by_cases inQ : r∈q
        · simp [extraCount,inQ]
        · rw [extraCount,if_neg inQ]
          have oneIn : r::q⊆menu := by
            intro k hk
            rcases List.mem_cons.mp hk with he|hm
            · exact he ▸ hr
            · exact inM hm
          rw [literal_count _ _ _ oneIn,containment_eq L L _ (List.nodup_cons.mpr ⟨inQ,sub.nodup unique⟩)
            (fun k hk => prime k (oneIn hk))]
          have near := floor_or_ceiling (odd_product (r::q) (fun k hk => odd k (oneIn hk))) L L
          change hitCount L (r*p) L = L/(r*p) ∨ hitCount L (r*p) L = ceilingQuotient L (r*p) at near
          have divbound := Nat.div_le_div_left (Nat.mul_le_mul_right p (lo r hr)) (Nat.mul_pos positive ppos)
            (a := L)
          unfold ceilingQuotient at near
          rcases near with he | he
          · change hitCount L (r*p) L ≤ _
            omega
          · change hitCount L (r*p) L ≤ _
            split at he <;> omega
      have cover := contain_to_cell (words L) menu q unique sub
      have union := sum_mono menu extra
      rw [sum_const] at union
      exact lower_algebra L n f menu.length p P sparse base lmax
        (Nat.le_trans cover (Nat.add_le_add_left union f))
  exact Nat.le_trans main (Nat.mul_le_mul_left (2*f) pmax)

/-- Probability denominators are (L*U)*K. The fourth field states exact
reciprocal product probability without division, including the empty query.
The last field retains the actual signed change, including its sign, not
merely a bound on the resulting densities. -/
structure LiteralCertificate (menu : List Nat) (edges : List (List Nat)) (coef : List Nat→Int)
    (L h U b eps K : Nat) (weight : Nat→Nat) : Prop where
  positive : 0<K
  normalized : sumNat (words L) weight = (L*U)*K
  density : ∀w∈words L,
    (b-eps)*((L*U)*K) ≤ b*L*weight w ∧ b*L*weight w ≤ (b+eps)*((L*U)*K)
  lowerMoments : ∀q∈legalCells menu h, q.length<h →
    histogramMoment (wordAtoms (words L) (tag menu) weight) q * (product q : Int) =
      (↑((L*U)*K):Int)
  occupied : ∀c∈legalCells menu h,0<cellMass (words L) (tag menu) weight c
  signedCells : ∀c∈legalCells menu h,
    (cellMass (words L) (tag menu) weight c:Int) = (K:Int)*
      (exactMass (calibrated menu h
        (table (legalCells menu h) (fun s => U*fiberSize (words L) (tag menu) s))
        (target U L)) c + effect c coef edges)

/-- End-to-end finite arithmetic hard-law constructor. Its hypotheses only
concern the supplied menu, interval, rational amplitude, and distinct
canonical h-edges. Physical rounding and fiber lower bounds are proved. -/
theorem exists_prime_witness (menu : List Nat) (edges : List (List Nat)) (coef : List Nat→Int)
    (P Q L h U d b eps : Nat) (pPos : 0<P) (uPos : 0<U) (hPos : 0<h)
    (epsSmall : eps<b) (multiple : product menu ∣ U)
    (sparse : 4*menu.length≤P) (alphabet : menu.length+1≤Q) (large : 4*Q^h≤L)
    (cap : 4*L<P^(h+1)) (window : 4*b*Q^h ≤ eps*L)
    (ampScale : 4*b*d*Q^h ≤ eps*(L*U))
    (unique : menu.Nodup) (prime : ∀p∈menu,IsPrime p) (odd : ∀p∈menu,p%2=1)
    (lo : ∀p∈menu,P≤p) (hi : ∀p∈menu,p≤Q) (distinct : edges.Nodup)
    (canonical : ∀e∈edges,e.Sublist menu) (degree : ∀e∈edges,e.length=h)
    (amplitudes : ∀e∈edges,(coef e).natAbs≤d) :
    ∃ K weight, LiteralCertificate menu edges coef L h U b eps K weight := by
  have len : (words L).length=L := by simp [words]
  have positiveQ : 0<Q := by omega
  have pospow := Nat.pow_pos positiveQ (n := h)
  have posL : 0<L := by omega
  have comp := complete_tags menu P L h pPos cap unique prime lo
  have fibers := physical_fiber_lower menu P Q L h pPos sparse alphabet large cap unique prime odd lo hi
  have tot : target U L [] = (↑((words L).length*U):Int) := by simp [target,product,len]
  obtain ⟨K,weight,kpos,norm,density,occ,lows,shift⟩ := calibrated_physical_witness (words L)
    (tag menu) menu edges coef (target U L) h d U b eps Q hPos uPos (by simpa [len] using posL)
    epsSmall alphabet unique distinct canonical degree amplitudes comp
    (fun c hc => by simpa [len] using fibers c hc) (by simpa [len] using window)
    (by simpa [len] using ampScale) tot (rounding_one_unit menu L h U multiple unique prime odd comp)
  rw [len] at norm
  simp only [len] at density
  refine ⟨K,weight,kpos,norm,density,?_,occ,shift⟩
  intro q hq small
  rw [lows q hq small]
  have pscale := product_target menu q U L multiple (legal_info hq).1
  change ((K:Int)*(↑(L*(U/product q)):Int))*(product q:Int) = (↑((L*U)*K):Int)
  rw [Int.mul_assoc, ← Int.natCast_mul,pscale, ← Int.natCast_mul,Nat.mul_comm]

/-- A common scale that exactly represents the paper's specified amplitude
eps/(1000*b*(2P)^h), including when its denominator is not a power of two. -/
def paperScale (menu : List Nat) (P h b : Nat) :=
  product menu * (1000*b*(2*P)^h)

def paperAmplitude (menu : List Nat) (L eps : Nat) := eps*L*product menu

def signedCoefficient (d : Nat) (tagSign : List Nat→Bool) (e : List Nat) : Int :=
  if tagSign e then (d:Int) else -(d:Int)

theorem paper_amplitude_exact (menu : List Nat) (P L h b eps : Nat) :
    paperAmplitude menu L eps * (1000*b*(2*P)^h) = eps*(L*paperScale menu P h b) := by
  unfold paperAmplitude paperScale
  ac_rfl

/-- The signed h-edge construction in the hard-menu paragraph of the natural
window theorem. Any assignment of signs is permitted, hence so are signs
shared by all edges carrying the same tail vertex. -/
theorem paper_signed_family (menu : List Nat) (edges : List (List Nat)) (tagSign : List Nat→Bool)
    (P L h b eps : Nat) (pPos : 0<P) (hPos : 0<h) (epsSmall : eps<b)
    (sparse : 4*menu.length≤P) (cap : 4*L<P^(h+1))
    (calibrationWindow : 1000*b*(2*P)^h ≤ eps*L)
    (unique : menu.Nodup) (prime : ∀p∈menu,IsPrime p) (odd : ∀p∈menu,p%2=1)
    (lo : ∀p∈menu,P≤p) (hi : ∀p∈menu,p≤2*P) (distinct : edges.Nodup)
    (canonical : ∀e∈edges,e.Sublist menu) (degree : ∀e∈edges,e.length=h) :
    ∃ K weight, LiteralCertificate menu edges (signedCoefficient (paperAmplitude menu L eps) tagSign)
      L h (paperScale menu P h b) b eps K weight := by
  let Q := 2*P
  let d := paperAmplitude menu L eps
  let U := paperScale menu P h b
  have bPos : 0<b := by omega
  have powPos : 0<Q^h := Nat.pow_pos (by dsimp [Q]; omega)
  have uPos : 0<U := Nat.mul_pos (product_positive menu odd)
    (Nat.mul_pos (Nat.mul_pos (by decide) bPos) powPos)
  have mult : product menu ∣ U := Nat.dvd_mul_right _ _
  have coeffLe : 4*b*Q^h ≤ 1000*b*Q^h :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  have window : 4*b*Q^h≤eps*L := Nat.le_trans coeffLe calibrationWindow
  have large : 4*Q^h≤L := by
    apply Nat.le_of_mul_le_mul_left _ bPos
    calc
      b*(4*Q^h) = 4*b*Q^h := by ac_rfl
      _ ≤ eps*L := window
      _ ≤ b*L := Nat.mul_le_mul_right L (Nat.le_of_lt epsSmall)
  have ampl : 4*b*d*Q^h≤eps*(L*U) := by
    calc
      _ = d*(4*b*Q^h) := by ac_rfl
      _ ≤ d*(1000*b*Q^h) := Nat.mul_le_mul_left d coeffLe
      _ = _ := paper_amplitude_exact menu P L h b eps
  exact exists_prime_witness menu edges _ P Q L h U d b eps pPos uPos hPos epsSmall mult
    sparse (by dsimp [Q]; omega) large cap window ampl unique prime odd lo hi distinct canonical
    degree (fun e _ => by cases hs : tagSign e <;> simp [signedCoefficient,hs,d])

end Screening.PrimeIntervalWitness
