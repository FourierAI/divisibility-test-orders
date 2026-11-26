import Screening.OneHitInversion

/-! Common whole-menu public priorities and the projection to a fixed pivot.
Labels are natural numbers. A partition is supplied as consecutive blocks in
reference order; the actual record is a single globally labeled first hit. -/
namespace Screening.GlobalOneHit

open Screening.OneHitInversion

def readBits : (labels : List Nat) → (Nat → Bool) → Mask labels.length
  | [],_ => ()
  | i::is,g => (g i,readBits is g)

def writeBit (g : Nat → Bool) (i : Nat) (b : Bool) : Nat → Bool :=
  fun j => if j=i then b else g j

private theorem read_unaffected (xs : List Nat) (g : Nat → Bool) (i : Nat) (b : Bool)
    (h : i ∉ xs) : readBits xs (writeBit g i b) = readBits xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hn : x≠i := by intro e; apply h; simp [e]
    have ht : i∉xs := fun hm => h (by simp [hm])
    simp [readBits,writeBit,hn,ih ht]

/-- Full public sign sum. Each location independently contributes both
public coins and an unassigned location defaults to false. -/
def fair : List Nat → ((Nat → Bool) → Int) → Int
  | [],f => f (fun _ => false)
  | i::is,f => fair is (fun g => f (writeBit g i false)) +
                fair is (fun g => f (writeBit g i true))

private theorem fair_constant (xs : List Nat) (c : Int) :
    fair xs (fun _ => c) = 2^xs.length*c := by
  induction xs with
  | nil => simp [fair]
  | cons x xs ih =>
    have h2 : 2*c=c+c := by omega
    simp only [fair,ih,List.length_cons,Int.pow_succ,Int.mul_assoc,h2,Int.mul_add]

private theorem active_coins (active post : List Nat) (hd : active.Nodup)
    (f : Mask active.length → Int) :
    fair (active++post) (fun g => f (readBits active g)) =
      (2:Int)^post.length*cubeSum active.length f := by
  induction active with
  | nil => simp only [List.nil_append,List.length_nil,readBits,cubeSum,fair_constant]
  | cons i is ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hd
    simp only [List.cons_append,fair,readBits,read_unaffected is _ i _ hn]
    have self (g : Nat→Bool) (b : Bool) : writeBit g i b i = b := by simp [writeBit]
    simp only [self,List.length_cons,cubeSum,Int.mul_add]
    rw [ih ht (fun t => f (false,t)),ih ht (fun t => f (true,t))]

/-- Exact marginal under a uniform global mark mask for any contiguous
window. Every configuration on the window occurs equally often. -/
theorem fair_window (pre active post : List Nat) (hd : (pre++active++post).Nodup)
    (f : Mask active.length → Int) :
    fair (pre++active++post) (fun g => f (readBits active g)) =
      (2:Int)^(pre.length+post.length)*cubeSum active.length f := by
  induction pre with
  | nil =>
    have ha : active.Nodup := (List.pairwise_append.mp (by simpa using hd)).1
    simpa using active_coins active post ha f
  | cons x xs ih =>
    have hh : (x::(xs++active++post)).Nodup := hd
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hh
    have ha : x ∉ active := fun h => hn (by simp [List.mem_append,h])
    change (fair (xs++active++post) (fun g => f (readBits active (writeBit g x false)))) +
      (fair (xs++active++post) (fun g => f (readBits active (writeBit g x true)))) = _
    simp only [read_unaffected active _ x _ ha, ih ht]
    have exp : (x::xs).length+post.length=(xs.length+post.length)+1 := by simp; omega
    rw [exp,Int.pow_succ,Int.mul_assoc]
    have hh : 2*cubeSum active.length f=cubeSum active.length f+cubeSum active.length f := by omega
    rw [hh,Int.mul_add]

def priority (block : List Nat) (mark : Nat → Bool) :=
  block.filter mark ++ block.filter (fun i => !mark i)

def allPriorities (blocks : List (List Nat)) (mark : Nat → Bool) :=
  blocks.flatMap (fun block => priority block mark)

def firstHit (blocks : List (List Nat)) (mark hit : Nat → Bool) : Option Nat :=
  (allPriorities blocks mark).find? hit

/-- The physical location of a fixed j inside one of the two partitions. -/
structure Split where
  before : List (List Nat)
  left : List Nat
  j : Nat
  right : List Nat
  after : List (List Nat)

def Split.blocks (x : Split) := x.before ++ [x.left++[x.j]++x.right] ++ x.after
def Split.pre (x : Split) := x.before.flatten ++ x.left
def Split.post (x : Split) := x.after.flatten
def Split.menu (x : Split) := x.pre ++ (x.j::x.right) ++ x.post

private def tests (labels : List Nat) (mark hit : Nat→Bool) :=
  labels.map fun i => (hit i,mark i)

private def tag (j : Nat) (mark hit : Nat→Bool) (i : Nat) : Test :=
  ⟨i==j,mark i,hit i⟩

private theorem filter_map {α β : Type} (xs : List α) (f : α→β) (p : β→Bool) :
    (xs.map f).filter p = (xs.filter (fun x => p (f x))).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p (f x) <;> simp [List.filter_cons,h,ih]

private theorem mark_map (block : List Nat) (j : Nat) (mark hit : Nat→Bool) :
    (priority block mark).map (tag j mark hit) = markedFirst (block.map (tag j mark hit)) := by
  simp [priority,markedFirst,filter_map,tag]

private theorem scan_tag (xs : List Nat) (j : Nat) (mark hit : Nat→Bool) :
    scan (xs.map (tag j mark hit)) = (xs.find? hit).map (fun i => i==j) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : hit x <;> simp [tag,scan,h,List.find?_cons,ih]

private theorem others (xs : List Nat) (j : Nat) (mark hit : Nat→Bool) (hn : j∉xs) :
    (tests xs mark hit).map ordinary = xs.map (tag j mark hit) := by
  simp only [tests,List.map_map]
  apply List.map_congr_left
  intro x hx
  have hne : x≠j := fun e => hn (e ▸ hx)
  simp [tag,ordinary,Function.comp_def,hne]

private theorem slots_read (xs : List Nat) (mark hit : Nat→Bool) :
    slots xs.length (readBits xs hit) (readBits xs mark) = tests xs mark hit := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [readBits,slots,tests] at ih ⊢; exact ih

private theorem priority_mem (blocks : List (List Nat)) (mark : Nat→Bool) (i : Nat) :
    i ∈ allPriorities blocks mark ↔ i∈blocks.flatten := by
  simp only [allPriorities,priority,List.mem_flatMap,List.mem_flatten,List.mem_append,List.mem_filter]
  constructor
  · rintro ⟨b,hb,h|h⟩ <;> exact ⟨b,hb,h.1⟩
  · rintro ⟨b,hb,hi⟩
    exact ⟨b,hb, by cases he : mark i <;> simp [he,hi]⟩

private theorem clear_tests (xs : List Nat) (mark hit : Nat→Bool) :
    clear (tests xs mark hit) = !xs.any hit := by
  simp [clear,tests,List.any_map,Function.comp_def]

private theorem prior_any (blocks : List (List Nat)) (mark hit : Nat→Bool) :
    (allPriorities blocks mark).any hit = blocks.flatten.any hit := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,priority_mem]

private theorem safety {x : Split} (hd : x.menu.Nodup) :
    x.j∉x.before.flatten ∧ x.j∉x.left ∧ x.j∉x.right ∧ x.j∉x.after.flatten := by
  have h : (x.pre ++ ((x.j::x.right)++x.post)).Nodup := by simpa [Split.menu,List.append_assoc] using hd
  obtain ⟨_,hrest,hdis⟩ := List.pairwise_append.mp h
  have member : x.j ∈ (x.j::x.right)++x.post := by simp
  have hpre : x.j ∉ x.pre := fun h => hdis x.j h x.j member rfl
  have hn : x.j ∉ x.right++x.post := (List.nodup_cons.mp hrest).1
  simp only [Split.pre,List.mem_append,not_or] at hpre
  simp only [Split.post,List.mem_append,not_or] at hn
  exact ⟨hpre.1,hpre.2,hn⟩

/-- Relabeling the globally returned result "is it j?" gives exactly the
local operational stopped scan. The value of no other observation is used. -/
theorem exact_global_log (x : Split) (hd : x.menu.Nodup) (mark hit : Nat→Bool) :
    (firstHit x.blocks mark hit).map (fun i => i==x.j) =
      stopped (tests (allPriorities x.before mark) mark hit)
        (tests x.left mark hit) (tests x.right mark hit)
        (tests (allPriorities x.after mark) mark hit) (hit x.j) (mark x.j) := by
  obtain ⟨hpre,hl,hr,hpost⟩ := safety hd
  have hb : x.j∉allPriorities x.before mark := fun h => hpre ((priority_mem _ _ _).mp h)
  have ha : x.j∉allPriorities x.after mark := fun h => hpost ((priority_mem _ _ _).mp h)
  rw [firstHit,←scan_tag _ x.j mark hit]
  simp only [Split.blocks,allPriorities,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.map_append,mark_map,List.map_cons,List.map_nil]
  unfold stopped
  simp only [allPriorities] at hb ha
  rw [others _ x.j mark hit hb,others _ x.j mark hit hl,others _ x.j mark hit hr,others _ x.j mark hit ha]
  simp [allPriorities,tag,List.append_assoc]

/-- The fixed local row uses the underlying hit bits only. Its natural-minimum
event is independent of all public marks in earlier blocks and before j. -/
def localWord (x : Split) (hit : Nat→Bool) : Word x.right.length :=
  ⟨tests x.before.flatten (fun _ => false) hit,tests x.left (fun _ => false) hit,
   hit x.j,readBits x.right hit,[]⟩

theorem global_negative (x : Split) (hd : x.menu.Nodup) (mark hit : Nat → Bool)
    (negative : mark x.j=false) :
    firstHit x.blocks mark hit = some x.j ↔
      (eligible (localWord x hit) && noPositiveHit (tests x.right mark hit)) = true := by
  have he := exact_global_log x hd mark hit
  rw [negative] at he
  have h := negative_first (tests (allPriorities x.before mark) mark hit)
    (tests x.left mark hit) (tests x.right mark hit)
    (tests (allPriorities x.after mark) mark hit) (hit x.j)
  rw [←he] at h
  simp only [localWord,eligible,clear_tests,prior_any] at h ⊢
  rw [←h]
  cases v : firstHit x.blocks mark hit with
  | none => simp
  | some j => simp [beq_iff_eq]

/-- One table per pivot, evaluated only from the globally returned index,
chosen partition and publicly visible marks. -/
def feature (x : Split) (selected : Bool) (c : Mask x.right.length → Int)
    (coin : Bool) (marks : Nat→Bool) (Y : Option Nat) : Int :=
  linearLog x.right.length c (readBits x.right marks) (coin==selected) (marks x.j)
    (Y.map (fun i => i==x.j))

private theorem flagged (y : Option Nat) (j : Nat) :
    y.map (fun i => i==j) = some true ↔ y=some j := by
  cases y <;> simp [beq_iff_eq]

private theorem proj_negative (x : Split) (hd : x.menu.Nodup) (m h : Nat→Bool)
    (hn : m x.j=false) :
    ((firstHit x.blocks m h).map (fun i => i==x.j) = some true) ↔
      stopped (localWord x h).before (localWord x h).left
        (slots x.right.length (localWord x h).tailHits (readBits x.right m))
        (localWord x h).after (localWord x h).pivotHit false = some true := by
  rw [flagged,global_negative x hd m h hn,negative_first]
  simp only [localWord,eligible,slots_read]

theorem global_feature_eq (x : Split) (hd : x.menu.Nodup) (selected : Bool)
    (plans : Bool→List (List Nat)) (hx : plans selected=x.blocks)
    (h m : Nat→Bool) (c : Mask x.right.length→Int) (coin : Bool) :
    feature x selected c coin m (firstHit (plans coin) m h) =
      linearLog x.right.length c (readBits x.right m) (coin==selected) (m x.j)
        (observed (localWord x h) (fun _ _ => none) (coin==selected) (m x.j) (readBits x.right m)) := by
  unfold feature
  rw [observed_linear,observed_linear]
  by_cases eq : coin=selected
  · subst coin
    cases hn : m x.j with
    | true => simp
    | false =>
      have hg := proj_negative x hd m h hn
      by_cases hglo : (firstHit x.blocks m h).map (fun i => i==x.j) = some true
      · simp [hx,observed,hglo,hg.mp hglo]
      · have hl := fun hl => hglo (hg.mpr hl)
        simp [hx,observed,hglo]; rw [if_neg hl]
  · have beq : (coin==selected)=false := by cases coin <;> cases selected <;> simp_all
    simp [beq]

def globalIntegral (menu : List Nat) (F : Bool → (Nat→Bool) → Int) :=
  fair menu (F false) + fair menu (F true)

private theorem partition_coins (d : Nat) (selected : Bool) (f : Bool→Bool→Mask d→Int) :
    cubeSum (d+1) (fun t => f (false==selected) t.1 t.2) +
    cubeSum (d+1) (fun t => f (true==selected) t.1 t.2) = integrateMarks d f := by
  cases selected <;> simp [cubeSum,integrateMarks,cube_add] <;> ac_rfl

/-- Exact marginalization for *any* integer statistic g of the first-hit
field on a full global record. All assignments on labels outside the
window are summed, not assumed independent after observing the hit. -/
theorem global_projection (x : Split) (hd : x.menu.Nodup) (selected : Bool)
    (plans : Bool → List (List Nat)) (hx : plans selected=x.blocks)
    (hit : Nat→Bool) (c : Mask x.right.length→Int) (g : Int→Int) :
    globalIntegral x.menu (fun coin mark =>
      g (feature x selected c coin mark (firstHit (plans coin) mark hit))) =
    (2:Int)^(x.pre.length+x.post.length)*integrateMarks x.right.length
      (fun a b s => g (linearLog x.right.length c s a b
        (observed (localWord x hit) (fun _ _ => none) a b s))) := by
  let d := x.right.length
  let f := fun a b (s : Mask d) => g (linearLog d c s a b
    (observed (localWord x hit) (fun _ _ => none) a b s))
  have branch (coin : Bool) :
      fair x.menu (fun mark => g (feature x selected c coin mark (firstHit (plans coin) mark hit))) =
      2^(x.pre.length+x.post.length)*cubeSum (d+1) (fun z => f (coin==selected) z.1 z.2) := by
    simp only [global_feature_eq x hd selected plans hx]
    exact fair_window x.pre (x.j::x.right) x.post hd (fun z => f (coin==selected) z.1 z.2)
  rw [globalIntegral,branch,branch,←Int.mul_add,partition_coins]

structure Record where
  partition : Bool
  marks : Nat → Bool
  first : Option Nat

/-- Enumerate both public settings of *every* coordinate of the full menu. -/
def enumerate {α : Type} : List Nat → ((Nat→Bool)→α) → List α
  | [],f => [f (fun _ => false)]
  | i::is,f => enumerate is (fun g => f (writeBit g i false)) ++
      enumerate is (fun g => f (writeBit g i true))

private theorem enumerate_sum {α : Type} (xs : List Nat) (f : (Nat→Bool)→α) (g : α→Int) :
    sumOn (enumerate xs f) g = fair xs (fun m => g (f m)) := by
  induction xs generalizing f with
  | nil => simp [enumerate,fair,sumOn]
  | cons i is ih => rw [enumerate,sum_append,ih,ih,fair]

/-- The full experiment uses one shared sign mask and one partition coin
per word; the data available afterwards contain just one globally labeled hit. -/
def records (menu : List Nat) (plans : Bool→List (List Nat)) (law : List (Nat→Bool)) : List Record :=
  law.flatMap fun hit =>
    let record := fun b m => Record.mk b m (firstHit (plans b) m hit)
    enumerate menu (record false) ++ enumerate menu (record true)

theorem records_sum (menu : List Nat) (plans : Bool→List (List Nat)) (law : List (Nat→Bool))
    (g : Record→Int) :
    sumOn (records menu plans law) g = sumOn law (fun hit => globalIntegral menu
      (fun b m => g ⟨b,m,firstHit (plans b) m hit⟩)) := by
  rw [records,sum_flatMap]
  congr 1; funext hit
  rw [sum_append,enumerate_sum,enumerate_sum,globalIntegral]

private theorem sum_scalar {α : Type} (xs : List α) (k : Int) (f : α→Int) :
    sumOn xs (fun x => k*f x) = k*sumOn xs f := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    change k*f x+sumOn xs _ = k*(f x+sumOn xs _)
    rw [ih,Int.mul_add]

/-- Every pivot's local marginal on the *same* explicitly enumerated full
records agrees with its stopped local construction, including all multiplicities. -/
theorem record_projection (x : Split) (hd : x.menu.Nodup) (selected : Bool)
    (plans : Bool → List (List Nat)) (hx : plans selected=x.blocks)
    (law : List (Nat→Bool)) (c : Mask x.right.length→Int) (g : Int→Int) :
    sumOn (records x.menu plans law) (fun rec =>
      g (feature x selected c rec.partition rec.marks rec.first)) =
    (2:Int)^(x.pre.length+x.post.length)*sumOn law (fun hit => integrateMarks x.right.length
      (fun a b s => g (linearLog x.right.length c s a b
        (observed (localWord x hit) (fun _ _ => none) a b s)))) := by
  rw [records_sum]
  simp only [global_projection x hd selected plans hx,sum_scalar]

/-- Number of joint public partition/mark outcomes. -/
def choices (m : Nat) := 2*2^m

private theorem choices_window (x : Split) :
    choices x.menu.length = 2^(x.pre.length+x.post.length)*(4*2^x.right.length) := by
  unfold choices Split.menu
  simp only [List.length_append,List.length_cons,Nat.pow_add,Nat.pow_one]
  change 2*(2^x.pre.length*(2^x.right.length*2)*2^x.post.length) =
    2^x.pre.length*2^x.post.length*((2*2)*2^x.right.length)
  ac_rfl

private theorem align (d K : Nat) (h : d≤K) : 2^(K-d)*2^d=2^K := by
  rw [← Nat.pow_add]; congr 1; omega

private theorem norm_mean (x : Split) (K : Nat) (hd : x.right.length≤K) :
    (2^(K-x.right.length)*2^(x.pre.length+x.post.length))*(4*4^x.right.length) =
    choices x.menu.length*2^K := by
  let d := x.right.length
  rw [choices_window,←align d K hd,show 4^d=2^d*2^d from Nat.mul_pow 2 2 d]
  ac_rfl

private theorem norm_energy (x : Split) (K : Nat) (hd : x.right.length≤K) (count rest : Nat) :
    (2^(K-x.right.length)*2^(K-x.right.length))*
      (2^(x.pre.length+x.post.length)*(16*count*(2^x.right.length*(4^x.right.length*rest)))) =
    choices x.menu.length*4*(4^K)*count*rest := by
  let d := x.right.length
  rw [choices_window,show 4^K=2^K*2^K from Nat.mul_pow 2 2 K,←align d K hd,
    show 4^d=2^d*2^d from Nat.mul_pow 2 2 d]
  change _*(_*((4*4)*count*(_*(_*rest)))) = _
  ac_rfl

private theorem mapped_sum {α β : Type} (xs : List α) (u : α→β) (v : β→Int) :
    sumOn (xs.map u) v = sumOn xs (fun x => v (u x)) := by
  simp [sumOn,List.map_map,Function.comp_def]

private theorem sum_constant {α : Type} (xs : List α) (c : Int) :
    sumOn xs (fun _ => c) = (xs.length:Int)*c := sum_const xs c

theorem record_size (menu : List Nat) (plans : Bool→List (List Nat)) (law : List (Nat→Bool)) :
    (records menu plans law).length = law.length*choices menu.length := by
  have h := records_sum menu plans law (fun _=>1)
  simp only [sum_constant,Int.mul_one,globalIntegral,fair_constant] at h
  have e : ((records menu plans law).length:Int) = ((law.length*choices menu.length:Nat):Int) := by
    rw [h]
    unfold choices
    simp only [Int.natCast_mul,Int.natCast_pow,Int.cast_ofNat_Int,Int.mul_one]
    congr 1; omega
  omega

private theorem energy_sum (vs : List Int) : (SampleVariance.energy vs : Int)=sumOn vs (fun z=>z*z) := by
  induction vs with
  | nil => rfl
  | cons z zs ih =>
    change ((z.natAbs*z.natAbs+SampleVariance.energy zs:Nat):Int)=z*z+sumOn zs _
    rw [Int.natCast_add,Int.natAbs_mul_self,ih]

private theorem scale_energy {α : Type} (rows : List α) (f : α→Int) (k : Nat) :
    SampleVariance.energy (rows.map (fun r => (k:Int)*f r)) =
    (k*k)*SampleVariance.energy (rows.map f) := by
  induction rows with
  | nil => simp [SampleVariance.energy]
  | cons r rs ih =>
    simp only [List.map_cons,SampleVariance.energy,Int.natAbs_mul,Int.natAbs_ofNat,ih,Nat.mul_add]
    ac_rfl

structure Pivot (menu : List Nat) (plans : Bool→List (List Nat)) where
  window : Split
  selected : Bool
  menu_eq : window.menu=menu
  plan_eq : plans selected=window.blocks

/-- Local values all have the same interpretation after division by 2^K,
even if a menu end shortens some blocks. -/
def value {menu plans} (p : Pivot menu plans) (K h : Nat) (f : Mask p.window.right.length→Int)
    (rec : Record) : Int :=
  ((2^(K-p.window.right.length):Nat):Int) *
  feature p.window p.selected (limited _ h (coefficient _ f)) rec.partition rec.marks rec.first

def minCount (x : Split) (law : List (Nat→Bool)) : Nat :=
  law.countP (fun hit => eligible (localWord x hit))

theorem actual_pivot_mean {menu plans} (p : Pivot menu plans) (hn : menu.Nodup) (K h : Nat)
    (hd : p.window.right.length≤K) (f : Mask p.window.right.length→Int) (law : List (Nat→Bool))
    (hcap : ∀ z ∈ law, eligible (localWord p.window z)=true → weight _ (readBits p.window.right z) ≤ h) :
    sumOn (records menu plans law) (value p K h f) =
    ((choices menu.length*2^K:Nat):Int)*sumOn law (fun hit =>
      if eligible (localWord p.window hit) then f (readBits p.window.right hit) else 0) := by
  let x := p.window
  let d := x.right.length
  let c := limited d h (coefficient d f)
  have hdw : x.menu.Nodup := p.menu_eq ▸ hn
  have local_mean : sumOn law (fun hit => integrateMarks d (fun a b s =>
      linearLog d c s a b (observed (localWord x hit) (fun _ _ => none) a b s))) =
      (4*(4:Int)^d)*sumOn law (fun hit =>
        if eligible (localWord x hit) then f (readBits x.right hit) else 0) := by
    induction law with
    | nil => simp [sumOn]
    | cons z zs ih =>
      change integrateMarks d _ + sumOn zs _ = _*((if eligible (localWord x z) then f (readBits x.right z) else 0)+sumOn zs _)
      rw [show integrateMarks d (fun a b s => linearLog d c s a b
        (observed (localWord x z) (fun _ _ => none) a b s)) = _ from
        capped_when_eligible d h f (localWord x z) (hcap z (by simp)) (fun _ _ => none)]
      rw [ih (fun z hz => hcap z (by simp [hz])),Int.mul_add]
      rfl
  have joined : ∀ z : Int,
      ((2^(K-d):Nat):Int)*((2:Int)^(x.pre.length+x.post.length)*(4*4^d*z)) =
      ((choices menu.length*2^K:Nat):Int)*z := by
    intro z
    rw [←p.menu_eq,←norm_mean x K hd]
    dsimp only [d]; simp only [Int.natCast_mul,Int.natCast_pow,Int.cast_ofNat_Int]; ac_rfl
  have hr := record_projection x hdw p.selected plans p.plan_eq law c id
  have hmenu : x.menu=menu := p.menu_eq
  simp only [id_eq,hmenu] at hr
  unfold value
  rw [sum_scalar]
  change ((2^(K-d):Nat):Int)*sumOn (records menu plans law) (fun r => feature x p.selected c r.partition r.marks r.first) = _
  rw [hr,local_mean,joined]

theorem actual_pivot_energy {menu plans} (p : Pivot menu plans) (hn : menu.Nodup) (K h : Nat)
    (hd : p.window.right.length≤K) (f : Mask p.window.right.length→Int) (hf : ∀ s, (f s).natAbs≤1)
    (law : List (Nat→Bool)) :
    SampleVariance.energy ((records menu plans law).map (value p K h f)) ≤
      choices menu.length*4*4^K*minCount p.window law*(9^h*(K+1)^h) := by
  let x := p.window
  let d := x.right.length
  let c := limited d h (coefficient d f)
  let loc :=  localWord x
  let rows := records menu plans law
  let F := fun r : Record => feature x p.selected c r.partition r.marks r.first
  have hdw : x.menu.Nodup := p.menu_eq ▸ hn
  have hr := record_projection x hdw p.selected plans p.plan_eq law c (fun v => v*v)
  have hmenu : x.menu=menu := p.menu_eq
  rw [hmenu] at hr
  have hb := bounded_population_second_moment d h f hf (law.map loc) (fun _ _ _ => none)
  rw [mapped_sum] at hb
  have ce : (law.map loc).countP eligible = minCount x law := by simp [minCount,loc,List.countP_map,Function.comp_def]
  rw [ce] at hb
  have raw : SampleVariance.energy (rows.map F) ≤
      2^(x.pre.length+x.post.length)*(16*minCount x law*(2^d*(4^d*(9^h*(d+1)^h)))) := by
    apply Int.ofNat_le.mp
    rw [energy_sum,mapped_sum,hr]
    have bound := Int.mul_le_mul_of_nonneg_left hb (Int.pow_nonneg (m:=x.pre.length+x.post.length) (n:=2) (by decide))
    simpa only [Int.natCast_mul,Int.natCast_pow,Int.cast_ofNat_Int,Int.mul_assoc] using bound
  change SampleVariance.energy (rows.map (fun r => ((2^(K-d):Nat):Int)*F r)) ≤ _
  rw [scale_energy]
  apply Nat.le_trans (Nat.mul_le_mul_left _ raw)
  rw [norm_energy x K hd,p.menu_eq]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) h))

theorem weight_read (labels : List Nat) (hit : Nat→Bool) :
    weight labels.length (readBits labels hit) = labels.countP hit := by
  induction labels with
  | nil => rfl
  | cons i is ih =>
    simp only [readBits,List.length_cons,weight,List.countP_cons,ih]

theorem eligible_minimum (x : Split) (hit : Nat → Bool) :
    eligible (localWord x hit) = (!x.pre.any hit && hit x.j) := by
  simp only [eligible,localWord,clear_tests,Split.pre,List.any_append,Bool.not_or]

theorem window_cap {menu plans} (p : Pivot menu plans) (z : Nat → Bool) (h : Nat)
    (cap : menu.countP z ≤ h+1) (emin : eligible (localWord p.window z)=true) :
    weight p.window.right.length (readBits p.window.right z) ≤ h := by
  rw [eligible_minimum] at emin
  have hj : z p.window.j = true := by cases he : z p.window.j <;> simp_all
  rw [←p.menu_eq] at cap
  simp only [Split.menu,List.countP_append,List.countP_cons,hj,if_true] at cap
  rw [weight_read]; omega

/-- Finite scalar prefix specification. Each registered index is the pivot
of its supplied concrete split in the selected partition. -/
structure Fields (menu : List Nat) (plans : Bool→List (List Nat)) where
  live : List Nat
  distinct : live.Nodup
  pivot : Nat → Pivot menu plans
  label : ∀ j ∈ live, (pivot j).window.j=j
  payoff : (j : Nat) → Mask (pivot j).window.right.length → Int
  bounded : ∀ j ∈ live, ∀ z, ((payoff j) z).natAbs ≤ 1

def coordinate {menu plans} (F : Fields menu plans) (K h j : Nat) (r : Record) : Int :=
  value (F.pivot j) K h (F.payoff j) r

def observedScore {menu plans} (F : Fields menu plans) (K h : Nat) (r : Record) : Int :=
  sumOn F.live (fun j => coordinate F K h j r)

def truth {menu plans} (F : Fields menu plans) (hit : Nat→Bool) : Int :=
  sumOn F.live fun j =>
    let x := (F.pivot j).window
    if eligible (localWord x hit) then F.payoff j (readBits x.right hit) else 0

private theorem not_reported {menu plans} (p : Pivot menu plans) (K h : Nat)
    (f : Mask p.window.right.length→Int) (r : Record) (hn : r.first≠some p.window.j) :
    value p K h f r=0 := by
  have hflag := fun hh => hn ((flagged r.first p.window.j).mp hh)
  unfold value feature
  rw [observed_linear]
  simp [hflag,hn]

private theorem coordinate_is_projected {menu plans} (F : Fields menu plans) (K h j : Nat)
    (hj : j∈F.live) (r : Record) :
    projection Record.first (coordinate F K h) j r = coordinate F K h j r := by
  unfold projection
  split
  · rfl
  · rename_i hn
    exact (not_reported _ _ _ _ _ (by rwa [F.label j hj])).symm

private theorem scores_shared {menu plans} (F : Fields menu plans) (K h : Nat) (rs : List Record) :
    sharedTickets rs F.live Record.first (coordinate F K h) = rs.map (observedScore F K h) := by
  unfold sharedTickets observedScore
  apply List.map_congr_left
  intro r _
  unfold sumOn
  congr 1
  apply List.map_congr_left
  intro j hj; exact coordinate_is_projected F K h j hj r

private theorem swap {α β : Type} (xs : List α) (ys : List β) (f : α→β→Int) :
    sumOn xs (fun x => sumOn ys (f x)) = sumOn ys (fun y => sumOn xs (fun x => f x y)) := by
  have add {γ : Type} (us : List γ) (a b : γ→Int) :
      sumOn us (fun z => a z+b z)=sumOn us a+sumOn us b := by
    induction us with
    | nil => rfl
    | cons z zs ih =>
      change a z+b z+sumOn zs _=(a z+sumOn zs a)+(b z+sumOn zs b)
      rw [ih]; ac_rfl
  induction xs with
  | nil => change 0 = sumOn ys (fun _ => 0); rw [sum_constant,Int.mul_zero]
  | cons x xs ih =>
    change sumOn ys (f x)+sumOn xs _ = sumOn ys (fun y=>f x y+sumOn xs _)
    rw [add,ih]

/-- Mean of a whole prefix score on the common full records, using only the
total hit cap on each original word. The common numerator scale is 2^K. -/
theorem actual_prefix_mean {menu plans} (F : Fields menu plans) (hn : menu.Nodup) (K h : Nat)
    (hwidth : ∀ j ∈ F.live, (F.pivot j).window.right.length ≤ K) (law : List (Nat→Bool))
    (cap : ∀ z ∈ law, menu.countP z ≤ h+1) :
    sumOn (records menu plans law) (observedScore F K h) =
      ((choices menu.length*2^K:Nat):Int)*sumOn law (truth F) := by
  unfold observedScore truth
  rw [swap,swap law,←sum_scalar]
  unfold sumOn
  congr 1
  apply List.map_congr_left
  intro j hj
  exact actual_pivot_mean (F.pivot j) hn K h (hwidth j hj) (F.payoff j) law
    (fun z hz => window_cap _ z h (cap z hz))

/-- Full-prefix block concentration from one globally logged label per word.
The sufficient sample inequality uses the frequency Q/law.length, the
number of active minima, and (K+1)^h. It has no assumption about the energy
or unbiasedness of the projections, which were derived above. -/
theorem actual_prefix_block {menu plans} (F : Fields menu plans) (hnodup : menu.Nodup)
    (K h : Nat) (hwidth : ∀ j ∈ F.live, (F.pivot j).window.right.length≤K)
    (law : List (Nat→Bool)) {N Q a D : Nat} (hn : 0<N) (ha : 0<a) (hD : 0<D)
    (hK : 0<law.length) (hq : ∀ j ∈ F.live, minCount (F.pivot j).window law ≤ Q)
    (hsize : 16*D*D*F.live.length*Q*(9^h*(K+1)^h) ≤ law.length*N*a*a) :
    let rs := records menu plans law
    let scores := rs.map (observedScore F K h)
    let blocks := SampleVariance.sampleSums (SampleVariance.centered scores) N
    3*blocks.length ≤ 4*SampleVariance.goodCount blocks (N*(scores.length*(2^K*a))) D := by
  let rs := records menu plans law
  let B := choices menu.length*4*4^K*Q*(9^h*(K+1)^h)
  have hb (j : Nat) (hj : j∈F.live) :
      SampleVariance.energy (rs.map (projection Record.first (coordinate F K h) j)) ≤ B := by
    have hmap : rs.map (projection Record.first (coordinate F K h) j)=rs.map (coordinate F K h j) :=
      List.map_congr_left (fun r _ => coordinate_is_projected F K h j hj r)
    rw [hmap]
    apply Nat.le_trans (actual_pivot_energy (F.pivot j) hnodup K h (hwidth j hj) (F.payoff j)
      (F.bounded j hj) law)
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hq j hj))
  have hr : rs.length = law.length*choices menu.length := record_size _ _ _
  have hrows : 0<rs.length := hr ▸ Nat.mul_pos hK (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
  have hbudget : 4*(D*D*(F.live.length*B)) ≤ rs.length*N*(2^K*a)*(2^K*a) := by
    rw [hr]
    calc _ = (choices menu.length*4^K)*(16*D*D*F.live.length*Q*(9^h*(K+1)^h)) := by
            dsimp only [B]; change (4*_) = (_*((4*4)*_*_*_*_*_)); ac_rfl
         _ ≤ (choices menu.length*4^K)*(law.length*N*a*a) := Nat.mul_le_mul_left _ hsize
         _ = _ := by rw [show 4^K=2^K*2^K from Nat.mul_pow 2 2 K]; ac_rfl
  have result := shared_block_guarantee rs F.live F.distinct Record.first (coordinate F K h)
    hb hrows hn (Nat.mul_pos (Nat.pow_pos (by decide)) ha) hD hbudget
  simpa only [scores_shared F K h rs] using result

/-- Enumerate independent raw records, in the order used by the convolution.
The same block is fed to every candidate prefix. -/
def rawBlocks {α : Type} (law : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => (rawBlocks law n).flatMap fun tail => law.map (fun r=>r::tail)

theorem raw_blocks_sums {α : Type} (law : List α) (f : α→Int) (n : Nat) :
    (rawBlocks law n).map (fun row=>sumOn row f) = SampleVariance.sampleSums (law.map f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rawBlocks,SampleVariance.sampleSums,SampleVariance.convolve,←ih,List.map_flatMap,
      List.flatMap_map,List.map_map,Function.comp_def]
    congr 1
    funext row
    apply List.map_congr_left; intro r _
    exact Int.add_comm _ _

theorem raw_block_length {α : Type} {law : List α} {n : Nat} {row : List α}
    (h : row∈rawBlocks law n) : row.length=n := by
  induction n generalizing row with
  | zero => simpa [rawBlocks] using h
  | succ n ih =>
    obtain ⟨tail,ht,hr⟩ := List.mem_flatMap.mp h
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    simp [ih ht]

private theorem weights_map {α : Type} (rs : List α) (f : α→Int) :
    SampleVariance.weightedSum id (rs.map f)=sumOn rs f := by
  induction rs with
  | nil => rfl
  | cons r rs ih => change f r+SampleVariance.weightedSum id (rs.map f)=f r+sumOn rs f; rw [ih]

/-- The population center occurs only in the accuracy event; the learned
quantity on a raw block is the sum of observable scores. -/
def centeredBlock {α : Type} (rs : List α) (f : α→Int) (block : List α) : Int :=
  (rs.length:Int)*sumOn block f-(block.length:Int)*sumOn rs f

private theorem centered_map {α : Type} (rs : List α) (f : α→Int) (N : Nat) :
    (rawBlocks rs N).map (centeredBlock rs f) =
      SampleVariance.sampleSums (SampleVariance.centered (rs.map f)) N := by
  let centered := fun r => (rs.length:Int)*f r-sumOn rs f
  have hsum (row : List α) : centeredBlock rs f row = sumOn row centered := by
    induction row with
    | nil => simp [centeredBlock,sumOn]
    | cons r row ih =>
      change (rs.length:Int)*(f r+sumOn row f)-(row.length+1:Int)*sumOn rs f =
        centered r+sumOn row centered
      rw [←ih]; unfold centeredBlock centered
      rw [Int.mul_add,Int.add_mul,Int.one_mul]; omega
  have ce : SampleVariance.centered (rs.map f) = rs.map centered := by
    simp [SampleVariance.centered,List.map_map,Function.comp_def,weights_map,centered]
  rw [ce,←raw_blocks_sums]
  exact List.map_congr_left (fun row _ => hsum row)

private theorem good_plus_bad (xs : List Int) (t d : Nat) :
    SampleVariance.goodCount xs t d + SampleVariance.badCount xs t d=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [SampleVariance.goodCount,SampleVariance.badCount,List.countP_cons,decide_eq_true_eq,
      List.length_cons] at ih ⊢
    split <;> split <;> omega

/-- Observable block sum versus its population mean, expressed by exact
integer cross multiplication. -/
def badBlock {menu plans} (rs : List Record) (K h N a D : Nat) (F : Fields menu plans)
    (row : List Record) : Bool :=
  decide (N*(rs.length*(2^K*a)) < D*(centeredBlock rs (observedScore F K h) row).natAbs)

/-- All candidate prefix estimates share both their raw records and their
block partition. The failure fraction is at most `|Fs| 3^s/(2·4^s)`.
In particular s may be selected from a desired failure probability before
seeing the data. -/
theorem simultaneous_raw_prefixes {menu plans} (Fs : List (Fields menu plans))
    (hnodup : menu.Nodup) (K h : Nat)
    (hwidth : ∀ F∈Fs, ∀ j ∈ F.live, (F.pivot j).window.right.length≤K)
    (law : List (Nat→Bool)) {N Q a D : Nat} (hn : 0<N) (ha : 0<a) (hD : 0<D)
    (hK : 0<law.length) (hq : ∀ F∈Fs, ∀ j ∈ F.live, minCount (F.pivot j).window law ≤ Q)
    (hsize : ∀ F∈Fs, 16*D*D*F.live.length*Q*(9^h*(K+1)^h) ≤ law.length*N*a*a)
    (s : Nat) :
    let rs := records menu plans law
    let draws := SampleVariance.iidTuples (rawBlocks rs N) (2*s+1)
    (2*4^s)*draws.countP (fun row => Fs.any fun F =>
        SampleVariance.atLeastBad (badBlock rs K h N a D F) (s+1) row) ≤
      Fs.length*(3^s*draws.length) := by
  let rs := records menu plans law
  let B := rawBlocks rs N
  let pred := badBlock (menu:=menu) (plans:=plans) rs K h N a D
  have quart (F : Fields menu plans) (hf : F∈Fs) : 4*B.countP (pred F) ≤ B.length := by
    let scores := rs.map (observedScore F K h)
    let cx := SampleVariance.sampleSums (SampleVariance.centered scores) N
    have result := actual_prefix_block F hnodup K h (hwidth F hf) law hn ha hD hK (hq F hf) (hsize F hf)
    change 3*cx.length ≤ 4*SampleVariance.goodCount cx (N*(scores.length*(2^K*a))) D at result
    have hc : B.map (centeredBlock rs (observedScore F K h)) = cx := centered_map rs _ N
    have hlen := congrArg List.length hc
    simp only [List.length_map] at hlen
    have count : B.countP (pred F) = SampleVariance.badCount cx (N*(scores.length*(2^K*a))) D := by
      rw [←hc]; simp [SampleVariance.badCount,List.countP_map,Function.comp_def,scores,pred,badBlock]; rfl
    have hp := good_plus_bad cx (N*(scores.length*(2^K*a))) D
    rw [count,hlen]; omega
  have bound := SampleVariance.simultaneous_prefix_bound B (Fs.map pred) (by
    intro g hg; obtain ⟨F,hf,rfl⟩ := List.mem_map.mp hg; exact quart F hf) s
  simpa only [List.any_map,List.length_map,Function.comp_def,pred,B,rs] using bound

/-- Interface for the explicitly clipped consecutive partitions. Only
indices in [0,m) need a valid distinguished label. -/
structure Geometry (m W : Nat) (plans : Bool→List (List Nat)) where
  pivot : Nat → Pivot (List.range m) plans
  label : ∀ j, j<m → (pivot j).window.j=j
  pre : ∀ j, j<m → (pivot j).window.pre=List.range j
  cover : ∀ j, j<m → ∀ i, j<i → i<m → i≤j+2*W → i∈(pivot j).window.right
  width : ∀ j, j<m → (pivot j).window.right.length≤4*W+1

/-- The exact natural-minimum indices that can contribute a prefix error. -/
def liveBand (m W t : Nat) : List Nat := List.range' (t-W) (min m (t+W) - (t-W))

theorem mem_live (m W t j : Nat) : j∈liveBand m W t ↔ j<m ∧ t≤j+W ∧ j<t+W := by
  simp only [liveBand,List.mem_range',Nat.one_mul]
  constructor
  · rintro ⟨i,hi,eq⟩; omega
  · rintro ⟨hm,hl,hu⟩; exact ⟨j-(t-W),by omega,by omega⟩

theorem live_size (m W t : Nat) : (liveBand m W t).length≤2*W := by
  simp only [liveBand,List.length_range']; omega

noncomputable def bandFields {m W plans} (G : Geometry m W plans) (t : Nat) (R : Nat→Bool) :
    Fields (List.range m) plans where
  live := liveBand m W t
  distinct := List.nodup_range' 1
  pivot := G.pivot
  label := fun j hj => G.label j ((mem_live _ _ _ _).mp hj).1
  payoff := fun j => prefixPayoff _ (readBits (G.pivot j).window.right R) (R j) (decide (t≤j))
  bounded := fun _ _ => prefix_payoff_bound _ _ _ _

/-- Ordinary centered survival on the literal full menu. Prefix membership
is supplied by R; the reference probes labels 0 through t−1. -/
def survivalDifference (m t : Nat) (R hit : Nat→Bool) : Int :=
  (if !(List.range m).any (fun i=>hit i && R i) then 1 else 0) -
  (if !(List.range m).any (fun i=>hit i && decide (i<t)) then 1 else 0)

/-- Actual minimum of the original word's hit positions in the menu. -/
def naturalMin (m : Nat) (z : Nat→Bool) : Option Nat := ((List.range m).filter z).min?

theorem natural_min_some {m j : Nat} {z : Nat→Bool} : naturalMin m z=some j ↔
    j<m ∧ z j=true ∧ ∀ i, i<m → z i=true → j≤i := by
  simp only [naturalMin,List.min?_eq_some_iff',List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨⟨hj,hz⟩,hp⟩; exact ⟨hj,hz,fun i hi h => hp i ⟨hi,h⟩⟩
  · rintro ⟨hj,hz,hp⟩; exact ⟨⟨hj,hz⟩,fun i hi => hp i hi.1 hi.2⟩

theorem natural_min_none {m : Nat} {z : Nat→Bool} : naturalMin m z=none ↔ ∀ i, i<m → z i=false := by
  simp only [naturalMin,List.min?_eq_none_iff,List.filter_eq_nil_iff,List.mem_range]
  simp only [Bool.not_eq_true]

theorem eligible_is_min {m W plans} (G : Geometry m W plans) (j : Nat) (hj : j<m) (z : Nat→Bool) :
    eligible (localWord (G.pivot j).window z)=true ↔ naturalMin m z=some j := by
  rw [eligible_minimum,G.pre j hj,G.label j hj,natural_min_some]
  simp only [Bool.and_eq_true,Bool.not_eq_true',List.any_eq_false,List.mem_range]
  constructor
  · rintro ⟨hb,hz⟩; refine ⟨hj,hz,?_⟩
    intro i hmi hi; by_cases hh : i<j
    · have := hb i hh; simp_all
    · omega
  · rintro ⟨_,hz,hm⟩; refine ⟨?_,hz⟩
    intro i hi; cases e : z i with
    | false => decide
    | true => have := hm i (by omega) e; omega

private theorem sum_point (js : List Nat) (hd : js.Nodup) (j : Nat) (f : Nat→Int) :
    sumOn js (fun i => if i=j then f i else 0) = if j∈js then f j else 0 := by
  induction js with
  | nil => simp [sumOn]
  | cons i js ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hd
    change (if i=j then f i else 0)+sumOn js _ = _
    rw [ih ht]; by_cases he : i=j <;> simp_all [List.mem_cons,eq_comm]

private theorem band_truth_min {m W plans} (G : Geometry m W plans) (t : Nat)
    (R z : Nat→Bool) (j : Nat) (h : naturalMin m z=some j) :
    truth (bandFields G t R) z = if j∈liveBand m W t then
      prefixPayoff _ (readBits (G.pivot j).window.right R) (R j) (decide (t≤j))
        (readBits (G.pivot j).window.right z) else 0 := by
  let f := fun i => prefixPayoff _ (readBits (G.pivot i).window.right R) (R i) (decide (t≤i))
    (readBits (G.pivot i).window.right z)
  change sumOn (liveBand m W t) (fun i => if eligible (localWord (G.pivot i).window z) then f i else 0)=_
  rw [←sum_point (liveBand m W t) (List.nodup_range' 1) j f]
  unfold sumOn; congr 1; apply List.map_congr_left
  intro i hi
  have eq := eligible_is_min G i ((mem_live _ _ _ _).mp hi).1 z
  rw [h] at eq
  simp only [Option.some.injEq,eq_comm (a:=j)] at eq
  simp [eq]

private theorem band_truth_empty {m W plans} (G : Geometry m W plans) (t : Nat)
    (R z : Nat→Bool) (h : naturalMin m z=none) : truth (bandFields G t R) z=0 := by
  rw [truth]; change sumOn (liveBand m W t) _=0
  have zero : sumOn (liveBand m W t) (fun _=>0)=0 := by rw [sum_constant,Int.mul_zero]
  apply Eq.trans _ zero; unfold sumOn; congr 1; apply List.map_congr_left
  intro i hi
  have eq := eligible_is_min G i ((mem_live _ _ _ _).mp hi).1 z
  rw [h] at eq
  change (if eligible (localWord (G.pivot i).window z) then _ else 0)=0
  simp [eq]

private theorem selected_any (m : Nat) (z R : Nat→Bool) :
    (List.range m).any (fun i=>z i && R i)=true ↔ ∃i, i<m ∧ z i=true ∧ R i=true := by
  simp only [List.any_eq_true,List.mem_range,Bool.and_eq_true]

private theorem reference_survives {m j} (z : Nat→Bool) (t : Nat) (hm : naturalMin m z=some j) :
    (!(List.range m).any (fun i=>z i && decide (i<t))) = decide (t≤j) := by
  obtain ⟨hj,hz,low⟩ := natural_min_some.mp hm
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',List.any_eq_false,List.mem_range,decide_eq_true_eq]
  constructor
  · intro hzall; by_cases lt : j<t
    · have := hzall j hj; simp [hz,lt] at this
    · omega
  · intro hjt i hi
    cases e : z i with
    | false => simp
    | true => have := low i hi e; simp [show ¬i<t by omega]

private theorem no_local_hits (labels : List Nat) (R z : Nat→Bool) :
    noPositiveHit (slots labels.length (readBits labels z) (readBits labels R)) =
      !labels.any (fun i=>z i && R i) := by
  rw [slots_read]; simp [noPositiveHit,tests,List.any_map,Function.comp_def]

private theorem right_mem_lt {m W plans} (G : Geometry m W plans) (i j : Nat)
    (h : i∈(G.pivot j).window.right) : i<m := by
  apply List.mem_range.mp
  rw [←(G.pivot j).menu_eq]; simp [Split.menu,h]

private theorem global_survives_at {m W plans} (G : Geometry m W plans) (t j : Nat)
    (R z : Nat→Bool) (band : inBand W t R) (live : j∈liveBand m W t)
    (hm : naturalMin m z=some j) :
    (!(List.range m).any (fun i=>z i && R i)) =
      (!R j && !(G.pivot j).window.right.any (fun i=>z i && R i)) := by
  obtain ⟨hj,hz,low⟩ := natural_min_some.mp hm
  obtain ⟨_,prox,_⟩ := (mem_live m W t j).mp live
  have selected : (List.range m).any (fun i=>z i && R i) =
      (R j || (G.pivot j).window.right.any (fun i=>z i && R i)) := by
    apply Bool.eq_iff_iff.mpr
    rw [selected_any]
    simp only [Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true]
    constructor
    · rintro ⟨i,hi,iz,ir⟩
      by_cases eq : i=j
      · exact Or.inl (eq ▸ ir)
      · have ji := low i hi iz
        have upper : i<t+W := by
          by_cases hh : t+W≤i
          · have := band.2 i hh; simp_all
          · omega
        exact Or.inr ⟨i,G.cover j hj i (by omega) hi (by omega),iz,ir⟩
    · rintro (rj|⟨i,ih,iz,ir⟩)
      · exact ⟨j,hj,hz,rj⟩
      · exact ⟨i,right_mem_lt G i j ih,iz,ir⟩
  rw [selected,Bool.not_or]

/-- The constructed scalar field equals the physical prefix-survival
contrast on every word, including a miss. Membership R need only obey the
two forced regions of a W-displaced prefix. -/
theorem band_truth {m W plans} (G : Geometry m W plans) (t : Nat) (R : Nat→Bool)
    (band : inBand W t R) (z : Nat→Bool) :
    truth (bandFields G t R) z=survivalDifference m t R z := by
  cases hm : naturalMin m z with
  | none =>
    rw [band_truth_empty G t R z hm]
    have empty (S : Nat→Bool) : (List.range m).any (fun i=>z i && S i)=false := by
      apply List.any_eq_false.mpr
      intro i hi; simp [(natural_min_none.mp hm) i (List.mem_range.mp hi)]
    simp [survivalDifference,empty]
  | some j =>
    rw [band_truth_min G t R z j hm]
    unfold survivalDifference
    rw [reference_survives z t hm]
    by_cases live : j∈liveBand m W t
    · rw [if_pos live,global_survives_at G t j R z band live hm]
      simp [prefixPayoff,no_local_hits]
    · rw [if_neg live]
      obtain ⟨hj,hz,low⟩ := natural_min_some.mp hm
      by_cases early : j+W<t
      · have found : (List.range m).any (fun i=>z i && R i)=true :=
          (selected_any m z R).mpr ⟨j,hj,hz,band.1 j early⟩
        simp [found,show ¬t≤j by omega]
      · have late : t+W≤j := by rw [mem_live] at live; omega
        have no : (List.range m).any (fun i=>z i && R i)=false := by
          apply List.any_eq_false.mpr
          intro i hi
          cases zi : z i with
          | false => simp
          | true =>
            have := low i (List.mem_range.mp hi) zi
            simp [band.2 i (by omega)]
        simp [no,show t≤j by omega]

/-- Literal reference minima, so a single frequency upper bound Q is
usable before choosing any prefix. -/
theorem band_min_count {m W plans} (G : Geometry m W plans) (j : Nat) (hj : j<m)
    (law : List (Nat→Bool)) : minCount (G.pivot j).window law =
      law.countP (fun z=>decide (naturalMin m z=some j)) := by
  unfold minCount
  congr 1
  funext z
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using eligible_is_min G j hj z

/-- The normalized expected score of a legal prefix is precisely the
centered physical survival probability. Each original word is one ticket. -/
theorem literal_prefix_mean {m W plans} (G : Geometry m W plans) (t : Nat) (R : Nat→Bool)
    (band : inBand W t R) (h : Nat) (law : List (Nat→Bool))
    (cap : ∀ z∈law, (List.range m).countP z≤h+1) :
    sumOn (records (List.range m) plans law) (observedScore (bandFields G t R) (4*W+1) h) =
      ((choices m*2^(4*W+1):Nat):Int)*sumOn law (survivalDifference m t R) := by
  have mean := actual_prefix_mean (bandFields G t R) List.nodup_range (4*W+1) h
    (fun j hj => G.width j ((mem_live m W t j).mp hj).1) law cap
  have hf := funext (band_truth G t R band)
  simpa only [List.length_range,hf] using mean

abbrev Prefix := Nat × (Nat→Bool)

/-- A finite common-sample confidence bound on the entire list of prefix
queries. Q is the largest allowed count of any natural minimum among the
original tickets. For a legal query its population center is exactly the
one in `literal_prefix_mean`.

The block length condition has order D²/a² times q W^(h+1) for fixed h,
where q=Q/law.length and words have at most h+1 hits. The separate cap on
word size is required for the mean identity, and the variance bound holds
even on words with arbitrary additional hits. -/
theorem literal_prefix_confidence {m W plans} (G : Geometry m W plans) (Ps : List Prefix)
    (h : Nat) (law : List (Nat→Bool)) {N Q a D : Nat}
    (hn : 0<N) (ha : 0<a) (hD : 0<D) (hL : 0<law.length)
    (freq : ∀ j, j<m → law.countP (fun z=>decide (naturalMin m z=some j)) ≤ Q)
    (budget : 16*D*D*(2*W)*Q*(9^h*(4*W+2)^h) ≤ law.length*N*a*a) (s : Nat) :
    let rs := records (List.range m) plans law
    let draws := SampleVariance.iidTuples (rawBlocks rs N) (2*s+1)
    (2*4^s)*draws.countP (fun row => Ps.any fun p =>
      SampleVariance.atLeastBad (badBlock rs (4*W+1) h N a D (bandFields G p.1 p.2)) (s+1) row) ≤
      Ps.length*(3^s*draws.length) := by
  let fields := fun (p : Prefix) => bandFields G p.1 p.2
  have pass (p : Prefix) : 16*D*D*(fields p).live.length*Q*(9^h*((4*W+1)+1)^h) ≤ law.length*N*a*a :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right Q
      (Nat.mul_le_mul_left (16*D*D) (live_size m W p.1)))) budget
  have bound := simultaneous_raw_prefixes (Ps.map fields) List.nodup_range (4*W+1) h (by
    intro F hF j hj; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hF
    exact G.width j ((mem_live m W p.1 j).mp hj).1) law hn ha hD hL (Q:=Q) (by
    intro F hF j hj; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hF
    have jm := ((mem_live m W p.1 j).mp hj).1
    change minCount (G.pivot j).window law ≤ Q
    rw [band_min_count G j jm law]; exact freq j jm) (by
    intro F hF; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hF; exact pass p) s
  simpa only [List.any_map,List.length_map,Function.comp_def,fields] using bound

end Screening.GlobalOneHit
