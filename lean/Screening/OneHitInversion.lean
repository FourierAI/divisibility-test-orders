import Std
import Screening.SampleVariance

/-! Fair-sign inversion of local exact hit cells from a marked-first stopped scan.
The distinguished label is j. The d positions following it in its block
are indexed by a Boolean cube. All arithmetic is integral, with explicit
powers of two for the denominators of the fair public coins. -/
namespace Screening.OneHitInversion

/-- A recursively indexed Boolean cube with one coordinate per tail position. -/
def Mask : Nat → Type
  | 0 => Unit
  | d+1 => Bool × Mask d

instance maskDecEq (d : Nat) : DecidableEq (Mask d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ d ih =>
    letI : DecidableEq (Mask d) := ih
    exact inferInstanceAs (DecidableEq (Bool × Mask d))

def cubeSum : (d : Nat) → (Mask d → Int) → Int
  | 0,f => f ()
  | d+1,f => cubeSum d (fun t => f (false,t)) + cubeSum d (fun t => f (true,t))

theorem cube_scale (d : Nat) (c : Int) (f : Mask d → Int) :
    cubeSum d (fun t => c*f t) = c*cubeSum d f := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [cubeSum,ih,Int.mul_add]

theorem cube_add (d : Nat) (f g : Mask d → Int) :
    cubeSum d (fun t => f t+g t) = cubeSum d f + cubeSum d g := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [cubeSum,ih]; ac_rfl

theorem cube_const (d : Nat) (c : Int) :
    cubeSum d (fun _ => c) = 2^d*c := by
  induction d with
  | zero => simp [cubeSum]
  | succ d ih =>
    have two : 2*c = c+c := by omega
    simp only [cubeSum,ih,Int.pow_succ,Int.mul_assoc,two,Int.mul_add]

/-- A scan label is true exactly at the single distinguished index j.
A missing hit returns none. -/
structure Test where
  pivot : Bool
  positive : Bool
  hit : Bool

def scan : List Test → Option Bool
  | [] => none
  | x::xs => if x.hit then some x.pivot else scan xs

def markedFirst (xs : List Test) : List Test :=
  xs.filter (fun x => x.positive) ++ xs.filter (fun x => !x.positive)

def ordinary (x : Bool × Bool) : Test := ⟨false,x.2,x.1⟩

/-- For earlier and later blocks, their public scans may already be listed in
any order. Every earlier test precedes this block and every later test
follows it. All local tests use the actual marked-before-unmarked priority. -/
def stopped (before left right after : List (Bool × Bool)) (jhit jmark : Bool) : Option Bool :=
  scan (before.map ordinary ++
        markedFirst (left.map ordinary ++ [⟨true,jmark,jhit⟩] ++ right.map ordinary) ++
        after.map ordinary)

def clear (xs : List (Bool × Bool)) : Bool := !(xs.any (fun x => x.1))
def noPositiveHit (xs : List (Bool × Bool)) : Bool := !(xs.any (fun x => x.1 && x.2))

private theorem scan_append (xs ys : List Test) : scan (xs++ys) = (scan xs).or (scan ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : x.hit <;> simp [scan,h,ih,Option.or]

private theorem scan_ordinary (xs : List (Bool × Bool)) :
    scan (xs.map ordinary) = if clear xs then none else some false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨h,m⟩
    cases h <;> simp [scan,ordinary,clear,List.any_cons] at ih ⊢ <;> exact ih

private theorem scan_part (xs : List (Bool × Bool)) (mark : Bool) :
    scan ((xs.map ordinary).filter (fun x => x.positive == mark)) =
      if xs.any (fun x => x.1 && (x.2 == mark)) then some false else none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨h,m⟩
    cases h <;> cases m <;> cases mark <;>
      simp [List.filter_cons,scan,ordinary,List.any_cons] at ih ⊢ <;> exact ih

private theorem clear_parts (xs : List (Bool × Bool)) :
    xs.any (fun x => x.1) =
      (xs.any (fun x => x.1 && x.2) || xs.any (fun x => x.1 && !x.2)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨h,m⟩
    cases h <;> cases m <;> simp [List.any_cons,ih]

/-- Detection of a negative pivot from the stopped log is equivalent to j
being the natural first hit and all tail hits in its block being unmarked.
Earlier positions of the current block also have to miss. -/
theorem negative_first (before left right after : List (Bool × Bool)) (jhit : Bool) :
    stopped before left right after jhit false = some true ↔
      (clear before && clear left && jhit && noPositiveHit right) = true := by
  have pos (l : List (Bool × Bool)) := scan_part l true
  have neg (l : List (Bool × Bool)) := scan_part l false
  simp only [beq_true] at pos
  simp only [beq_false] at neg
  unfold stopped markedFirst noPositiveHit clear
  simp only [List.filter_append,List.filter_cons,List.filter_nil,Bool.not_false,
    Bool.false_eq_true,if_false,if_true,List.nil_append,List.cons_append,
    scan_append,scan_ordinary,pos,neg,scan]
  rw [clear_parts left]
  unfold clear
  cases jhit <;> cases before.any (fun x => x.1) <;>
    cases left.any (fun x => x.1 && x.2) <;> cases left.any (fun x => x.1 && !x.2) <;>
    cases right.any (fun x => x.1 && x.2) <;> cases right.any (fun x => x.1 && !x.2) <;>
    cases after.any (fun x => x.1) <;> decide

def slots : (d : Nat) → Mask d → Mask d → List (Bool × Bool)
  | 0,_,_ => []
  | d+1,(z,zs),(s,ss) => (z,s)::slots d zs ss

/-- This includes the negative sign (-1) for every selected tail position:
a positive public sign contributes -2 and a negative public sign +2. -/
def charBit (query sign : Bool) : Int :=
  if query then (if sign then -2 else 2) else 1

def character : (d : Nat) → Mask d → Mask d → Int
  | 0,_,_ => 1
  | d+1,(t,ts),(s,ss) => charBit t s * character d ts ss

/-- The score uses only public signs, the recorded pivot flag and the
partition coin. In particular it never reads the underlying hit set. -/
def score (d : Nat) (query marks : Mask d) (assigned jmark : Bool) (log : Option Bool) : Int :=
  if assigned && !jmark && (log == some true) then 4*character d query marks else 0

/-- Unnormalized forward matrix for one tail coordinate. Rows are query
membership, columns are actual hit membership. Dividing by 2 gives
[[1,1/2],[0,1]]. -/
def forwardBit : Bool → Bool → Int
  | false, false => 2
  | false, true => 1
  | true, false => 0
  | true, true => 2

/-- The inverse matrix, also scaled by 2, is [[2,-1],[0,2]]. -/
def inverseBit : Bool → Bool → Int
  | false, false => 2
  | false, true => -1
  | true, false => 0
  | true, true => 2

def kernel (entry : Bool → Bool → Int) : (d : Nat) → Mask d → Mask d → Int
  | 0,_,_ => 1
  | d+1,(x,xs),(y,ys) => entry x y * kernel entry d xs ys

private def activeBit (z s : Bool) : Int := if z && s then 0 else 1

private theorem negative_cons (d : Nat) (zs ss : Mask d) (z s : Bool) :
    (if noPositiveHit ((z,s)::slots d zs ss) then (1:Int) else 0) =
      activeBit z s * (if noPositiveHit (slots d zs ss) then 1 else 0) := by
  cases z <;> cases s <;> simp [noPositiveHit,activeBit]

private theorem marked_kernel (d : Nat) (t z : Mask d) :
    cubeSum d (fun s => (if noPositiveHit (slots d z s) then (1:Int) else 0) *
      character d t s) = kernel forwardBit d t z := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases t with ⟨t,ts⟩; rcases z with ⟨z,zs⟩
    have branch (b : Bool) :
        cubeSum d (fun ss => (if noPositiveHit (slots (d+1) (z,zs) (b,ss)) then (1:Int) else 0) *
          character (d+1) (t,ts) (b,ss)) =
          (activeBit z b*charBit t b)*kernel forwardBit d ts zs := by
      have hfun : (fun ss => (if noPositiveHit (slots (d+1) (z,zs) (b,ss)) then (1:Int) else 0) *
          character (d+1) (t,ts) (b,ss)) =
        (fun ss => (activeBit z b*charBit t b)*
          ((if noPositiveHit (slots d zs ss) then (1:Int) else 0)*character d ts ss)) := by
        funext ss; rw [slots,negative_cons,character]; ac_rfl
      rw [hfun,cube_scale,ih]
    rw [cubeSum,branch,branch,kernel,← Int.add_mul]
    cases t <;> cases z <;> rfl

/-- Sum over all public marks and the two independent fair choices for
the partition and the pivot's own sign. On the other partition its
record may be entirely arbitrary, since that branch has zero score. -/
def rawScoreSum (d : Nat) (query z : Mask d) (before left after : List (Bool × Bool))
    (jhit : Bool) (other : Bool → Mask d → Option Bool) : Int :=
  cubeSum d fun s =>
    score d query s false false (other false s) + score d query s false true (other true s) +
    score d query s true false (stopped before left (slots d z s) after jhit false) +
    score d query s true true (stopped before left (slots d z s) after jhit true)

/-- There are 4·2^d public outcomes in this sum. Conditional on the
word, the mean is the forward kernel divided by 2^d if j is the natural
minimum, and zero otherwise. All hits after this block are arbitrary. -/
theorem stopped_forward (d : Nat) (query z : Mask d) (before left after : List (Bool × Bool))
    (jhit : Bool) (other : Bool → Mask d → Option Bool) :
    rawScoreSum d query z before left after jhit other =
      (if clear before && clear left && jhit then 4 else 0) * kernel forwardBit d query z := by
  let gate := clear before && clear left && jhit
  have hf (s : Mask d) :
      score d query s false false (other false s) + score d query s false true (other true s) +
      score d query s true false (stopped before left (slots d z s) after jhit false) +
      score d query s true true (stopped before left (slots d z s) after jhit true) =
      (if gate then 4 else 0) *
      ((if noPositiveHit (slots d z s) then (1:Int) else 0)*character d query s) := by
    have obs := negative_first before left (slots d z s) after jhit
    change (stopped before left (slots d z s) after jhit false = some true ↔
      (gate && noPositiveHit (slots d z s)) = true) at obs
    by_cases hg : gate <;> by_cases hs : noPositiveHit (slots d z s) <;>
      simp [score,hg,hs] at obs ⊢ <;> simp [obs]
  unfold rawScoreSum
  simp only [hf,cube_scale,marked_kernel,gate]

/-- Exact two-sided triangular inversion on every Boolean subset interval,
with no type-level restriction on d. -/
theorem inverse_forward (d : Nat) (u z : Mask d) :
    cubeSum d (fun t => kernel inverseBit d u t * kernel forwardBit d t z) =
      if u=z then (4:Int)^d else 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases u with ⟨u,us⟩; rcases z with ⟨z,zs⟩
    have branch (t : Bool) :
        cubeSum d (fun ts => kernel inverseBit (d+1) (u,us) (t,ts) *
          kernel forwardBit (d+1) (t,ts) (z,zs)) =
        (inverseBit u t*forwardBit t z)*(if us=zs then (4:Int)^d else 0) := by
      have eqf : (fun ts => kernel inverseBit (d+1) (u,us) (t,ts) *
          kernel forwardBit (d+1) (t,ts) (z,zs)) =
        (fun ts => (inverseBit u t*forwardBit t z) *
          (kernel inverseBit d us ts*kernel forwardBit d ts zs)) := by
        funext ts; simp only [kernel]; ac_rfl
      rw [eqf,cube_scale,ih]
    rw [cubeSum,branch,branch,← Int.add_mul]
    change _ = if ((u,us) : Bool × Mask d) = (z,zs) then _ else _
    simp only [Prod.mk.injEq]
    cases u <;> cases z <;> by_cases he : us=zs <;>
      simp [he,inverseBit,forwardBit,Int.pow_succ,Int.mul_comm]

theorem cube_swap (d e : Nat) (f : Mask d → Mask e → Int) :
    cubeSum d (fun x => cubeSum e (f x)) = cubeSum e (fun y => cubeSum d (fun x => f x y)) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change cubeSum d (fun x => cubeSum e (f (false,x))) +
      cubeSum d (fun x => cubeSum e (f (true,x))) = _
    rw [ih,ih,← cube_add]
    rfl

private theorem cube_scale_right (d : Nat) (c : Int) (f : Mask d → Int) :
    cubeSum d (fun x => f x*c) = cubeSum d f*c := by
  simpa only [Int.mul_comm c] using cube_scale d c f

private theorem cube_point (d : Nat) (f : Mask d → Int) (z : Mask d) :
    cubeSum d (fun u => if u=z then f u else 0) = f z := by
  induction d with
  | zero => cases z; rfl
  | succ d ih =>
    rcases z with ⟨b,z⟩
    rw [cubeSum]
    change (cubeSum d (fun u => if ((false,u) : Bool × Mask d) = (b,z) then _ else _) +
      cubeSum d (fun u => if ((true,u) : Bool × Mask d) = (b,z) then _ else _)) = _
    cases b <;> simp [Prod.mk.injEq,ih,cube_const]

/-- Coefficients of a local payoff in observed signed features, scaled by
2^d. Any integer payoff on the exact local hit cell can be used. -/
def coefficient (d : Nat) (f : Mask d → Int) (t : Mask d) : Int :=
  cubeSum d (fun u => f u * kernel inverseBit d u t)

theorem decode_kernel (d : Nat) (f : Mask d → Int) (z : Mask d) :
    cubeSum d (fun t => coefficient d f t * kernel forwardBit d t z) =
      (4:Int)^d*f z := by
  unfold coefficient
  simp only [← cube_scale_right, Int.mul_assoc]
  rw [cube_swap]
  simp only [cube_scale,inverse_forward]
  have hf (u : Mask d) : f u * (if u=z then (4:Int)^d else 0) =
      if u=z then f u*4^d else 0 := by split <;> simp_all
  simp only [hf,cube_point,Int.mul_comm ((4:Int)^d)]

/-- Public estimator based on one log, shared by all its queried subsets. -/
def decodedLog (d : Nat) (f : Mask d → Int) (marks : Mask d)
    (assigned jmark : Bool) (log : Option Bool) : Int :=
  cubeSum d (fun t => coefficient d f t * score d t marks assigned jmark log)

/-- A single training experiment has four public partition/pivot-sign
choices for each enumerated tail-sign assignment. -/
def integrateMarks (d : Nat) (F : Bool → Bool → Mask d → Int) : Int :=
  cubeSum d (fun s => F false false s + F false true s + F true false s + F true true s)

private theorem integrate_scale (d : Nat) (c : Int) (F : Bool → Bool → Mask d → Int) :
    integrateMarks d (fun a b s => c*F a b s) = c*integrateMarks d F := by
  unfold integrateMarks
  simp only [← Int.mul_add,cube_scale]

private theorem integrate_features (d : Nat) (F : Mask d → Bool → Bool → Mask d → Int) :
    integrateMarks d (fun a b s => cubeSum d (fun t => F t a b s)) =
      cubeSum d (fun t => integrateMarks d (F t)) := by
  unfold integrateMarks
  simp only [← cube_add]
  exact cube_swap d d _

structure Word (d : Nat) where
  before : List (Bool × Bool)
  left : List (Bool × Bool)
  pivotHit : Bool
  tailHits : Mask d
  after : List (Bool × Bool)

def eligible {d : Nat} (w : Word d) := clear w.before && clear w.left && w.pivotHit

def observed {d : Nat} (w : Word d) (other : Bool → Mask d → Option Bool)
    (assigned jmark : Bool) (s : Mask d) : Option Bool :=
  if assigned then stopped w.before w.left (slots d w.tailHits s) w.after w.pivotHit jmark
  else other jmark s

/-- Exact single-word reconstruction of any local payoff. Divide the
estimator by 2^d and average it over its 4·2^d public outcomes. -/
theorem one_word_unbiased (d : Nat) (f : Mask d → Int) (w : Word d)
    (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s => decodedLog d f s a b (observed w other a b s)) =
      4*(4:Int)^d*(if eligible w then f w.tailHits else 0) := by
  unfold decodedLog
  rw [integrate_features]
  simp only [integrate_scale]
  have hg (t : Mask d) :
      integrateMarks d (fun a b s => score d t s a b (observed w other a b s)) =
        (if eligible w then 4 else 0)*kernel forwardBit d t w.tailHits :=
    stopped_forward d t w.tailHits w.before w.left w.after w.pivotHit other
  simp only [hg]
  by_cases h : eligible w
  · simp only [h,if_true]
    have hmul (t : Mask d) : coefficient d f t*(4*kernel forwardBit d t w.tailHits) =
        4*(coefficient d f t*kernel forwardBit d t w.tailHits) := by ac_rfl
    simp only [hmul,cube_scale,decode_kernel,Int.mul_assoc]
  · simp [h,cube_const]

def sumOn {α : Type} (xs : List α) (f : α → Int) := (xs.map f).sum

/-- Summing over an arbitrary finite population is sufficient for every
rational finite law, by repeating words according to integer weights. -/
theorem population_unbiased (d : Nat) (f : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    sumOn law (fun w => integrateMarks d
      (fun a b s => decodedLog d f s a b (observed w (other w) a b s))) =
      (4*(4:Int)^d)*sumOn law (fun w => if eligible w then f w.tailHits else 0) := by
  induction law with
  | nil => simp [sumOn]
  | cons w ws ih =>
    change integrateMarks d _ + sumOn ws _ = 4*4^d*((if eligible w then f w.tailHits else 0)+sumOn ws _)
    rw [one_word_unbiased,ih,Int.mul_add]

/-- Local centered survival of a prefix: was the distinguished minimum
tested, was any other local hit tested, and would the natural prefix survive? -/
def prefixPayoff (d : Nat) (tailPrefix : Mask d) (includesPivot referenceSurvives : Bool)
    (z : Mask d) : Int :=
  (if !includesPivot && noPositiveHit (slots d z tailPrefix) then 1 else 0) -
  (if referenceSurvives then 1 else 0)

theorem population_prefix_unbiased (d : Nat) (tailPrefix : Mask d)
    (includesPivot referenceSurvives : Bool) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    let f := prefixPayoff d tailPrefix includesPivot referenceSurvives
    sumOn law (fun w => integrateMarks d
      (fun a b s => decodedLog d f s a b (observed w (other w) a b s))) =
      (4*(4:Int)^d)*sumOn law (fun w => if eligible w then f w.tailHits else 0) :=
  population_unbiased _ _ _ _

def weight : (d : Nat) → Mask d → Nat
  | 0,_ => 0
  | d+1,(b,bs) => weight d bs + if b then 1 else 0

private theorem forward_heavy (d : Nat) (t z : Mask d) (h : weight d z < weight d t) :
    kernel forwardBit d t z = 0 := by
  induction d with
  | zero => simp [weight] at h
  | succ d ih =>
    rcases t with ⟨t,ts⟩; rcases z with ⟨z,zs⟩
    cases t <;> cases z <;> simp [weight,kernel,forwardBit] at h ⊢ <;>
      rw [ih ts zs (by omega)] <;> simp

def linearLog (d : Nat) (c : Mask d → Int) (marks : Mask d)
    (assigned jmark : Bool) (log : Option Bool) : Int :=
  cubeSum d (fun t => c t * score d t marks assigned jmark log)

theorem one_word_field (d : Nat) (c : Mask d → Int) (w : Word d)
    (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s => linearLog d c s a b (observed w other a b s)) =
      (if eligible w then 4 else 0)*cubeSum d (fun t => c t*kernel forwardBit d t w.tailHits) := by
  unfold linearLog
  rw [integrate_features]
  simp only [integrate_scale]
  have hb (t : Mask d) :
      integrateMarks d (fun a b s => score d t s a b (observed w other a b s)) =
      (if eligible w then 4 else 0)*kernel forwardBit d t w.tailHits :=
    stopped_forward d t w.tailHits w.before w.left w.after w.pivotHit other
  simp only [hb]
  rw [← cube_scale]
  congr 1
  funext t; ac_rfl

/-- Keep at most h tail coordinates per queried subset. The pivot itself
adds one to obtain the manuscript's total hit cap. -/
def limited (d h : Nat) (c : Mask d → Int) (t : Mask d) : Int :=
  if weight d t ≤ h then c t else 0

theorem capped_unbiased (d h : Nat) (f : Mask d → Int) (w : Word d)
    (hcap : weight d w.tailHits ≤ h) (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s =>
      linearLog d (limited d h (coefficient d f)) s a b (observed w other a b s)) =
      4*(4:Int)^d*(if eligible w then f w.tailHits else 0) := by
  rw [one_word_field]
  have ht (t : Mask d) : limited d h (coefficient d f) t * kernel forwardBit d t w.tailHits =
      coefficient d f t * kernel forwardBit d t w.tailHits := by
    unfold limited
    split
    · rfl
    · rename_i hh
      rw [forward_heavy d t w.tailHits (by omega)]
      simp
  simp only [ht,decode_kernel]
  cases eligible w <;> simp [Int.mul_assoc]

/-- The tail cap is needed only when j is the first hit. In particular a
word with h+1 tail hits and no pivot contributes zero, as required by a
global cap of h+1 true hits. -/
theorem capped_when_eligible (d h : Nat) (f : Mask d → Int) (w : Word d)
    (hcap : eligible w = true → weight d w.tailHits ≤ h) (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s =>
      linearLog d (limited d h (coefficient d f)) s a b (observed w other a b s)) =
      4*(4:Int)^d*(if eligible w then f w.tailHits else 0) := by
  by_cases he : eligible w=true
  · exact capped_unbiased d h f w (hcap he) other
  · rw [one_word_field]; simp [he]

private def gramWeight : (d : Nat) → Mask d → Int
  | 0,_ => 1
  | d+1,(b,bs) => (if b then 8 else 2)*gramWeight d bs

private theorem gram_weight_formula (d : Nat) (t : Mask d) :
    gramWeight d t = 2^d*(4:Int)^(weight d t) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases t with ⟨b,bs⟩
    cases b <;> simp only [weight,gramWeight,ih,if_true,if_false,Bool.false_eq_true,
      Nat.add_zero,Int.pow_succ]
    · ac_rfl
    · change (2*4:Int)*(2^d*4^(weight d bs)) = _
      ac_rfl

/-- Orthogonality proved by summing products over every actual fair sign
assignment, including the normalization of the diagonal character energy. -/
theorem walsh_orthogonality (d : Nat) (t u : Mask d) :
    cubeSum d (fun s => character d t s * character d u s) =
      if t=u then gramWeight d t else 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases t with ⟨t,ts⟩; rcases u with ⟨u,us⟩
    have br (b : Bool) :
        cubeSum d (fun ss => character (d+1) (t,ts) (b,ss)*character (d+1) (u,us) (b,ss)) =
        (charBit t b*charBit u b)*(if ts=us then gramWeight d ts else 0) := by
      have hfun : (fun ss => character (d+1) (t,ts) (b,ss)*character (d+1) (u,us) (b,ss)) =
        (fun ss => (charBit t b*charBit u b)*(character d ts ss*character d us ss)) := by
        funext ss; simp only [character]; ac_rfl
      rw [hfun,cube_scale,ih]
    rw [cubeSum,br,br,← Int.add_mul]
    change _ = if ((t,ts) : Bool × Mask d) = (u,us) then _ else _
    simp only [Prod.mk.injEq]
    cases t <;> cases u <;> by_cases he : ts=us <;> simp [he,charBit,gramWeight]

private theorem product_sums (d : Nat) (f g : Mask d → Int) :
    cubeSum d f * cubeSum d g = cubeSum d (fun t => cubeSum d (fun u => f t*g u)) := by
  simp only [cube_scale,cube_scale_right]

def polynomial (d : Nat) (c : Mask d → Int) (s : Mask d) : Int :=
  cubeSum d (fun t => c t*character d t s)

def spectralEnergy (d : Nat) (c : Mask d → Int) : Int :=
  cubeSum d (fun t => (c t*c t)*(4:Int)^(weight d t))

theorem walsh_square (d : Nat) (c : Mask d → Int) :
    cubeSum d (fun s => polynomial d c s * polynomial d c s) =
      2^d*spectralEnergy d c := by
  unfold polynomial
  have expand (s : Mask d) :
      cubeSum d (fun t => c t*character d t s) * cubeSum d (fun t => c t*character d t s) =
      cubeSum d (fun t => cubeSum d (fun u => (c t*c u)*(character d t s*character d u s))) := by
    rw [product_sums]
    congr 1; funext t; congr 1; funext u; ac_rfl
  simp only [expand]
  rw [cube_swap]
  have inner (t : Mask d) : cubeSum d (fun s =>
      cubeSum d (fun u => (c t*c u)*(character d t s*character d u s))) =
      (c t*c t)*gramWeight d t := by
    rw [cube_swap]
    simp only [cube_scale,walsh_orthogonality]
    have hg (u : Mask d) : (c t*c u)*(if t=u then gramWeight d t else 0) =
        if u=t then (c t*c u)*gramWeight d t else 0 := by
      by_cases he : t=u <;> simp [he,eq_comm]
    simp only [hg,cube_point]
  simp only [inner,gram_weight_formula]
  unfold spectralEnergy
  rw [← cube_scale]
  congr 1; funext t; ac_rfl

private theorem cube_mono (d : Nat) (f g : Mask d → Int) (h : ∀ s, f s ≤ g s) :
    cubeSum d f ≤ cubeSum d g := by
  induction d with
  | zero => exact h ()
  | succ d ih =>
    exact Int.add_le_add (ih _ _ (fun s => h (false,s))) (ih _ _ (fun s => h (true,s)))

private theorem sq_nonneg (v : Int) : 0 ≤ v*v := by
  rw [← Int.natAbs_mul_self]; omega

theorem observed_linear (d : Nat) (c : Mask d → Int) (s : Mask d) (a b : Bool)
    (log : Option Bool) :
    linearLog d c s a b log =
      if a && !b && (log == some true) then 4*polynomial d c s else 0 := by
  unfold linearLog score polynomial
  split
  · rw [← cube_scale]
    congr 1; funext t; ac_rfl
  · simp [cube_const]

/-- Four public coin cases and 2^d tail signs. After dividing by their
number the second moment on an eligible word is at most 4 times the
weighted squared coefficient sum; an ineligible word has zero second moment. -/
theorem observed_second_moment (d : Nat) (c : Mask d → Int) (w : Word d)
    (other : Bool → Mask d → Option Bool) :
    integrateMarks d (fun a b s =>
      let v := linearLog d c s a b (observed w other a b s)
      v*v) ≤
    (if eligible w then 16 else 0)*(2^d*spectralEnergy d c) := by
  rw [← walsh_square,←cube_scale]
  unfold integrateMarks
  apply cube_mono
  intro s
  simp only [observed_linear,observed, Bool.false_and,Bool.true_and,
    Bool.not_true,Bool.not_false,if_true,if_false,Bool.false_eq_true,
    Int.zero_mul,Int.add_zero,Int.zero_add]
  have obs := negative_first w.before w.left (slots d w.tailHits s) w.after w.pivotHit
  change _ ↔ (eligible w && noPositiveHit (slots d w.tailHits s)) = true at obs
  by_cases hg : eligible w <;> by_cases hs : noPositiveHit (slots d w.tailHits s) <;>
    simp [hg,hs] at obs ⊢ <;> simp [obs]
  all_goals first
    | have he : (4*polynomial d c s)*(4*polynomial d c s) =
          16*(polynomial d c s * polynomial d c s) := by
        change ((4:Int)*_)*(4*_) = (4*4)*(_*_); ac_rfl
      rw [he]; exact Int.le_refl _
    | exact Int.mul_nonneg (by decide) (sq_nonneg _)

private def absWeight : (d : Nat) → Mask d → Nat
  | 0,_ => 1
  | d+1,(b,bs) => (if b then 3 else 2)*absWeight d bs

private theorem coefficient_cons (d : Nat) (f : Mask (d+1) → Int) (b : Bool) (t : Mask d) :
    coefficient (d+1) f (b,t) =
      inverseBit false b * coefficient d (fun u => f (false,u)) t +
      inverseBit true b * coefficient d (fun u => f (true,u)) t := by
  unfold coefficient
  rw [cubeSum]
  have br (v : Bool) :
      cubeSum d (fun u => f (v,u)*kernel inverseBit (d+1) (v,u) (b,t)) =
        inverseBit v b * cubeSum d (fun u => f (v,u)*kernel inverseBit d u t) := by
    rw [← cube_scale]; congr 1; funext u; simp only [kernel]; ac_rfl
  rw [br,br]

private theorem coefficient_bound (d : Nat) (f : Mask d → Int)
    (hf : ∀ z, (f z).natAbs ≤ 1) (t : Mask d) :
    (coefficient d f t).natAbs ≤ absWeight d t := by
  induction d with
  | zero => simpa [coefficient,cubeSum,kernel,absWeight] using hf ()
  | succ d ih =>
    rcases t with ⟨b,t⟩
    rw [coefficient_cons]
    have h0 := ih (fun u => f (false,u)) (fun u => hf (false,u)) t
    have h1 := ih (fun u => f (true,u)) (fun u => hf (true,u)) t
    apply Nat.le_trans (Int.natAbs_add_le _ _)
    cases b <;> simp [inverseBit,absWeight,Int.natAbs_mul] <;> omega

private theorem abs_weight_formula (d : Nat) (t : Mask d) :
    absWeight d t * absWeight d t * 4^(weight d t) = 4^d * 9^(weight d t) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases t with ⟨b,t⟩
    cases b
    · simp only [absWeight,weight,if_false,Bool.false_eq_true,Nat.add_zero,Nat.pow_succ]
      calc 2*absWeight d t*(2*absWeight d t)*4^(weight d t)
            = (2*2)*(absWeight d t*absWeight d t*4^(weight d t)) := by ac_rfl
           _ = _ := by rw [ih]; change 4*(4^d*9^(weight d t)) = _; ac_rfl
    · simp only [absWeight,weight,if_true,Nat.pow_succ]
      calc 3*absWeight d t*(3*absWeight d t)*(4^(weight d t)*4)
            = (3*3)*4*(absWeight d t*absWeight d t*4^(weight d t)) := by ac_rfl
           _ = _ := by rw [ih]; change 9*4*(4^d*9^(weight d t)) = _; ac_rfl

/-- Number of tail-query sets of cardinality at most h. -/
def smallCount : Nat → Nat → Nat
  | 0,_ => 1
  | _+1,0 => 1
  | d+1,h+1 => smallCount d (h+1) + smallCount d h

private theorem count_small (d h : Nat) :
    cubeSum d (fun t => if weight d t ≤ h then (1:Int) else 0) = (smallCount d h : Int) := by
  induction d generalizing h with
  | zero => simp [cubeSum,weight,smallCount]
  | succ d ih =>
    cases h with
    | zero =>
      have impossible (t : Mask d) : ¬ weight d t + 1 ≤ 0 := by omega
      have exactZero : smallCount d 0 = 1 := by cases d <;> rfl
      simp only [cubeSum,weight,Bool.false_eq_true,if_false,if_true,Nat.add_zero,
        Nat.not_succ_le_zero,cube_const,Int.mul_zero,Int.add_zero,smallCount]
      simp only [impossible,if_false,cube_const,Int.mul_zero,Int.add_zero,ih,exactZero]
    | succ h =>
      simp only [cubeSum,weight,Bool.false_eq_true,if_false,if_true,Nat.add_zero,
        Nat.add_le_add_iff_right,ih,smallCount,Int.natCast_add]

theorem small_count_le (d h : Nat) : smallCount d h ≤ (d+1)^h := by
  induction d generalizing h with
  | zero => simp [smallCount]
  | succ d ih =>
    cases h with
    | zero => simp [smallCount]
    | succ h =>
      change smallCount d (h+1) + smallCount d h ≤ (d+2)^(h+1)
      calc _ ≤ (d+1)^(h+1)+(d+1)^h := Nat.add_le_add (ih (h+1)) (ih h)
           _ = (d+1)^h*(d+2) := by rw [Nat.pow_succ,Nat.mul_succ ((d+1)^h) (d+1)]
           _ ≤ (d+2)^h*(d+2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) h)
           _ = _ := (Nat.pow_succ _ _).symm

/-- The coefficient bound includes the 2^d scaling of the reported decoder.
After dividing by its square the energy is at most 9^h times the actual
number of tail subsets of size at most h. -/
theorem capped_energy (d h : Nat) (f : Mask d → Int) (hf : ∀ z, (f z).natAbs ≤ 1) :
    spectralEnergy d (limited d h (coefficient d f)) ≤
      ((4^d*9^h*smallCount d h : Nat):Int) := by
  let bound : Int := ((4^d*9^h : Nat):Int)
  have point (t : Mask d) :
      (limited d h (coefficient d f) t * limited d h (coefficient d f) t)*(4:Int)^(weight d t) ≤
      bound*(if weight d t ≤ h then 1 else 0) := by
    by_cases hi : weight d t ≤ h
    · simp only [limited,hi,if_true,Int.mul_one]
      have v := coefficient_bound d f hf t
      have hn : (coefficient d f t).natAbs*(coefficient d f t).natAbs*4^(weight d t) ≤ 4^d*9^h :=
        Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul v v))
          (by rw [abs_weight_formula]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hi))
      have hz := Int.ofNat_le.mpr hn
      rw [Int.natCast_mul _ (4^(weight d t)),Int.natAbs_mul_self] at hz
      simpa only [Int.natCast_mul,Int.natCast_pow,bound] using hz
    · simp [limited,hi]
  have hsum := cube_mono d _ _ point
  rw [cube_scale,count_small] at hsum
  simpa only [spectralEnergy, Int.natCast_mul, bound] using hsum

theorem prefix_payoff_bound (d : Nat) (r : Mask d) (hasJ reference : Bool) (z : Mask d) :
    (prefixPayoff d r hasJ reference z).natAbs ≤ 1 := by
  unfold prefixPayoff
  cases hasJ <;> cases reference <;> cases noPositiveHit (slots d z r) <;> decide

/-- At population level the square bound is proportional to the number
of words having j as their minimum, not the whole number of input words. -/
theorem population_second_moment (d : Nat) (c : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    sumOn law (fun w => integrateMarks d (fun a b s =>
      let v := linearLog d c s a b (observed w (other w) a b s)
      v*v)) ≤
    16*(law.countP eligible : Int)*(2^d*spectralEnergy d c) := by
  induction law with
  | nil => simp [sumOn]
  | cons w ws ih =>
    have hw := observed_second_moment d c w (other w)
    have hh := Int.add_le_add hw ih
    change integrateMarks d _ + sumOn ws _ ≤ _
    apply Int.le_trans hh
    cases he : eligible w <;>
      simp [List.countP_cons,he,Int.natCast_add,Int.add_mul,Int.mul_add] <;> omega

theorem bounded_population_second_moment (d h : Nat) (f : Mask d → Int)
    (hf : ∀ z, (f z).natAbs ≤ 1) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    sumOn law (fun w => integrateMarks d (fun a b s =>
      let v := linearLog d (limited d h (coefficient d f)) s a b (observed w (other w) a b s)
      v*v)) ≤
    16*(law.countP eligible : Int)*(2^d*((4^d*9^h*(d+1)^h : Nat):Int)) := by
  apply Int.le_trans (population_second_moment d _ law other)
  apply Int.mul_le_mul_of_nonneg_left _ (Int.mul_nonneg (by decide) (by omega))
  apply Int.mul_le_mul_of_nonneg_left _ (by exact Int.pow_nonneg (by decide))
  apply Int.le_trans (capped_energy d h f hf)
  exact Int.ofNat_le.mpr (Nat.mul_le_mul_left _ (small_count_le d h))

theorem sum_append {α : Type} (xs ys : List α) (f : α → Int) :
    sumOn (xs++ys) f = sumOn xs f+sumOn ys f := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    change f x+sumOn (xs++ys) f = (f x+sumOn xs f)+sumOn ys f
    rw [ih,Int.add_assoc]

theorem sum_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → Int) :
    sumOn (xs.flatMap f) g = sumOn xs (fun x => sumOn (f x) g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change sumOn (f x++xs.flatMap f) g = sumOn (f x) g + sumOn xs _
    rw [sum_append,ih]

private def visit : (d : Nat) → (Mask d → List Int) → List Int
  | 0,f => f ()
  | d+1,f => visit d (fun t => f (false,t)) ++ visit d (fun t => f (true,t))

private theorem integrate_visits (d : Nat) (f : Mask d → List Int) (g : Int → Int) :
    sumOn (visit d f) g = cubeSum d (fun s => sumOn (f s) g) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [visit,sum_append,ih,ih,cubeSum]

def wordTickets (d : Nat) (c : Mask d → Int) (w : Word d) (other : Bool → Mask d → Option Bool) :=
  visit d (fun s =>
    let v := fun a b => linearLog d c s a b (observed w other a b s)
    [v false false,v false true,v true false,v true true])

/-- Actual estimator tickets, with multiplicity, over independent word and
public signs. The size is the number of input tickets times 4·2^d. -/
def logTickets (d : Nat) (c : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :=
  law.flatMap (fun w => wordTickets d c w (other w))

private theorem integrate_tickets (d : Nat) (c : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) (g : Int → Int) :
    sumOn (logTickets d c law other) g = sumOn law (fun w => integrateMarks d
      (fun a b s => g (linearLog d c s a b (observed w (other w) a b s)))) := by
  rw [logTickets,sum_flatMap]
  congr 1; funext w
  rw [wordTickets,integrate_visits]
  unfold integrateMarks
  congr 1; funext s
  simp [sumOn,Int.add_assoc]

private theorem sum_one {α : Type} (xs : List α) : sumOn xs (fun _ => 1) = (xs.length : Int) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (1:Int)+sumOn xs (fun _ => 1) = ((xs.length+1 : Nat):Int)
    rw [ih,Int.natCast_succ,Int.add_comm]

theorem sum_const {α : Type} (xs : List α) (k : Int) :
    sumOn xs (fun _ => k) = (xs.length : Int)*k := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    change k+sumOn xs _ = ((xs.length+1 : Nat):Int)*k
    rw [ih,Int.natCast_succ,Int.add_mul,Int.one_mul,Int.add_comm]

theorem log_ticket_count (d : Nat) (c : Mask d → Int) (law : List (Word d))
    (other : Word d → Bool → Mask d → Option Bool) :
    (logTickets d c law other).length = law.length*(4*2^d) := by
  have ht := integrate_tickets d c law other (fun _ => 1)
  rw [sum_one] at ht
  simp only [integrateMarks,cube_const,sum_const] at ht
  have hg : (1+1+1+1:Int)=4 := by decide
  rw [hg,Int.mul_comm ((2:Int)^d) 4] at ht
  have eq : ((logTickets d c law other).length:Int) = ((law.length*(4*2^d):Nat):Int) := by
    simpa only [Int.natCast_mul,Int.natCast_pow] using ht
  omega

theorem actual_logged_mean (d h : Nat) (f : Mask d → Int) (law : List (Word d))
    (hcap : ∀ w ∈ law, weight d w.tailHits ≤ h)
    (other : Word d → Bool → Mask d → Option Bool) :
    sumOn (logTickets d (limited d h (coefficient d f)) law other) id =
      (4*(4:Int)^d)*sumOn law (fun w => if eligible w then f w.tailHits else 0) := by
  rw [integrate_tickets]
  simp only [id_eq]
  induction law with
  | nil => simp [sumOn]
  | cons w ws ih =>
    change integrateMarks d _ + sumOn ws _ = _*((if eligible w then f w.tailHits else 0)+sumOn ws _)
    rw [capped_unbiased d h f w (hcap w (by simp)),ih (fun w hw => hcap w (by simp [hw])),Int.mul_add]

private theorem ticket_energy (xs : List Int) :
    sumOn xs (fun v => v*v) = (SampleVariance.energy xs : Int) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x*x+sumOn xs _ = ((x.natAbs*x.natAbs+SampleVariance.energy xs : Nat):Int)
    rw [ih,Int.natCast_add,Int.natAbs_mul_self]

theorem actual_logged_energy (d h : Nat) (f : Mask d → Int) (hf : ∀ z, (f z).natAbs≤1)
    (law : List (Word d)) (other : Word d → Bool → Mask d → Option Bool) :
    SampleVariance.energy (logTickets d (limited d h (coefficient d f)) law other) ≤
      16*law.countP eligible*(2^d*(4^d*9^h*(d+1)^h)) := by
  apply Int.ofNat_le.mp
  rw [← ticket_energy,integrate_tickets]
  simpa only [Int.natCast_mul,Int.natCast_pow] using bounded_population_second_moment d h f hf law other

private theorem square_shift (k x s : Int) :
    (k*x-s)*(k*x-s) = k*k*(x*x) - (k*s+k*s)*x + s*s := by
  have h1 : (k*x)*(k*x) = k*k*(x*x) := by ac_rfl
  have h2 : (k*x)*s = k*s*x := by ac_rfl
  have h3 : s*(k*x) = k*s*x := by ac_rfl
  simp only [Int.sub_mul,Int.mul_sub,Int.add_mul,h1,h2,h3]; omega

private theorem shifted_sum (k s : Int) (xs : List Int) :
    sumOn xs (fun x => (k*x-s)*(k*x-s)) =
      k*k*sumOn xs (fun x => x*x) - (k*s+k*s)*sumOn xs id + (xs.length : Int)*(s*s) := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    change (k*x-s)*(k*x-s)+sumOn xs _ =
      k*k*(x*x+sumOn xs _) - (k*s+k*s)*(x+sumOn xs id) + ((xs.length+1 : Nat):Int)*(s*s)
    rw [square_shift,ih,Int.natCast_succ]
    simp only [Int.mul_add,Int.add_mul,Int.one_mul]; omega

private theorem weight_sum_id (xs : List Int) : SampleVariance.weightedSum id xs = sumOn xs id := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change x+SampleVariance.weightedSum id xs=x+sumOn xs id; rw [ih]

/-- Usual inequality Var(V) ≤ E[V²], with the integral centering used by
the independent-sample module. -/
theorem centering_energy_le (xs : List Int) :
    SampleVariance.energy (SampleVariance.centered xs) ≤ xs.length*xs.length*SampleVariance.energy xs := by
  let k : Int := xs.length
  let s := sumOn xs id
  have he : (SampleVariance.energy (SampleVariance.centered xs):Int) =
      sumOn xs (fun x => (k*x-s)*(k*x-s)) := by
    rw [←ticket_energy]
    simp only [SampleVariance.centered,weight_sum_id,k,s,sumOn,List.map_map,Function.comp_def]
  apply Int.ofNat_le.mp
  rw [he,shifted_sum,ticket_energy,Int.natCast_mul,Int.natCast_mul]
  change k*k*(SampleVariance.energy xs : Int) -(k*s+k*s)*s+k*(s*s) ≤ k*k*(SampleVariance.energy xs : Int)
  rw [Int.add_mul,Int.mul_assoc k s s]
  have hn : 0 ≤ k*(s*s) := Int.mul_nonneg (by dsimp [k]; omega) (sq_nonneg s)
  omega

theorem centered_size (xs : List Int) (D n t : Nat)
    (h : 4*(D*D*SampleVariance.energy xs) ≤ xs.length*n*t*t) :
    4*(D*D*SampleVariance.energy (SampleVariance.centered xs)) ≤
      (SampleVariance.centered xs).length*n*(xs.length*t)*(xs.length*t) := by
  simp only [SampleVariance.centered,List.length_map] at h ⊢
  let K := xs.length
  have he := centering_energy_le xs
  calc 4*(D*D*SampleVariance.energy (SampleVariance.centered xs))
           ≤ 4*(D*D*(K*K*SampleVariance.energy xs)) :=
             Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ he)
       _ = (K*K)*(4*(D*D*SampleVariance.energy xs)) := by ac_rfl
       _ ≤ (K*K)*(K*n*t*t) := Nat.mul_le_mul_left _ h
       _ = _ := by ac_rfl

/-- An explicit sample size for one local prefix contribution. The
integer threshold a/D is in original payoff units (the recorded linear
score itself has scale 2^d). Eligibility counts the actual words for
which this pivot is the minimum. For a hit cap H, h=H−1. -/
theorem local_prefix_concentration (d h : Nat) (r : Mask d) (hasJ reference : Bool)
    (law : List (Word d)) (other : Word d → Bool → Mask d → Option Bool)
    {n a D : Nat} (hn : 0<n) (ha : 0<a) (hD : 0<D) (hK : 0<law.length)
    (hsize : 16*D*D*law.countP eligible*(9^h*(d+1)^h) ≤ law.length*n*a*a) :
    let f := prefixPayoff d r hasJ reference
    let xs := logTickets d (limited d h (coefficient d f)) law other
    let blocks := SampleVariance.sampleSums (SampleVariance.centered xs) n
    3*blocks.length ≤ 4*SampleVariance.goodCount blocks (n*(xs.length*(2^d*a))) D := by
  let f := prefixPayoff d r hasJ reference
  let xs := logTickets d (limited d h (coefficient d f)) law other
  have he := actual_logged_energy d h f (prefix_payoff_bound d r hasJ reference) law other
  have ht : xs.length = law.length*(4*2^d) := log_ticket_count _ _ _ _
  have h2 : 4^d = (2^d)*(2^d) := Nat.mul_pow 2 2 d
  have hraw : 4*(D*D*SampleVariance.energy xs) ≤ xs.length*n*(2^d*a)*(2^d*a) := by
    rw [ht]
    calc 4*(D*D*SampleVariance.energy xs)
          ≤ 4*(D*D*(16*law.countP eligible*(2^d*(4^d*9^h*(d+1)^h)))) :=
            Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ he)
         _ = (4*2^d*4^d)*(16*D*D*law.countP eligible*(9^h*(d+1)^h)) := by ac_rfl
         _ ≤ (4*2^d*4^d)*(law.length*n*a*a) := Nat.mul_le_mul_left _ hsize
         _ = _ := by rw [h2]; ac_rfl
  have hc := centered_size xs D n (2^d*a) hraw
  have hlen : 0<xs.length := ht ▸ Nat.mul_pos hK (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
  apply SampleVariance.block_three_quarters (SampleVariance.centered xs)
    (SampleVariance.centered_mean_zero xs) _ hn (Nat.mul_pos hlen (Nat.mul_pos (Nat.pow_pos (by decide)) ha)) hD hc
  simpa only [SampleVariance.centered,List.length_map] using hlen

/-- The two shifted blockings used by the actual public design. For every
j at least one blocking keeps the whole interval [j,j+2W] together. -/
theorem two_shift_cover (W j : Nat) :
    let b := 2*W+1
    ∃ offset, (offset=0 ∨ offset=b) ∧
      ∀ i, j≤i → i≤j+2*W → (j+offset)/(2*b)=(i+offset)/(2*b) := by
  let b := 2*W+1
  let D := 2*b
  have hp : 0<D := by dsimp [D,b]; omega
  have hb : b<D := by dsimp [D,b]; omega
  have hW : 2*W<D := by dsimp [D,b]; omega
  have hsum : b+2*W<D := by dsimp [D,b]; omega
  have span (offset : Nat) (h : (j+offset)/D=(j+2*W+offset)/D) (i : Nat)
      (h1 : j≤i) (h2 : i≤j+2*W) : (j+offset)/D=(i+offset)/D := by
    have mono {x y : Nat} (hh : x ≤ y) : x/D ≤ y/D :=
      (Nat.le_div_iff_mul_le hp).mpr (Nat.le_trans (Nat.div_mul_le_self x D) hh)
    have hl := mono (Nat.add_le_add_right h1 offset)
    have hu := mono (Nat.add_le_add_right h2 offset)
    omega
  by_cases small : j%D<b
  · refine ⟨0,Or.inl rfl,span 0 ?_⟩
    simp only [Nat.add_zero]
    rw [Nat.add_div (a:=j) (b:=2*W) hp,Nat.div_eq_of_lt hW,Nat.mod_eq_of_lt hW]
    have hnone : ¬ D≤j%D+2*W := by dsimp [D,b] at *; omega
    simp only [if_neg hnone,Nat.add_zero]
  · refine ⟨b,Or.inr rfl,span b ?_⟩
    rw [Nat.add_right_comm j (2*W) b,Nat.add_assoc]
    rw [Nat.add_div (a:=j) (b:=b) hp,Nat.add_div (a:=j) (b:=b+2*W) hp,
      Nat.div_eq_of_lt hb,Nat.mod_eq_of_lt hb,Nat.div_eq_of_lt hsum,Nat.mod_eq_of_lt hsum]
    have hc1 : D≤j%D+b := by dsimp [D,b] at *; omega
    have hc2 : D≤j%D+(b+2*W) := by omega
    rw [if_pos hc1,if_pos hc2]

/-- A prefix of a permutation whose inverse ranks satisfy displacement W
is decided outside its central strip. Labels and ranks here start at zero. -/
theorem displaced_prefix_band (rank : Nat → Nat) (W t : Nat)
    (hdis : ∀ i, rank i≤i+W ∧ i≤rank i+W) :
    (∀ i, i+W<t → rank i<t) ∧ (∀ i, t+W≤i → ¬rank i<t) := by
  constructor
  · intro i h; have hi := (hdis i).1; omega
  · intro i h; have hi := (hdis i).2; omega

/-- Centered survival outside the strip vanishes. Inside the strip, hits
past j+2W have no effect, so the exact local payoff equals whole-word
centered survival. A hit set is enumerated as j followed by its other hits. -/
theorem displaced_local_survival (rank : Nat → Nat) (W t j : Nat) (hits : List Nat)
    (hdis : ∀ i, rank i≤i+W ∧ i≤rank i+W) (hmin : ∀ i ∈ hits, j≤i) :
    let R := fun i => decide (rank i<t)
    let natural := fun i : Nat => decide (i<t)
    let Z := j::hits
    let Zlocal := j::hits.filter (fun i => decide (i≤j+2*W))
    ((!Z.any R) = ((!Z.any natural))) ∨
      ((j+W≥t ∧ j<t+W) ∧ (!Z.any R) = (!Zlocal.any R)) := by
  dsimp only
  obtain ⟨low,high⟩ := displaced_prefix_band rank W t hdis
  by_cases early : j+W<t
  · exact Or.inl (by simp [List.any_cons,low j early,show j<t by omega])
  by_cases late : t+W≤j
  · left
    have hfalse {i} (hi : j≤i) : ¬rank i<t ∧ ¬i<t := by
      have := high i (by omega); omega
    have rzero : hits.any (fun i => decide (rank i<t)) = false := by
      apply List.any_eq_false.mpr
      intro i hi; simp [(hfalse (hmin i hi)).1]
    have nzero : hits.any (fun i => decide (i<t)) = false := by
      apply List.any_eq_false.mpr
      intro i hi; simp [(hfalse (hmin i hi)).2]
    simp [List.any_cons,(hfalse (Nat.le_refl j)).1,(hfalse (Nat.le_refl j)).2,rzero,nzero]
  right
  refine ⟨⟨by omega,by omega⟩,?_⟩
  have filter_same :
      hits.any (fun i => decide (rank i<t)) =
      (hits.filter (fun i => decide (i≤j+2*W))).any (fun i => decide (rank i<t)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨i,hi,hr⟩
      have bound := (hdis i).2
      exact ⟨i,⟨hi,by omega⟩,hr⟩
    · rintro ⟨i,⟨hi,_⟩,hr⟩; exact ⟨i,hi,hr⟩
  simp only [List.any_cons,filter_same]

/-- On a shared global first-hit record Y, every local index j computes
a contribution supported on Y=j. Their cross products vanish pointwise. -/
theorem only_reported_square {α : Type} (indices : List Nat) (hd : indices.Nodup)
    (record : α) (Y : α → Option Nat) (v : Nat → α → Int) :
    let contribution := fun j => if Y record=some j then v j record else 0
    sumOn indices contribution * sumOn indices contribution =
      sumOn indices (fun j => contribution j*contribution j) := by
  dsimp only
  induction indices with
  | nil => simp [sumOn]
  | cons j js ih =>
    obtain ⟨hnot,hrest⟩ := List.nodup_cons.mp hd
    change ((if Y record=some j then v j record else 0)+sumOn js _)*
      ((if Y record=some j then v j record else 0)+sumOn js _) =
      (if Y record=some j then v j record else 0)*(if Y record=some j then v j record else 0)+sumOn js _
    by_cases he : Y record=some j
    · have hz : sumOn js (fun i => if Y record=some i then v i record else 0) = 0 := by
        have hmap : js.map (fun i => if Y record=some i then v i record else 0) =
            js.map (fun _ => (0:Int)) := by
          apply List.map_congr_left
          intro i hi
          have hn : j≠i := fun h => hnot (h ▸ hi)
          simp [he,hn]
        simpa [sumOn,hmap] using sum_const js (0:Int)
      rw [← ih hrest,hz]; simp
    · simp [he,ih hrest]

private theorem swap_lists {α β : Type} (xs : List α) (ys : List β) (g : α → β → Int) :
    sumOn xs (fun x => sumOn ys (g x)) = sumOn ys (fun y => sumOn xs (fun x => g x y)) := by
  have add {γ : Type} (l : List γ) (a b : γ → Int) :
      sumOn l (fun z => a z+b z) = sumOn l a+sumOn l b := by
    induction l with
    | nil => rfl
    | cons z zs ih => change a z+b z+sumOn zs _ = (a z+sumOn zs a)+(b z+sumOn zs b); rw [ih]; ac_rfl
  induction xs with
  | nil =>
    change 0 = sumOn ys (fun _ => 0)
    rw [sum_const, Int.mul_zero]
  | cons x xs ih =>
    change sumOn ys (g x)+sumOn xs _ = sumOn ys (fun y => g x y+sumOn xs _)
    rw [add,ih]

def projection {α : Type} (Y : α → Option Nat) (v : Nat → α → Int) (j : Nat) (x : α) : Int :=
  if Y x=some j then v j x else 0

def sharedTickets {α : Type} (xs : List α) (js : List Nat)
    (Y : α → Option Nat) (v : Nat → α → Int) :=
  xs.map (fun x => sumOn js (fun j => projection Y v j x))

/-- Per-minimum square certificates add exactly on a common first-hit log.
No independence across minima is required. -/
theorem shared_energy {α : Type} (xs : List α) (js : List Nat) (hd : js.Nodup)
    (Y : α → Option Nat) (v : Nat → α → Int) :
    ((SampleVariance.energy (sharedTickets xs js Y v)):Int) =
      sumOn js (fun j => ((SampleVariance.energy (xs.map (projection Y v j))):Int)) := by
  rw [← ticket_energy]
  simp only [sharedTickets,sumOn,List.map_map,Function.comp_def]
  have hsq := fun x => only_reported_square js hd x Y v
  change sumOn xs (fun x => sumOn js (fun j => projection Y v j x) * sumOn js (fun j => projection Y v j x)) = _
  have h (x : α) : sumOn js (fun j => projection Y v j x)*sumOn js (fun j => projection Y v j x) =
      sumOn js (fun j => projection Y v j x*projection Y v j x) := hsq x
  simp only [h]
  rw [swap_lists]
  change sumOn js _ = sumOn js _
  congr 1; funext j
  rw [← ticket_energy]
  simp [sumOn,List.map_map,Function.comp_def]

/-- A whole prefix evaluated on one shared record per word. A separate
per-pivot variance certificate can be used for each projection. The only
probabilistic hypothesis here is the numerical second-moment limit for
each projection; actual_logged_energy supplies it on the local design. -/
theorem shared_block_guarantee {α : Type} (rows : List α) (js : List Nat) (hd : js.Nodup)
    (Y : α → Option Nat) (v : Nat → α → Int) {B N T D : Nat}
    (hB : ∀ j ∈ js, SampleVariance.energy (rows.map (projection Y v j)) ≤ B)
    (hrows : 0<rows.length) (hn : 0<N) (ht : 0<T) (hD : 0<D)
    (hsize : 4*(D*D*(js.length*B)) ≤ rows.length*N*T*T) :
    let scores := sharedTickets rows js Y v
    let blocks := SampleVariance.sampleSums (SampleVariance.centered scores) N
    3*blocks.length ≤ 4*SampleVariance.goodCount blocks (N*(scores.length*T)) D := by
  let scores := sharedTickets rows js Y v
  have eqK : scores.length=rows.length := List.length_map _
  have hm : ∀ l : List Nat, (∀ j ∈ l, SampleVariance.energy (rows.map (projection Y v j)) ≤ B) →
      sumOn l (fun j => ((SampleVariance.energy (rows.map (projection Y v j))):Int)) ≤ ((l.length*B:Nat):Int) := by
    intro l
    induction l with
    | nil => intro _; simp [sumOn]
    | cons j l ih =>
      intro hh
      have hb := Int.ofNat_le.mpr (hh j (by simp))
      have hr := ih (fun j hj => hh j (by simp [hj]))
      have hcomb := Int.add_le_add hb hr
      change _ + sumOn l _ ≤ ((l.length+1)*B:Nat)
      simpa only [Nat.add_mul,Nat.one_mul,Int.natCast_add,Int.add_comm (B:Int)] using hcomb
  have he : SampleVariance.energy scores ≤ js.length*B := by
    apply Int.ofNat_le.mp
    rw [shared_energy rows js hd Y v]
    exact hm js hB
  have hc := centered_size scores D N T (by
    rw [eqK]
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ he)) hsize)
  have hk : 0<scores.length := eqK ▸ hrows
  apply SampleVariance.block_three_quarters _ (SampleVariance.centered_mean_zero scores) _ hn
    (Nat.mul_pos hk ht) hD hc
  simpa only [SampleVariance.centered,List.length_map] using hk

def windowCode : (d start : Nat) → (Nat → Bool) → Mask d
  | 0,_,_ => ()
  | d+1,start,p => (p start,windowCode d (start+1) p)

private theorem window_injective (d start : Nat) (p q : Nat → Bool)
    (h : windowCode d start p = windowCode d start q) :
    ∀ i, start≤i → i<start+d → p i=q i := by
  induction d generalizing start with
  | zero => intro i h1 h2; omega
  | succ d ih =>
    have eq : (p start,windowCode d (start+1) p) = (q start,windowCode d (start+1) q) := h
    obtain ⟨first,rest⟩ := Prod.mk.inj eq
    intro i h1 h2
    by_cases hs : start=i
    · simpa [hs] using first
    · exact ih (start+1) rest i (by omega) (by omega)

def inBand (W t : Nat) (p : Nat → Bool) : Prop :=
   (∀ i, i+W<t → p i=true) ∧ (∀ i, t+W≤i → p i=false)

theorem band_code_injective (W t : Nat) (p q : Nat → Bool)
    (hp : inBand W t p) (hq : inBand W t q)
    (hcode : windowCode (2*W) (t-W) p = windowCode (2*W) (t-W) q) : p=q := by
  funext i
  by_cases low : i+W<t
  · rw [hp.1 i low,hq.1 i low]
  by_cases high : t+W≤i
  · rw [hp.2 i high,hq.2 i high]
  exact window_injective (2*W) (t-W) p q hcode i (by omega) (by omega)

private def allMasks : (d : Nat) → List (Mask d)
  | 0 => [()]
  | d+1 => ((allMasks d).map (false,·)) ++ ((allMasks d).map (true,·))

private theorem mem_masks (d : Nat) (s : Mask d) : s ∈ allMasks d := by
  induction d with
  | zero => cases s; simp [allMasks]
  | succ d ih =>
    rcases s with ⟨s,ss⟩
    cases s <;> simp [allMasks,ih]

private theorem masks_length (d : Nat) : (allMasks d).length=2^d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [allMasks,List.length_append,List.length_map,ih,Nat.pow_succ]; omega

private theorem nodup_subset_length {α : Type} (xs ys : List α) (hd : xs.Nodup)
    (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hn,hr⟩ := List.nodup_cons.mp hd
    obtain ⟨a,b,rfl⟩ := List.append_of_mem (hs (by simp : x ∈ x::xs))
    have sub : xs ⊆ a++b := by
      intro z hz
      have hother : z≠x := fun he => hn (he ▸ hz)
      have : z ∈ a++x::b := hs (by simp [hz])
      simpa [List.mem_append,hother] using this
    have := ih (a++b) hr sub
    simp only [List.length_append,List.length_cons] at *; omega

/-- At a fixed prefix length, every legal membership function is encoded
by at most 2W bits even when the window extends beyond the menu. -/
theorem prefix_count (W t : Nat) (prefixes : List (Nat → Bool)) (hd : prefixes.Nodup)
    (hb : ∀ p ∈ prefixes, inBand W t p) : prefixes.length ≤ 2^(2*W) := by
  let code := windowCode (2*W) (t-W)
  have nd : (prefixes.map code).Nodup := by
    induction prefixes with
    | nil => simp
    | cons p ps ih =>
      obtain ⟨hn,hr⟩ := List.nodup_cons.mp hd
      rw [List.map_cons,List.nodup_cons]
      refine ⟨?_,ih hr (fun q hq => hb q (by simp [hq]))⟩
      intro hp
      obtain ⟨q,hq,e⟩ := List.mem_map.mp hp
      have he := band_code_injective W t q p (hb q (by simp [hq])) (hb p (by simp)) e
      exact hn (he ▸ hq)
  have hl := nodup_subset_length (prefixes.map code) (allMasks (2*W)) nd (fun _ _ => mem_masks _ _)
  simpa only [List.length_map,masks_length] using hl

/-- Optimization step. If each candidate's sum of m prefix errors has
absolute discrepancy at most mδ, exact minimization of the estimated
cost gives true excess at most 2mδ. All quantities may be scaled integers. -/
theorem minimizing_estimated_cost {α : Type} (C estimated : α → Int) (chosen best : α)
    (m δ : Nat) (hc : C chosen ≤ estimated chosen + (m*δ:Nat))
    (hb : estimated best ≤ C best + (m*δ:Nat)) (hfit : estimated chosen ≤ estimated best) :
    C chosen - C best ≤ 2*((m*δ:Nat):Int) := by omega

end Screening.OneHitInversion
