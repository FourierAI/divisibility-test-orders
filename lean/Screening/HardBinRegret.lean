import Screening.ArithmeticWitness

/-! Signed prefix survival effects and projected sign inversions in the
hard-menu construction. Positions belonging to other bins may interleave. -/

namespace Screening.HardBinRegret
open Screening.MomentCube Screening.ArithmeticWitness

def avoids [DecidableEq V] (pre cell : List V) : Bool :=
  cell.all (fun v => decide (v∉pre))

def survival [DecidableEq V] (atoms : List (List V × Int)) (pre : List V) : Int :=
  sumOn atoms (fun a => if avoids pre a.1 then a.2 else 0)

private theorem missing [DecidableEq V] (xs ys : List V) (no : ¬xs⊆ys) : ∃v∈xs,v∉ys := by
  induction xs with
  | nil => simp at no
  | cons x xs ih =>
    by_cases hx : x∈ys
    · have tail : ¬xs⊆ys := by
        intro sub; apply no; intro z hz
        rcases List.mem_cons.mp hz with eq|h
        · exact eq ▸ hx
        · exact sub h
      obtain ⟨v,hv,hy⟩ := ih tail
      exact ⟨v,by simp [hv],hy⟩
    · exact ⟨x,by simp,hx⟩

/-- A signed cube changes survival exactly when the prefix includes every
vertex of its edge. Its mass there is the cube coefficient (not a parity sign). -/
theorem cube_survival [DecidableEq V] (edge pre : List V) (d : Int) (unique : edge.Nodup) :
    survival (cubeAtoms edge d) pre = if edge⊆pre then d else 0 := by
  let f := fun c => if avoids pre c then (1:Int) else 0
  have expand : survival (cubeAtoms edge d) pre = d * alternating edge f := by
    unfold survival cubeAtoms alternating
    rw [← sum_factor]
    change (((cells edge).map _).map _).sum = _
    simp only [List.map_map,Function.comp_def]
    apply sum_congr (cells edge)
    intro c _
    cases h : avoids pre c <;> simp [f,h]
  rw [expand]
  by_cases all : edge⊆pre
  · have point (c : List V) (hc : c∈cells edge) :
        (-1:Int)^c.length*f c = if c=[] then 1 else 0 := by
      cases c with
      | nil => simp [f,avoids]
      | cons x xs =>
        have seen : x∈pre := all ((mem_cells.mp hc).subset (by simp))
        simp [f,avoids,seen]
    have emptyCell : [] ∈ cells edge := mem_cells.mpr (by simp)
    have one : alternating edge f=1 := by
      unfold alternating
      rw [sum_congr _ point,sum_pick (cells edge) (fun _ => 1) [] (cells_nodup unique), if_pos emptyCell]
    simp [all,one]
  · obtain ⟨v,he,unseen⟩ := missing edge pre all
    have cancel := free_vertex_cancel edge v he f (by
      intro left right
      simp only [f,avoids,List.all_append,List.all_cons]
      simp only [unseen,not_false_eq_true,decide_true,Bool.true_and])
    simp [all,cancel]

theorem perturbed_survival [DecidableEq V] (base updates : List (List V × Int)) (pre : List V)
    (unique : ∀s∈updates,s.1.Nodup) :
    survival (addCubes base updates) pre =
      survival base pre + sumOn updates (fun s => if s.1⊆pre then s.2 else 0) := by
  induction updates with
  | nil => simp [addCubes,sumOn]
  | cons s ss ih =>
    obtain ⟨e,d⟩ := s
    change sumOn (cubeAtoms e d ++ addCubes base ss) _ =
      survival base pre + ((if e⊆pre then d else 0) + sumOn ss _)
    rw [ArithmeticWitness.sum_append]
    change survival (cubeAtoms e d) pre + survival (addCubes base ss) pre = _
    rw [cube_survival e pre d (unique (e,d) (by simp)), ih (fun s hs => unique s (by simp [hs]))]
    omega

def tailUpdates (anchorSets : List (List V)) (tails : List V) (amp : V→Int) :=
  tails.flatMap (fun i => anchorSets.map (fun a => (a++[i],amp i)))

private theorem constant_sum (xs : List A) (k : Int) : sumOn xs (fun _ => k) = xs.length*k := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
    change k+sumOn xs (fun _ => k) = (↑(xs.length+1):Int)*k
    rw [ih,Int.natCast_add,Int.add_mul]; simp [Int.add_comm]

/-- After all anchors have been tested, the impact is linear in the tested
tail signs. The multiplier is the number of supplied anchor subsets. -/
theorem anchor_tail_survival [DecidableEq V] (base : List (List V×Int))
    (anchorSets : List (List V)) (tails pre : List V) (amp : V→Int)
    (anchorsTested : ∀a∈anchorSets,a⊆pre)
    (unique : ∀i∈tails,∀a∈anchorSets,(a++[i]).Nodup) :
    survival (addCubes base (tailUpdates anchorSets tails amp)) pre = survival base pre +
      (anchorSets.length:Int)*sumOn tails (fun i => if i∈pre then amp i else 0) := by
  have un : ∀s∈tailUpdates anchorSets tails amp,s.1.Nodup := by
    intro s hs
    obtain ⟨i,hi,hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact unique i hi a ha
  rw [perturbed_survival _ _ _ un]
  congr 1
  clear un unique
  induction tails with
  | nil => simp [tailUpdates,sumOn]
  | cons i ts ih =>
    change sumOn ((anchorSets.map (fun a => (a++[i],amp i))) ++ tailUpdates anchorSets ts amp) _ =
      (anchorSets.length:Int)*((if i∈pre then amp i else 0)+sumOn ts _)
    rw [ArithmeticWitness.sum_append,ih,Int.mul_add]
    congr 1
    have c : sumOn (anchorSets.map (fun a => (a++[i],amp i)))
        (fun s => if s.1⊆pre then s.2 else 0) =
        sumOn anchorSets (fun _ => if i∈pre then amp i else 0) := by
      simp only [sumOn,List.map_map,Function.comp_def]
      apply sum_congr anchorSets
      intro a ha
      simp [List.append_subset,anchorsTested a ha]
    rw [c,constant_sum]

/-- Positive-before-negative inversions in one bin. -/
def inversions : List Bool→Nat
  | [] => 0
  | false::bs => inversions bs
  | true::bs => bs.count false + inversions bs

private theorem inversion_swap (front back : List Bool) :
    inversions (front++true::false::back) = inversions (front++false::true::back)+1 := by
  induction front with
  | nil => simp [inversions,List.count_cons]; omega
  | cons t ts ih =>
    cases t <;> simp [inversions,List.count_append,List.count_cons,ih] <;> omega

private theorem positive_pair (bs : List Bool) (positive : 0<inversions bs) :
    ∃front back, bs=front++true::false::back := by
  induction bs with
  | nil => contradiction
  | cons t ts ih =>
    by_cases yes : 0<inversions ts
    · obtain ⟨p,s,eq⟩ := ih yes
      exact ⟨t::p,s,by rw [eq];rfl⟩
    · cases t with
      | false => exact False.elim (yes positive)
      | true =>
        have has : false∈ts := List.count_pos_iff.mp (by
          change 0<ts.count false+inversions ts at positive; omega)
        cases ts with
        | nil => simp at has
        | cons y ys =>
          cases y with
          | false => exact ⟨[],ys,rfl⟩
          | true =>
            have hmem : false∈ys := by simpa using has
            have ypos := List.count_pos_iff.mpr hmem
            change ¬ 0<ys.count false+inversions ys at yes
            omega

/-- Order of the signs in one projected bin while all other positions are discarded. -/
@[nospecialize] def view [DecidableEq B] (group : A→B) (sign : A→Bool) (b : B) (xs : List A) :=
  xs.filterMap (fun a => if group a=b then some (sign a) else none)

private theorem view_head [DecidableEq B] (group : A→B) (sign : A→Bool) (b : B)
    (xs : List A) (t : Bool) (ts : List Bool) (showing : view group sign b xs=t::ts) :
    ∃before a rest, xs=before++a::rest ∧ view group sign b before=[] ∧
      group a=b ∧ sign a=t ∧ view group sign b rest=ts := by
  induction xs with
  | nil => simp [view] at showing
  | cons x xs ih =>
    by_cases hx : group x=b
    · simp [view,hx] at showing
      exact ⟨[],x,xs,rfl,rfl,hx,showing.1,showing.2⟩
    · simp only [view,List.filterMap_cons,hx,if_false] at showing
      obtain ⟨p,a,rest,eq,absent,grp,sg,suffix⟩ := ih showing
      exact ⟨x::p,a,rest,by rw [eq];rfl,by simpa [view,hx] using absent,grp,sg,suffix⟩

private theorem lift_adjacent [DecidableEq B] (group : A→B) (sign : A→Bool) (b : B)
    (xs : List A) (front back : List Bool)
    (showing : view group sign b xs=front++true::false::back) :
    ∃ p x middle y s, xs=p++x::(middle++y::s) ∧
      group x=b ∧ group y=b ∧ sign x=true ∧ sign y=false ∧ view group sign b middle=[] := by
  induction front generalizing xs with
  | nil =>
    obtain ⟨p,x,r,ex,_,gx,sx,next⟩ := view_head group sign b xs true (false::back) showing
    obtain ⟨mid,y,s,ey,empty,gy,sy,_⟩ := view_head group sign b r false back next
    exact ⟨p,x,mid,y,s,by rw [ex,ey],gx,gy,sx,sy,empty⟩
  | cons t ts ih =>
    obtain ⟨pre,z,r,eq,_,_,_,next⟩ := view_head group sign b xs t (ts++true::false::back) showing
    obtain ⟨p,x,mid,y,s,er,gx,gy,sx,sy,empty⟩ := ih r next
    exact ⟨pre++z::p,x,mid,y,s,by rw [eq,er];simp,gx,gy,sx,sy,empty⟩

def allInversions [DecidableEq B] (bins : List B) (group : A→B) (sign : A→Bool) (xs : List A) :=
  Screening.CellLift.sumNat bins (fun b => inversions (view group sign b xs))

private theorem positive_bin [DecidableEq B] (bins : List B) (group : A→B) (sign : A→Bool)
    (xs : List A) (pos : 0<allInversions bins group sign xs) :
    ∃b∈bins,0<inversions (view group sign b xs) := by
  induction bins with
  | nil => contradiction
  | cons b bs ih =>
    by_cases localPos : 0<inversions (view group sign b xs)
    · exact ⟨b,by simp,localPos⟩
    · change 0<inversions (view group sign b xs) + allInversions bs group sign xs at pos
      obtain ⟨c,hc,z⟩ := ih (by omega)
      exact ⟨c,by simp [hc],z⟩

private theorem one_weight_change [DecidableEq B] (bins : List B) (b : B) (f g : B→Nat)
    (unique : bins.Nodup) (inside : b∈bins) (atBin : f b=g b+1)
    (other : ∀c,c≠b→f c=g c) :
    Screening.CellLift.sumNat bins f=Screening.CellLift.sumNat bins g+1 := by
  induction bins with
  | nil => simp at inside
  | cons c cs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp unique
    change f c + Screening.CellLift.sumNat cs f = (g c+Screening.CellLift.sumNat cs g)+1
    by_cases eq : c=b
    · subst c
      have same : cs.map f=cs.map g := List.map_congr_left (fun x hx => other x
        (fun he => fresh (he ▸ hx)))
      unfold Screening.CellLift.sumNat
      rw [atBin,same];omega
    · have h := ih tail ((List.mem_cons.mp inside).resolve_left (Ne.symm eq))
      rw [other c eq]; omega

/-- Exchanging neighboring members of a projected bin, even when arbitrary
other bins lie between them, removes one inversion in the global sum. -/
theorem interleaved_drop [DecidableEq B] (bins : List B) (group : A→B) (sign : A→Bool)
    (b : B) (p mid s : List A) (x y : A) (unique : bins.Nodup) (inside : b∈bins)
    (gx : group x=b) (gy : group y=b) (sx : sign x=true) (sy : sign y=false)
    (empty : view group sign b mid=[]) :
    allInversions bins group sign (p++x::(mid++y::s)) =
      allInversions bins group sign (p++y::(mid++x::s))+1 := by
  apply one_weight_change bins b _ _ unique inside
  · have emp := empty
    unfold view at emp
    simpa [view,List.filterMap_append,gx,gy,sx,sy,emp] using
      inversion_swap (view group sign b p) (view group sign b s)
  · intro c diff
    have nx : group x≠c := by rw [gx]; exact Ne.symm diff
    have ny : group y≠c := by rw [gy]; exact Ne.symm diff
    simp [view,List.filterMap_append,nx,ny]

private theorem transposition_perm (p middle s : List A) (x y : A) :
    (p++y::(middle++x::s)).Perm (p++x::(middle++y::s)) := by
  apply List.Perm.append_left
  exact ((List.perm_middle.cons y).trans (List.Perm.swap x y _)).trans
    (List.perm_middle.symm.cons x)

/-- A lower bound of g on each projected adjacent exchange gives regret at
least g times the number of within-bin sign inversions. The cost need only
obey the exchange inequality on permutations of the initial full order. -/
theorem inversion_regret [DecidableEq B] (bins : List B) (group : A→B) (sign : A→Bool)
    (order : List A) (cost : List A→Int) (opt g : Int) (unique : bins.Nodup)
    (lower : ∀xs,xs.Perm order→opt≤cost xs)
    (save : ∀ b∈bins, ∀p x mid y s, (p++x::(mid++y::s)).Perm order →
      group x=b → group y=b → sign x=true → sign y=false → view group sign b mid=[] →
      cost (p++y::(mid++x::s)) + g ≤ cost (p++x::(mid++y::s))) :
    g*(allInversions bins group sign order:Int) ≤ cost order-opt := by
  have bound (n : Nat) : ∀xs : List A, xs.Perm order → allInversions bins group sign xs=n →
      g*(n:Int) ≤ cost xs-opt := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro xs perm count
      by_cases zero : n=0
      · rw [zero,Int.natCast_zero,Int.mul_zero]; have := lower xs perm; omega
      · have pos : 0<allInversions bins group sign xs := by omega
        obtain ⟨b,hb,posb⟩ := positive_bin bins group sign xs pos
        obtain ⟨front,back,showing⟩ := positive_pair _ posb
        obtain ⟨p,x,mid,y,s,rfl,gx,gy,sx,sy,empty⟩ := lift_adjacent group sign b xs front back showing
        let next := p++y::(mid++x::s)
        have newPerm : next.Perm order := (transposition_perm p mid s x y).trans perm
        have one := interleaved_drop bins group sign b p mid s x y unique hb gx gy sx sy empty
        change allInversions bins group sign (p++x::(mid++y::s)) = allInversions bins group sign next+1 at one
        have hprev := ih (allInversions bins group sign next) (by omega) next newPerm rfl
        have delta := save b hb p x mid y s perm gx gy sx sy empty
        have nEq : n=allInversions bins group sign next+1 := by omega
        rw [nEq,Int.natCast_add,Int.mul_add,Int.natCast_one,Int.mul_one]
        change cost next + g ≤ cost (p++x::(mid++y::s)) at delta
        omega
  exact bound _ order (List.Perm.refl _) rfl

/-! Exact average over independent fair tags, one bit for each tested position. -/

open Screening.CellLift

def fairTags : List B → List (List (B×Bool))
  | [] => [[]]
  | b::bs => (fairTags bs).map ((b,false)::·) ++ (fairTags bs).map ((b,true)::·)

theorem fairTags_length (bs : List B) : (fairTags bs).length = 2^bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [fairTags,ih,Nat.pow_succ];omega

def pairs : Nat→Nat
  | 0 => 0
  | n+1 => pairs n+n

theorem twice_pairs (n : Nat) : 2*pairs n=n*(n-1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ k =>
      simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Nat.succ_mul,Nat.mul_succ] at ih ⊢
      rw [pairs,Nat.mul_add]
      simp only [Nat.zero_mul] at *
      omega

private theorem nat_sum_append (xs ys : List A) (f : A→Nat) :
    sumNat (xs++ys) f=sumNat xs f+sumNat ys f := by
  induction xs with
  | nil => simp [sumNat]
  | cons x xs ih =>
    change f x+sumNat (xs++ys) f = (f x+sumNat xs f)+sumNat ys f
    omega

private theorem nat_sum_add (xs : List A) (f g : A→Nat) :
    sumNat xs (fun x => f x+g x)=sumNat xs f+sumNat xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x+g x+sumNat xs (fun z => f z+g z) = (f x+sumNat xs f)+(g x+sumNat xs g)
    omega

private theorem nat_sum_one (xs : List A) : sumNat xs (fun _=>1)=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change 1+sumNat xs (fun _=>1)=xs.length+1; omega

private theorem fair_branch (b : B) (bs : List B) (f : List (B×Bool)→Nat) :
    sumNat (fairTags (b::bs)) f =
      sumNat (fairTags bs) (fun z => f ((b,false)::z)) +
      sumNat (fairTags bs) (fun z => f ((b,true)::z)) := by
  rw [fairTags,nat_sum_append]
  simp [sumNat,List.map_map,Function.comp_def]

private def nBin [DecidableEq B] (b : B) (bs : List B) := bs.countP (fun c => decide (c=b))
private def negs [DecidableEq B] (b : B) (z : List (B×Bool)) :=
  (view Prod.fst Prod.snd b z).count false
private def inv [DecidableEq B] (b : B) (z : List (B×Bool)) :=
  inversions (view Prod.fst Prod.snd b z)

private theorem fair_means [DecidableEq B] (b : B) (bs : List B) :
    2*sumNat (fairTags bs) (negs b) = 2^bs.length*nBin b bs ∧
    4*sumNat (fairTags bs) (inv b) = 2^bs.length*pairs (nBin b bs) := by
  induction bs with
  | nil => simp [fairTags,sumNat,negs,inv,view,inversions,nBin,pairs]
  | cons x xs ih =>
    obtain ⟨ihNeg,ihInv⟩ := ih
    have etaN : sumNat (fairTags xs) (fun z => negs b z) = sumNat (fairTags xs) (negs b) := rfl
    have etaI : sumNat (fairTags xs) (fun z => inv b z) = sumNat (fairTags xs) (inv b) := rfl
    simp only [fair_branch,List.length_cons,Nat.pow_succ]
    by_cases eq : x=b
    · subst x
      have neg0 (z) : negs b ((b,false)::z)=negs b z+1 := by simp [negs,view,List.count_cons]
      have neg1 (z) : negs b ((b,true)::z)=negs b z := by simp [negs,view,List.count_cons]
      have inv0 (z) : inv b ((b,false)::z)=inv b z := by simp [inv,view,inversions]
      have inv1 (z) : inv b ((b,true)::z)=negs b z + inv b z := by simp [inv,negs,view,inversions]
      have bins : nBin b (b::xs)=nBin b xs+1 := by simp [nBin,List.countP_cons]
      simp only [neg0,neg1,inv0,inv1,bins,pairs,nat_sum_add,nat_sum_one,fairTags_length]
      have eqn (u a d : Nat) : u*2*(a+d) = 2*(u*a)+2*(u*d) := by
        rw [Nat.mul_add]; ac_rfl
      rw [eqn,eqn]
      simp only [Nat.mul_one]
      omega
    · have simpN (flag) (z) : negs b ((x,flag)::z)=negs b z := by simp [negs,view,eq]
      have simpI (flag) (z) : inv b ((x,flag)::z)=inv b z := by simp [inv,view,eq]
      have bins : nBin b (x::xs)=nBin b xs := by simp [nBin,List.countP_cons,eq]
      simp only [simpN,simpI,bins]
      have eqn (u a : Nat) : u*2*a=2*(u*a) := by ac_rfl
      rw [eqn,eqn]
      omega

/-- For a frozen order with this list of bin labels, the uniform mean
inversion count is exactly one quarter of its number of within-bin pairs.
The formula is cross-multiplied by the size 2^m of the finite sample space. -/
theorem fair_inversion_mean [DecidableEq B] (bins schedule : List B) :
    4 * sumNat (fairTags schedule) (allInversions bins Prod.fst Prod.snd) =
      2^schedule.length * sumNat bins (fun b => pairs (schedule.countP (fun x => decide (x=b)))) := by
  induction bins with
  | nil =>
    change 4*sumNat (fairTags schedule) (fun _=>0)=2^schedule.length*0
    simp only [Nat.mul_zero]
    induction fairTags schedule with
    | nil => rfl
    | cons z zs ih =>
      change 4*(0+sumNat zs (fun _=>0))=0
      simpa only [Nat.zero_add] using ih
  | cons b bins ih =>
    change 4*sumNat (fairTags schedule) (fun z => inv b z + allInversions bins Prod.fst Prod.snd z) =
      2^schedule.length*(pairs (nBin b schedule)+sumNat bins _)
    rw [nat_sum_add,Nat.mul_add,Nat.mul_add,(fair_means b schedule).2,ih]

end Screening.HardBinRegret
