import Std

/-! Reciprocal reduction and the packed unsigned divisibility test. -/
namespace Screening.PacketArithmetic

def quotient (B v n : Nat) : Nat := n*v/B

def residue (B M v n : Nat) : Nat := n - quotient B v n * M

/-- Both floor(B/M) and floor((B−1)/M) are valid reciprocals. The
second is exactly the reciprocal computed from UINT64_MAX in packet.hpp. -/
def ValidReciprocal (B M v : Nat) : Prop :=
  v*M ≤ B ∧ B ≤ v*M + M

theorem floor_reciprocal {B M : Nat} (hm : 0 < M) : ValidReciprocal B M (B/M) := by
  constructor
  · exact Nat.div_mul_le_self _ _
  · have h := Nat.div_add_mod B M
    have hmod := Nat.mod_lt B hm
    rw [Nat.mul_comm M] at h
    omega

theorem maxword_reciprocal {B M : Nat} (hB : 0 < B) (hm : 0 < M) :
    ValidReciprocal B M ((B-1)/M) := by
  constructor
  · exact Nat.le_trans (Nat.div_mul_le_self _ _) (Nat.sub_le _ _)
  · have h := Nat.div_add_mod (B-1) M
    have hmod := Nat.mod_lt (B-1) hm
    rw [Nat.mul_comm M] at h
    omega

/-- The estimated product never exceeds n, and one more correction
beyond the next multiple of M exceeds n strictly. -/
theorem bracket {B M v n : Nat} (hm : 0 < M) (hn : n < B)
    (hv : ValidReciprocal B M v) :
    quotient B v n * M ≤ n ∧ n < (quotient B v n + 2)*M := by
  have hB : 0 < B := by omega
  obtain ⟨hvlo,hvhi⟩ := hv
  let q := quotient B v n
  have hlo : q*B ≤ n*v := Nat.div_mul_le_self _ _
  have hhi : n*v < (q+1)*B :=
    (Nat.div_lt_iff_lt_mul hB).mp (Nat.lt_succ_self q)
  constructor
  · apply Nat.le_of_mul_le_mul_left (c := B) _ hB
    calc B*(q*M) = (q*B)*M := by ac_rfl
         _ ≤ (n*v)*M := Nat.mul_le_mul_right M hlo
         _ = n*(v*M) := Nat.mul_assoc _ _ _
         _ ≤ n*B := Nat.mul_le_mul_left n hvlo
         _ = B*n := Nat.mul_comm _ _
  · apply Nat.lt_of_mul_lt_mul_left (a := B)
    calc B*n = n*B := Nat.mul_comm _ _
         _ ≤ n*(v*M+M) := Nat.mul_le_mul_left n hvhi
         _ = (n*v)*M+n*M := by rw [Nat.mul_add, Nat.mul_assoc]
         _ < ((q+1)*B)*M+B*M :=
           Nat.add_lt_add (Nat.mul_lt_mul_of_pos_right hhi hm)
             (Nat.mul_lt_mul_of_pos_right hn hm)
         _ = B*((q+2)*M) := by
           simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, Nat.two_mul,
             Nat.mul_two]
           ac_rfl

theorem quotient_exact_or_one_low {B M v n : Nat} (hm : 0 < M) (hn : n < B)
    (hv : ValidReciprocal B M v) :
    n/M = quotient B v n ∨ n/M = quotient B v n + 1 := by
  obtain ⟨hl,hu⟩ := bracket hm hn hv
  have hlo := (Nat.le_div_iff_mul_le hm).mpr hl
  have hhi := (Nat.div_lt_iff_lt_mul hm).mpr hu
  omega

theorem residue_lt_twice {B M v n : Nat} (hm : 0 < M) (hn : n < B)
    (hv : ValidReciprocal B M v) : residue B M v n < 2*M := by
  obtain ⟨hl,hu⟩ := bracket hm hn hv
  rw [Nat.add_mul] at hu
  unfold residue
  omega

theorem residue_dvd_iff {B M v n p : Nat} (hm : 0 < M) (hn : n < B)
    (hv : ValidReciprocal B M v) (hp : p ∣ M) :
    p ∣ residue B M v n ↔ p ∣ n := by
  have hprod := Nat.dvd_trans hp (Nat.dvd_mul_left M (quotient B v n))
  have heq : residue B M v n + quotient B v n*M = n :=
    Nat.sub_add_cancel (bracket hm hn hv).1
  constructor
  · intro hr
    rw [← heq]
    exact Nat.dvd_add hr hprod
  · intro h
    exact Nat.dvd_sub h hprod

/-- A 32-bit machine subtraction can use only the low input and quotient:
they recover the *entire* mathematical remainder, since it fits in one lane. -/
private theorem ofNat_mul (width a b : Nat) :
    BitVec.ofNat width a * BitVec.ofNat width b = BitVec.ofNat width (a*b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mul_mod, Nat.mul_mod_mod]

theorem low_lane_reduction {width n q M : Nat} (hl : q*M ≤ n)
    (hfits : n-q*M < 2^width) :
    (BitVec.ofNat width n - BitVec.ofNat width q * BitVec.ofNat width M).toNat = n-q*M := by
  have heq : BitVec.ofNat width n - BitVec.ofNat width q * BitVec.ofNat width M =
      BitVec.ofNat width (n-q*M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    rw [ofNat_mul, ← BitVec.ofNat_add, Nat.sub_add_cancel hl]
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfits]

theorem packet64 {n M : Nat} (hn : n < 2^64) (hm : 0 < M) (hsize : M < 2^31) :
    let v := (2^64-1)/M
    let q := quotient (2^64) v n
    let r := residue (2^64) M v n
    (n/M = q ∨ n/M = q+1) ∧ r < 2*M ∧ r < 2^32 ∧
    (BitVec.ofNat 32 n - BitVec.ofNat 32 q * BitVec.ofNat 32 M).toNat = r ∧
    (∀ p, p ∣ M → (p ∣ r ↔ p ∣ n)) := by
  dsimp only
  have hv := maxword_reciprocal (B := 2^64) (by decide) hm
  have hr := residue_lt_twice hm hn hv
  have h32 : residue (2^64) M ((2^64-1)/M) n < 2^32 := by omega
  exact ⟨quotient_exact_or_one_low hm hn hv,hr,h32,
    low_lane_reduction (bracket hm hn hv).1 h32, fun _ hp => residue_dvd_iff hm hn hv hp⟩

/-- Multiplication by a modular inverse turns divisibility into one unsigned
comparison. The inverse identity is a precondition on the supplied table. -/
theorem inverse_cutoff {W p a r : Nat} (hp : 0 < p) (hr : r < W)
    (hinv : (p*a)%W = 1) :
    (r*a)%W ≤ (W-1)/p ↔ p ∣ r := by
  have cancel (k : Nat) : k*(p*a)%W = k%W := by
    rw [← Nat.mul_mod_mod k (p*a) W, hinv, Nat.mul_one]
  constructor
  · intro h
    let k := (r*a)%W
    have hkp : k*p ≤ W-1 := (Nat.le_div_iff_mul_le hp).mp h
    have hk : k*p < W := by omega
    have heq : k*p = r := calc
      k*p = k*p%W := (Nat.mod_eq_of_lt hk).symm
      _ = (r*a)*p%W := Nat.mod_mul_mod (r*a) p W
      _ = r*(p*a)%W := by ac_rfl
      _ = r%W := cancel r
      _ = r := Nat.mod_eq_of_lt hr
    exact ⟨k, by rw [← heq, Nat.mul_comm]⟩
  · rintro ⟨k,rfl⟩
    have hk : k < W :=
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left k hp) hr
    have heq : (p*k)*a%W = k := calc
      _ = k*(p*a)%W := by ac_rfl
      _ = k%W := cancel k
      _ = k := Nat.mod_eq_of_lt hk
    rw [heq]
    apply (Nat.le_div_iff_mul_le hp).mpr
    rw [Nat.mul_comm]
    omega

/-- Truncating a full-word inverse to a lane preserves the inverse identity. -/
theorem low32_inverse {p a : Nat} (hinv : (p*a)%(2^64) = 1) :
    (p*(a%(2^32)))%(2^32) = 1 := by
  rw [Nat.mul_mod_mod, ← Nat.mod_mod_of_dvd (p*a) (show 2^32 ∣ 2^64 by decide), hinv]

/-- Complete single-slot predicate of the 32-bit SIMD screen, from the high
product quotient through the wrapped lane product and unsigned comparison. -/
theorem packed_test64 {n M p a : Nat} (hn : n < 2^64) (hm : 0 < M)
    (hsize : M < 2^31) (hp : 0 < p) (hpm : p ∣ M)
    (hinv : (p*a)%(2^64) = 1) :
    let q := quotient (2^64) ((2^64-1)/M) n
    let lane := BitVec.ofNat 32 n - BitVec.ofNat 32 q * BitVec.ofNat 32 M
    (lane * BitVec.ofNat 32 a).toNat ≤ (2^32-1)/p ↔ p ∣ n := by
  dsimp only
  obtain ⟨_,_,hfits,hlane,hdiv⟩ := packet64 hn hm hsize
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hlane]
  exact (inverse_cutoff hp hfits (low32_inverse hinv)).trans (hdiv p hpm)

end Screening.PacketArithmetic
