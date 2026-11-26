import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual measure-theoretic KL for a free record with a distinguished silence.
The marked contents may lie in any measurable space. -/

namespace ScreeningAnalysis.GeneralMessageKL

open MeasureTheory InformationTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- A measure-order likelihood band, preserved by a common observation kernel. -/
def RatioBand (e : ℝ) (P Q : Measure α) : Prop :=
  ENNReal.ofReal (1 - e) • Q ≤ P ∧ P ≤ ENNReal.ofReal (1 + e) • Q

/-- A countable public record whose only no-message output per record is the
specified measurable singleton. No measurability of marked singletons is needed. -/
structure Disclosure (F : Type*) (α : Type*) [MeasurableSpace α] where
  cell : F → Set α
  silence : F → α
  cellMeasurable : ∀ f, MeasurableSet (cell f)
  silenceMeasurable : ∀ f, MeasurableSet ({silence f} : Set α)
  silenceInCell : ∀ f, silence f ∈ cell f
  disjointCells : Pairwise (fun a b => Disjoint (cell a) (cell b))
  covers : (⋃ f, cell f) = univ

namespace Disclosure

variable {F : Type*} (d : Disclosure F α)

def marked (f : F) : Set α := d.cell f \ {d.silence f}

def sent : Set α := ⋃ f, d.marked f

theorem markedMeasurable (f : F) : MeasurableSet (d.marked f) :=
  (d.cellMeasurable f).diff (d.silenceMeasurable f)

theorem sentMeasurable [Countable F] : MeasurableSet d.sent :=
  MeasurableSet.iUnion d.markedMeasurable

theorem disjointMarked : Pairwise (fun a b => Disjoint (d.marked a) (d.marked b)) :=
  fun _ _ different => (d.disjointCells different).mono diff_subset diff_subset

theorem cell_split (f : F) : ({d.silence f} : Set α) ∪ d.marked f = d.cell f := by
  have inside : ({d.silence f} : Set α) ⊆ d.cell f := singleton_subset_iff.mpr (d.silenceInCell f)
  ext x
  constructor
  · rintro (silent | marked)
    · exact inside silent
    · exact marked.1
  · intro present
    by_cases silent : x ∈ ({d.silence f} : Set α)
    · exact Or.inl silent
    · exact Or.inr ⟨present, silent⟩

theorem silence_marked_disjoint (f : F) : Disjoint ({d.silence f} : Set α) (d.marked f) :=
  disjoint_left.mpr (fun _ silent marked => marked.2 silent)

end Disclosure

private theorem mass_abs_band {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {e : ℝ} (he : 0 ≤ e) (half : e ≤ 1 / 2) (band : RatioBand e P Q) (s : Set α) :
    |P.real s - Q.real s| ≤ e * Q.real s := by
  have lower : ENNReal.ofReal (1 - e) * Q s ≤ P s := by
    simpa [Measure.smul_apply, smul_eq_mul] using band.1 s
  have upper : P s ≤ ENNReal.ofReal (1 + e) * Q s := by
    simpa [Measure.smul_apply, smul_eq_mul] using band.2 s
  have lo := ENNReal.toReal_mono (measure_ne_top P s) lower
  have hi := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top Q s)) upper
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at lo hi
  simp only [measureReal_def]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem density_ae_band {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {e : ℝ} (band : RatioBand e P Q) :
    ∀ᵐ x ∂Q, ENNReal.ofReal (1 - e) ≤ P.rnDeriv Q x ∧
      P.rnDeriv Q x ≤ ENNReal.ofReal (1 + e) := by
  have ac : P ≪ Q := Measure.absolutelyContinuous_of_le_smul band.2
  have lo : (fun _ : α => ENNReal.ofReal (1 - e)) ≤ᵐ[Q] P.rnDeriv Q := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const
    intro s meas _
    rw [setLIntegral_const, Measure.setLIntegral_rnDeriv' ac meas]
    simpa [Measure.smul_apply, smul_eq_mul] using band.1 s
  have hi : P.rnDeriv Q ≤ᵐ[Q] (fun _ : α => ENNReal.ofReal (1 + e)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (P.measurable_rnDeriv Q)
    intro s meas _
    rw [Measure.setLIntegral_rnDeriv' ac meas, setLIntegral_const]
    simpa [Measure.smul_apply, smul_eq_mul] using band.2 s
  exact lo.and hi

private theorem klFun_le_square {x : ℝ} (hx : 0 ≤ x) :
    klFun x ≤ (x - 1) ^ 2 := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h, klFun_zero]
  · have log := Real.log_le_sub_one_of_pos h
    have prod := mul_le_mul_of_nonneg_left log hx
    unfold klFun
    nlinarith

private theorem abs_square_le {x e : ℝ} (h : |x| ≤ e) (he : 0 ≤ e) : x ^ 2 ≤ e ^ 2 := by
  have mul := mul_le_mul h h (abs_nonneg _) he
  simpa only [← pow_two, sq_abs] using mul

private theorem marked_integral_le {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {e : ℝ} (he : 0 ≤ e) (half : e ≤ 1 / 2) (band : RatioBand e P Q) (s : Set α) :
    (∫⁻ x in s, ENNReal.ofReal (klFun ((P.rnDeriv Q x).toReal)) ∂Q) ≤ ENNReal.ofReal (e ^ 2) * Q s := by
  rw [← setLIntegral_const]
  apply lintegral_mono_ae
  apply ae_restrict_of_ae
  filter_upwards [density_ae_band band] with x hx
  have lo := ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx.2) hx.1
  have hi := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx.2
  rw [ENNReal.toReal_ofReal (by linarith)] at lo hi
  have close : |(P.rnDeriv Q x).toReal - 1| ≤ e :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  exact ENNReal.ofReal_le_ofReal ((klFun_le_square ENNReal.toReal_nonneg).trans (abs_square_le close he))

private theorem square_mul_mass {p q z e : ℝ} (hq : 0 < q) (he : 0 ≤ e)
    (h₁ : |p - q| ≤ e * q) (h₂ : |p - q| ≤ e * z) :
    (p / q - 1)^2 * q ≤ e^2 * z := by
  have prod := mul_le_mul h₁ h₂ (abs_nonneg _) (mul_nonneg he hq.le)
  rw [← pow_two, sq_abs] at prod
  have denominator : (p / q - 1)^2 * q = (p - q)^2 / q := by field_simp; ring
  rw [denominator, div_le_iff₀ hq]
  nlinarith only [prod]

private theorem singleton_rn_mul {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (ac : P ≪ Q) (x : α) (meas : MeasurableSet ({x} : Set α)) :
    P.rnDeriv Q x * Q {x} = P {x} := by
  rw [← lintegral_singleton' (P.measurable_rnDeriv Q), Measure.setLIntegral_rnDeriv' ac meas]

private theorem silence_integral_le {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {e : ℝ} (he : 0 ≤ e) (half : e ≤ 1 / 2) (band : RatioBand e P Q)
    (x : α) (meas : MeasurableSet ({x} : Set α)) (s : Set α)
    (cancellation : |P.real {x} - Q.real {x}| ≤ e * Q.real s) :
    (∫⁻ a in {x}, ENNReal.ofReal (klFun ((P.rnDeriv Q a).toReal)) ∂Q) ≤
      ENNReal.ofReal (e^2) * Q s := by
  rw [lintegral_singleton' (by fun_prop)]
  by_cases zero : Q {x} = 0
  · simp [zero]
  · have positive : 0 < Q.real {x} := ENNReal.toReal_pos zero (measure_ne_top Q _)
    have ac : P ≪ Q := Measure.absolutelyContinuous_of_le_smul band.2
    have rn := congrArg ENNReal.toReal (singleton_rn_mul ac x meas)
    rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def] at rn
    have ratio : (P.rnDeriv Q x).toReal = P.real {x} / Q.real {x} :=
      (eq_div_iff positive.ne').mpr rn
    have square := square_mul_mass positive he (mass_abs_band he half band {x}) cancellation
    calc
      _ = ENNReal.ofReal (klFun ((P.rnDeriv Q x).toReal) * Q.real {x}) := by
        rw [ENNReal.ofReal_mul (klFun_nonneg ENNReal.toReal_nonneg), measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top Q _)]
      _ ≤ ENNReal.ofReal (e^2 * Q.real s) := by
        apply ENNReal.ofReal_le_ofReal
        have h := mul_le_mul_of_nonneg_right
          (klFun_le_square (x := (P.rnDeriv Q x).toReal) ENNReal.toReal_nonneg) positive.le
        exact h.trans (by rwa [ratio])
      _ = _ := by
        rw [ENNReal.ofReal_mul (sq_nonneg e), measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top Q _)]

private theorem same_record_cancels {F : Type*} (d : Disclosure F α)
    {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q] (f : F)
    (same : P (d.cell f) = Q (d.cell f)) :
    P.real {d.silence f} - Q.real {d.silence f} =
      -(P.real (d.marked f) - Q.real (d.marked f)) := by
  have split (R : Measure α) [IsFiniteMeasure R] :
      R.real (d.cell f) = R.real {d.silence f} + R.real (d.marked f) := by
    simp only [measureReal_def]
    rw [← d.cell_split f, measure_union (d.silence_marked_disjoint f) (d.markedMeasurable f),
      ENNReal.toReal_add (measure_ne_top R _) (measure_ne_top R _)]
  have equal : P.real (d.cell f) = Q.real (d.cell f) := congrArg ENNReal.toReal same
  rw [split P, split Q] at equal
  linarith

private theorem record_integral_le {F : Type*} (d : Disclosure F α)
    {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q] {e : ℝ}
    (he : 0 ≤ e) (half : e ≤ 1 / 2) (band : RatioBand e P Q) (f : F)
    (same : P (d.cell f) = Q (d.cell f)) :
    (∫⁻ a in d.cell f, ENNReal.ofReal (klFun ((P.rnDeriv Q a).toReal)) ∂Q) ≤
      (ENNReal.ofReal (e^2) + ENNReal.ofReal (e^2)) * Q (d.marked f) := by
  have cancel : |P.real {d.silence f} - Q.real {d.silence f}| ≤ e * Q.real (d.marked f) := by
    rw [same_record_cancels d f same, abs_neg]
    exact mass_abs_band he half band (d.marked f)
  rw [← d.cell_split f, lintegral_union (d.markedMeasurable f) (d.silence_marked_disjoint f), add_mul]
  exact add_le_add
    (silence_integral_le he half band (d.silence f) (d.silenceMeasurable f) (d.marked f) cancel)
    (marked_integral_le he half band (d.marked f))

/-- Genuine KL for arbitrary measurable marked contents, with countably many
free records. The marked part of a single record may have a nonatomic law. -/
theorem arbitrary_output_information {F : Type*} [Countable F] (d : Disclosure F α)
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] (e : ℝ)
    (he : 0 ≤ e) (half : e ≤ 1 / 2) (band : RatioBand e P Q)
    (same : ∀ f, P (d.cell f) = Q (d.cell f)) :
    klDiv P Q ≤ ENNReal.ofReal (4 * e^2) * P d.sent := by
  have ac : P ≪ Q := Measure.absolutelyContinuous_of_le_smul band.2
  rw [klDiv_eq_lintegral_klFun, if_pos ac, ← setLIntegral_univ,
    ← d.covers, lintegral_iUnion d.cellMeasurable d.disjointCells]
  have markedMass : (∑' f, Q (d.marked f)) = Q d.sent :=
    (measure_iUnion d.disjointMarked d.markedMeasurable).symm
  have sentRatio : Q d.sent ≤ ENNReal.ofReal 2 * P d.sent := by
    have lower := (abs_le.mp (mass_abs_band he half band d.sent)).1
    have halfBound := mul_le_mul_of_nonneg_right half (show 0 ≤ Q.real d.sent from ENNReal.toReal_nonneg)
    have compare : Q.real d.sent ≤ 2 * P.real d.sent := by linarith
    have cast := ENNReal.ofReal_le_ofReal compare
    rwa [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), measureReal_def, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top Q _), ENNReal.ofReal_toReal (measure_ne_top P _)] at cast
  calc
    _ ≤ ∑' f, (ENNReal.ofReal (e^2) + ENNReal.ofReal (e^2)) * Q (d.marked f) :=
      ENNReal.tsum_le_tsum (fun f => record_integral_le d he half band f (same f))
    _ = (ENNReal.ofReal (e^2) + ENNReal.ofReal (e^2)) * Q d.sent := by
      rw [ENNReal.tsum_mul_left, markedMass]
    _ ≤ (ENNReal.ofReal (e^2) + ENNReal.ofReal (e^2)) * (ENNReal.ofReal 2 * P d.sent) :=
      mul_le_mul_left' sentRatio _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_add (sq_nonneg e) (sq_nonneg e),
        ← ENNReal.ofReal_mul (add_nonneg (sq_nonneg e) (sq_nonneg e))]
      ring_nf

/-- The almost-everywhere likelihood-ratio hypothesis in the paper implies
the band in the order of finite measures. -/
theorem ratioBand_of_likelihood {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {e : ℝ} (ac : P ≪ Q)
    (close : ∀ᵐ x ∂Q, |(P.rnDeriv Q x).toReal - 1| ≤ e) :
    RatioBand e P Q := by
  have ratio : ∀ᵐ x ∂Q, ENNReal.ofReal (1 - e) ≤ P.rnDeriv Q x ∧
      P.rnDeriv Q x ≤ ENNReal.ofReal (1 + e) := by
    filter_upwards [close, Measure.rnDeriv_ne_top P Q] with x hx finite
    have bounds := abs_le.mp hx
    have lo : 1 - e ≤ (P.rnDeriv Q x).toReal := by linarith
    have hi : (P.rnDeriv Q x).toReal ≤ 1 + e := by linarith
    simpa only [ENNReal.ofReal_toReal finite] using
      And.intro (ENNReal.ofReal_le_ofReal lo) (ENNReal.ofReal_le_ofReal hi)
  constructor
  · apply Measure.le_iff.mpr
    intro s meas
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [← setLIntegral_const, ← Measure.setLIntegral_rnDeriv' ac meas]
    exact lintegral_mono_ae (ae_restrict_of_ae (ratio.mono fun _ hx => hx.1))
  · apply Measure.le_iff.mpr
    intro s meas
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [← setLIntegral_const, ← Measure.setLIntegral_rnDeriv' ac meas]
    exact lintegral_mono_ae (ae_restrict_of_ae (ratio.mono fun _ hx => hx.2))

private theorem kernel_comp_mono {β : Type*} [MeasurableSpace β] (κ : Kernel α β)
    {P Q : Measure α} (order : P ≤ Q) : κ ∘ₘ P ≤ κ ∘ₘ Q := by
  apply Measure.le_iff.mpr
  intro s meas
  rw [Measure.bind_apply meas κ.aemeasurable, Measure.bind_apply meas κ.aemeasurable]
  exact lintegral_mono' order le_rfl

/-- A common arbitrary randomized kernel preserves the pointwise band,
by positivity of integration on each measurable output event. -/
theorem ratioBand_kernel {β : Type*} [MeasurableSpace β] (κ : Kernel α β)
    {P Q : Measure α} {e : ℝ} (band : RatioBand e P Q) :
    RatioBand e (κ ∘ₘ P) (κ ∘ₘ Q) := by
  constructor
  · rw [← Measure.comp_smul]
    exact kernel_comp_mono κ band.1
  · rw [← Measure.comp_smul]
    exact kernel_comp_mono κ band.2

/-- Actual randomized-encoder information bound for any measurable output
type implementing the public record and silence partition. -/
theorem arbitrary_encoder_information {β F : Type*} [MeasurableSpace β] [Countable F]
    (d : Disclosure F β) (κ : Kernel α β) [IsMarkovKernel κ]
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] (e : ℝ)
    (he : 0 ≤ e) (half : e ≤ 1 / 2) (ac : P ≪ Q)
    (close : ∀ᵐ x ∂Q, |(P.rnDeriv Q x).toReal - 1| ≤ e)
    (same : ∀ f, (κ ∘ₘ P) (d.cell f) = (κ ∘ₘ Q) (d.cell f)) :
    klDiv (κ ∘ₘ P) (κ ∘ₘ Q) ≤ ENNReal.ofReal (4 * e^2) * (κ ∘ₘ P) d.sent :=
  arbitrary_output_information d (κ ∘ₘ P) (κ ∘ₘ Q) e he half
    (ratioBand_kernel κ (ratioBand_of_likelihood ac close)) same

/-- Usual record-and-message output. The left branch is silence, and the
right branch may be any measurable content type. -/
noncomputable def productDisclosure (F A : Type*) [MeasurableSpace F] [MeasurableSingletonClass F]
    [MeasurableSpace A] : Disclosure F (F × (Unit ⊕ A)) where
  cell f := Prod.fst ⁻¹' {f}
  silence f := (f, Sum.inl ())
  cellMeasurable f := measurable_fst (measurableSet_singleton f)
  silenceMeasurable f := by
    have identity : ({(f, Sum.inl ())} : Set (F × (Unit ⊕ A))) =
        ({f} : Set F) ×ˢ (Set.range Sum.inl : Set (Unit ⊕ A)) := by
      ext ⟨x, b⟩
      cases b with
      | inl u => cases u; simp
      | inr a => simp
    rw [identity]
    exact (measurableSet_singleton f).prod measurableSet_range_inl
  silenceInCell f := by simp
  disjointCells := by
    intro f g different
    apply disjoint_left.mpr
    intro x hf hg
    exact different ((Set.mem_singleton_iff.mp hf).symm.trans (Set.mem_singleton_iff.mp hg))
  covers := by
    ext x
    constructor
    · intro _
      exact mem_univ _
    · intro _
      exact mem_iUnion.mpr ⟨x.1, by simp⟩

theorem productDisclosure_sent (F A : Type*) [MeasurableSpace F] [MeasurableSingletonClass F]
    [MeasurableSpace A] :
    (productDisclosure F A).sent = Prod.snd ⁻¹' (Set.range Sum.inr : Set (Unit ⊕ A)) := by
  ext ⟨x, b⟩
  cases b with
  | inl u => cases u; simp [Disclosure.sent, Disclosure.marked, productDisclosure]
  | inr a => simp [Disclosure.sent, Disclosure.marked, productDisclosure]

/-- Full pushforward form of the public-record lemma with arbitrary
measurable message contents and a common randomized Markov encoder.
The kernel preserves the declared free record and may choose both whether
to send and the message law from the entire current input. -/
theorem product_encoder_information {F A : Type*} [Countable F] [MeasurableSpace F]
    [MeasurableSingletonClass F] [MeasurableSpace A]
    (κ : Kernel α (F × (Unit ⊕ A))) [IsMarkovKernel κ]
    (record : α → F) (recordMeas : Measurable record)
    (preserves : κ.map Prod.fst = Kernel.deterministic record recordMeas)
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] (e : ℝ)
    (he : 0 ≤ e) (half : e ≤ 1 / 2) (ac : P ≪ Q)
    (close : ∀ᵐ x ∂Q, |(P.rnDeriv Q x).toReal - 1| ≤ e)
    (sameFree : P.map record = Q.map record) :
    klDiv (κ ∘ₘ P) (κ ∘ₘ Q) ≤
      ENNReal.ofReal (4 * e^2) * (κ ∘ₘ P) (Prod.snd ⁻¹' Set.range Sum.inr) := by
  rw [← productDisclosure_sent F A]
  apply arbitrary_encoder_information (productDisclosure F A) κ P Q e he half ac close
  intro f
  change (κ ∘ₘ P) (Prod.fst ⁻¹' {f}) = (κ ∘ₘ Q) (Prod.fst ⁻¹' {f})
  rw [← Measure.map_apply measurable_fst (measurableSet_singleton f),
    ← Measure.map_apply measurable_fst (measurableSet_singleton f),
    Measure.map_comp P κ measurable_fst, Measure.map_comp Q κ measurable_fst,
    preserves, Measure.deterministic_comp_eq_map, Measure.deterministic_comp_eq_map, sameFree]

end ScreeningAnalysis.GeneralMessageKL
