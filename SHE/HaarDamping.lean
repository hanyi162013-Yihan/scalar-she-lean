module

public import SHE.HaarLimit
public import SHE.SignedDamping
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.FiniteHaar
open MeasureTheory AddCircle CircleHeat Set
open scoped ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : MeasurableSpace CircleL2 := borel CircleL2
local instance : BorelSpace CircleL2 := ⟨rfl⟩

theorem measurable_detailColumn (n : ℕ) (i : DetailIndex n) (x : Grid n) :
    Measurable (fun a : Grid n → ℝ => detailColumn n a i x) := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    have hleft : Measurable (fun a : Grid (n+1) → ℝ => fun y : Grid n => a (Sum.inl y)) :=
      Measurable.of_eval (fun y => measurable_pi_apply (Sum.inl y))
    have hright : Measurable (fun a : Grid (n+1) → ℝ => fun y : Grid n => a (Sum.inr y)) :=
      Measurable.of_eval (fun y => measurable_pi_apply (Sum.inr y))
    have hL := (continuous_totalMass n).measurable.comp hleft
    have hR := (continuous_totalMass n).measurable.comp hright
    rcases i with ⟨⟩ | (i | i) <;> rcases x with x | x
    · simp only [detailColumn,Sum.elim_inl]
      unfold haarLeft haarMass
      exact ((hL.mul hR).div (hL.add hR)).sqrt.div hL
    · simp only [detailColumn,Sum.elim_inr]
      unfold haarRight haarMass
      exact ((hL.mul hR).div (hL.add hR)).sqrt.neg.div hR
    · exact (ih i x).comp hleft
    · exact measurable_const
    · exact measurable_const
    · exact (ih i x).comp hright

theorem measurable_haarColumn (n : ℕ) (i : Option (DetailIndex n)) (x : Grid n) :
    Measurable (fun a : Grid n → ℝ => haarColumn n a i x) := by
  cases i with
  | none => exact (continuous_totalMass n).measurable.sqrt.inv
  | some i => exact measurable_detailColumn n i x

/-- Even at singular local mass values the literal coefficient-to-column
formula is Borel measurable. Positivity is needed for continuity and the
estimates, not for this measurability statement. -/
theorem measurable_fixedHaarColumn (n : ℕ) (i : Option (DetailIndex n)) :
    Measurable (fixedHaarColumn n i) := by
  unfold fixedHaarColumn
  apply Finset.measurable_fun_sum
  intro x hx
  exact (measurable_const.mul ((measurable_haarColumn n i x).comp
    (continuous_localAverage n).measurable)).smul (cellRestriction n x).continuous.measurable

theorem measurable_globalHaarColumn (q : HaarNode) :
    Measurable (globalHaarColumn q) := measurable_fixedHaarColumn _ _

theorem measurable_globalSignedColumn (q : HaarNode) :
    Measurable (fun p : CircleL2 × CircleL2 => globalSignedColumn q p.1 p.2) :=
  ((measurable_globalHaarColumn q).comp measurable_fst).sub
    ((measurable_globalHaarColumn q).comp measurable_snd)

theorem measurable_globalSignedHeatAction (q : HaarNode) :
    Measurable (fun p : ℝ × (CircleL2 × CircleL2) =>
      heat p.1 (globalSignedColumn q p.2.1 p.2.2)) := by
  exact Continuous.measurable2 (c := fun (t:ℝ) (f:CircleL2) => heat t f)
    continuous_heat_action measurable_fst
    ((measurable_globalSignedColumn q).comp measurable_snd)

/-- The actual countable squared signed Haar column energy. -/
def globalSignedHeatEnergy (f g : CircleL2) (t : ℝ) : ℝ :=
  ∑' q : HaarNode, ‖heat t (globalSignedColumn q f g)‖ ^ 2

theorem globalSignedHeatEnergy_nonneg (f g : CircleL2) (t : ℝ) :
    0 ≤ globalSignedHeatEnergy f g t := tsum_nonneg (fun _ => sq_nonneg _)

theorem measurable_globalSignedHeatEnergy (f g : CircleL2) :
    Measurable (globalSignedHeatEnergy f g) := by
  exact Measurable.tsum (fun q : HaarNode => (continuous_heat_energy
    (globalSignedColumn q f g)).measurable)

theorem signedHeatSqConstant_nonneg {κ ρ m U : ℝ}
    (hκ : 0 ≤ κ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (hU : 0 ≤ U) :
    0 ≤ signedHeatSqConstant κ ρ m U := by
  exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
    (mul_nonneg (div_nonneg hU (sq_nonneg m)) (inverseConstant_nonneg hκ hρ hρhalf)))
    (sq_nonneg _)

/-- The physical real coefficient difference has an actual finite `L²`
norm, bounded only by the ellipticity interval width. -/
theorem elliptic_difference_norm_le (f g : CircleL2) {m U : ℝ}
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hgreal : ∀ᵐ y ∂haarAddCircle, (g y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hg : ∀ᵐ y ∂haarAddCircle, m ≤ (g y).re ∧ (g y).re ≤ U) :
    ‖f-g‖ ≤ U-m := by
  have hwidth : 0 ≤ U-m := by
    obtain ⟨y,hy⟩ := hf.exists
    linarith [hy.1, hy.2]
  have hae : ∀ᵐ y ∂haarAddCircle, ‖(f-g) y‖ ≤ U-m := by
    filter_upwards [Lp.coeFn_sub f g, hfreal, hgreal, hf, hg] with y hy hfr hgr hfb hgb
    have he : f y-g y = (((f y).re-(g y).re:ℝ):ℂ) := by
      apply Complex.ext <;> simp [hfr,hgr]
    rw [hy]
    change ‖f y-g y‖ ≤ U-m
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hfb.1,hfb.2,hgb.1,hgb.2],
      by linarith [hfb.1,hfb.2,hgb.1,hgb.2]⟩
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hwidth hae

theorem elliptic_negative_input_le {κ Λ ρ : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ)
    (f g : CircleL2) {m U : ℝ}
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hgreal : ∀ᵐ y ∂haarAddCircle, (g y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hg : ∀ᵐ y ∂haarAddCircle, m ≤ (g y).re ∧ (g y).re ≤ U) :
    StepInput.negativeEnergy κ Λ ρ (f-g) ≤ Λ ^ (-ρ) * (U-m) ^ 2 := by
  exact (negativeEnergy_le_L2 hΛ hρ _).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (elliptic_difference_norm_le f g hfreal hgreal hf hg) 2)
      (Real.rpow_nonneg hΛ.le _))

theorem globalSignedHeatEnergy_bound {t κ Λ ρ : ℝ}
    (ht : 0 < t) (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hgreal : ∀ᵐ y ∂haarAddCircle, (g y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hg : ∀ᵐ y ∂haarAddCircle, m ≤ (g y).re ∧ (g y).re ≤ U) :
    globalSignedHeatEnergy f g t ≤
      signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (f-g) *
        (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1)) := by
  have hU : 0 ≤ U := by
    obtain ⟨y,hy⟩ := hf.exists
    exact hm.le.trans (hy.1.trans hy.2)
  have hC := mul_nonneg (signedHeatSqConstant_nonneg (m := m) hκ hρ hρhalf hU)
    (negativeEnergy_nonneg κ ρ hΛ.le (f-g))
  by_cases ht1 : t ≤ 1
  · exact (global_signed_heat ht ht1 hκ hΛ hρ hρhalf f g m U hm hfreal hgreal hf hg).2.trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hC)
  · exact (global_signed_heat_tail (le_of_lt (lt_of_not_ge ht1)) hκ hΛ hρ hρhalf
      f g m U hm hfreal hgreal hf hg).2.trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hC)

/-- Actual infinite-noise signed column energy has the exact massive
damping power, for arbitrary real bounded elliptic `L²` coefficients. -/
theorem damped_globalSignedHeatEnergy {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hgreal : ∀ᵐ y ∂haarAddCircle, (g y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hg : ∀ᵐ y ∂haarAddCircle, m ≤ (g y).re ∧ (g y).re ≤ U) :
    IntegrableOn (fun t => Real.exp (-2*Λ*t) * globalSignedHeatEnergy f g t) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ), Real.exp (-2*Λ*t) * globalSignedHeatEnergy f g t) ≤
        (signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (f-g) *
          signedDampingConstant ρ) * Λ ^ (ρ-1/2) := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hU : 0 ≤ U := by
    obtain ⟨y,hy⟩ := hf.exists
    exact hm.le.trans (hy.1.trans hy.2)
  have hC := mul_nonneg (signedHeatSqConstant_nonneg (m := m) hκ hρ hρhalf hU)
    (negativeEnergy_nonneg κ ρ hΛp.le (f-g))
  have hh := damped_signed_energy_of_heat_bound (F:=1) hΛ hρ.le hρhalf hC
    (measurable_globalSignedHeatEnergy f g).aestronglyMeasurable
    (Filter.Eventually.of_forall (globalSignedHeatEnergy_nonneg f g)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [one_pow,mul_one] using globalSignedHeatEnergy_bound ht hκ hΛp hρ hρhalf
        f g m U hm hfreal hgreal hf hg)
  simpa only [one_pow,mul_one] using hh

/-- The countable signed columns are integrated on the actual ordered
time triangle. The causal convolution estimate preserves the negative
input energy of the coefficient difference. -/
theorem signed_global_causal_energy {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f g : ℝ → CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ s, ∀ᵐ y ∂haarAddCircle, (f s y).im = 0)
    (hgreal : ∀ s, ∀ᵐ y ∂haarAddCircle, (g s y).im = 0)
    (hf : ∀ s, ∀ᵐ y ∂haarAddCircle, m ≤ (f s y).re ∧ (f s y).re ≤ U)
    (hg : ∀ s, ∀ᵐ y ∂haarAddCircle, m ≤ (g s y).re ∧ (g s y).re ≤ U)
    (hmf : Measurable f) (hmg : Measurable g) (T : ℝ) :
    (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t,
      ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * globalSignedHeatEnergy (f s) (g s) (t-s))) ≤
      ENNReal.ofReal ((signedHeatSqConstant κ ρ m U * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) *
        ∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal (StepInput.negativeEnergy κ Λ ρ (f s-g s)) := by
  let C := signedHeatSqConstant κ ρ m U
  let F := fun s => ENNReal.ofReal (StepInput.negativeEnergy κ Λ ρ (f s-g s))
  let K := fun t => ENNReal.ofReal C * signedDampedKernel Λ ρ t
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hF : Measurable F := ENNReal.continuous_ofReal.measurable.comp
    ((continuous_negativeEnergy hΛp hρ.le).measurable.comp (hmf.sub hmg))
  have hU : 0 ≤ U := by
    obtain ⟨y,hy⟩ := (hf 0).exists
    exact hm.le.trans (hy.1.trans hy.2)
  have hC : 0 ≤ C := signedHeatSqConstant_nonneg hκ hρ hρhalf hU
  have hK : Measurable K := measurable_const.mul (measurable_signedDampedKernel Λ ρ)
  have hmass : (∫⁻ t : ℝ, K t) ≤
      ENNReal.ofReal ((C * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) := by
    calc
      _ = ENNReal.ofReal C * ∫⁻ t : ℝ, signedDampedKernel Λ ρ t :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (signedDampingConstant ρ * Λ ^ (ρ-1/2)) :=
        mul_le_mul_right (signedDampedKernel_mass hΛ hρ.le hρhalf) _
      _ = _ := by rw [← ENNReal.ofReal_mul hC]; congr 1; ring
  have hpoint (t s : ℝ) (hs : s ∈ Ioo (0:ℝ) t) :
      ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * globalSignedHeatEnergy (f s) (g s) (t-s)) ≤
        K (t-s) * F s := by
    have hage : 0 < t-s := sub_pos.mpr hs.2
    have hh := globalSignedHeatEnergy_bound hage hκ hΛp hρ hρhalf (f s) (g s) m U hm
      (hfreal s) (hgreal s) (hf s) (hg s)
    have hmaj : 0 ≤ Real.exp (-2*Λ*(t-s)) *
        (Λ ^ ρ * (t-s) ^ (-(1/2:ℝ)) + (t-s) ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1)) := by positivity
    apply (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le)).trans_eq
    dsimp only [K,F,signedDampedKernel]
    rw [Set.indicator_of_mem (show t-s ∈ Ioi (0:ℝ) from hage)]
    rw [show Real.exp (-2*Λ*(t-s)) * (signedHeatSqConstant κ ρ m U *
      StepInput.negativeEnergy κ Λ ρ (f s-g s) *
        (Λ ^ ρ * (t-s) ^ (-(1/2:ℝ)) + (t-s) ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) =
      C * (Real.exp (-2*Λ*(t-s)) *
        (Λ ^ ρ * (t-s) ^ (-(1/2:ℝ)) + (t-s) ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) *
          StepInput.negativeEnergy κ Λ ρ (f s-g s) by dsimp only [C]; ring]
    rw [ENNReal.ofReal_mul (mul_nonneg hC hmaj),ENNReal.ofReal_mul hC]
  calc
    _ ≤ ∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t, K (t-s) * F s := by
      apply lintegral_mono
      intro t
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hpoint t s hs
    _ ≤ ∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioc (0:ℝ) t, K (t-s) * F s :=
      lintegral_mono (fun t => lintegral_mono_set Ioo_subset_Ioc_self)
    _ ≤ (∫⁻ t : ℝ, K t) * ∫⁻ s in Ioc (0:ℝ) T, F s :=
      causal_convolution_energy_bound K F hK hF T
    _ ≤ _ := mul_le_mul_left hmass _

/-- Expectation preserves the countable-column causal estimate even for
dependent coefficient processes. -/
theorem signed_global_random_causal_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f g : Ω → ℝ → CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ ω s, ∀ᵐ y ∂haarAddCircle, (f ω s y).im = 0)
    (hgreal : ∀ ω s, ∀ᵐ y ∂haarAddCircle, (g ω s y).im = 0)
    (hf : ∀ ω s, ∀ᵐ y ∂haarAddCircle, m ≤ (f ω s y).re ∧ (f ω s y).re ≤ U)
    (hg : ∀ ω s, ∀ᵐ y ∂haarAddCircle, m ≤ (g ω s y).re ∧ (g ω s y).re ≤ U)
    (hmf : ∀ ω, Measurable (f ω)) (hmg : ∀ ω, Measurable (g ω)) (T : ℝ) :
    (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t,
      ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * globalSignedHeatEnergy (f ω s) (g ω s) (t-s))) ∂μ) ≤
      ENNReal.ofReal ((signedHeatSqConstant κ ρ m U * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) *
        ∫⁻ ω, (∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal
          (StepInput.negativeEnergy κ Λ ρ (f ω s-g ω s))) ∂μ := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((signedHeatSqConstant κ ρ m U * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) *
      (∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal (StepInput.negativeEnergy κ Λ ρ (f ω s-g ω s))) ∂μ :=
      lintegral_mono (fun ω => signed_global_causal_energy hκ hΛ hρ hρhalf
        (f ω) (g ω) m U hm (hfreal ω) (hgreal ω) (hf ω) (hg ω) (hmf ω) (hmg ω) T)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem elliptic_random_input_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {κ Λ ρ : ℝ}
    (hΛ : 0 < Λ) (hρ : 0 ≤ ρ)
    (f g : Ω → ℝ → CircleL2) (m U T : ℝ)
    (hfreal : ∀ ω s, ∀ᵐ y ∂haarAddCircle, (f ω s y).im = 0)
    (hgreal : ∀ ω s, ∀ᵐ y ∂haarAddCircle, (g ω s y).im = 0)
    (hf : ∀ ω s, ∀ᵐ y ∂haarAddCircle, m ≤ (f ω s y).re ∧ (f ω s y).re ≤ U)
    (hg : ∀ ω s, ∀ᵐ y ∂haarAddCircle, m ≤ (g ω s y).re ∧ (g ω s y).re ≤ U) :
    (∫⁻ ω, (∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal
      (StepInput.negativeEnergy κ Λ ρ (f ω s-g ω s))) ∂μ) ≤
        ENNReal.ofReal (Λ ^ (-ρ) * (U-m) ^ 2) * ENNReal.ofReal T := by
  calc
    _ ≤ ∫⁻ _ω : Ω, (∫⁻ _s in Ioc (0:ℝ) T, ENNReal.ofReal (Λ ^ (-ρ) * (U-m) ^ 2)) ∂μ := by
      apply lintegral_mono
      intro ω
      apply lintegral_mono
      intro s
      exact ENNReal.ofReal_le_ofReal (elliptic_negative_input_le hΛ hρ (f ω s) (g ω s)
        (hfreal ω s) (hgreal ω s) (hf ω s) (hg ω s))
    _ = _ := by simp [Real.volume_Ioc]

/-- The actual countable random causal energy is finite. In particular,
the signed estimate is not a comparison of two infinite quantities. -/
theorem signed_global_random_causal_energy_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f g : Ω → ℝ → CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ ω s, ∀ᵐ y ∂haarAddCircle, (f ω s y).im = 0)
    (hgreal : ∀ ω s, ∀ᵐ y ∂haarAddCircle, (g ω s y).im = 0)
    (hf : ∀ ω s, ∀ᵐ y ∂haarAddCircle, m ≤ (f ω s y).re ∧ (f ω s y).re ≤ U)
    (hg : ∀ ω s, ∀ᵐ y ∂haarAddCircle, m ≤ (g ω s y).re ∧ (g ω s y).re ≤ U)
    (hmf : ∀ ω, Measurable (f ω)) (hmg : ∀ ω, Measurable (g ω)) (T : ℝ) :
    (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t,
      ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * globalSignedHeatEnergy (f ω s) (g ω s) (t-s))) ∂μ) < ∞ := by
  have he := signed_global_random_causal_energy μ hκ hΛ hρ hρhalf f g m U hm
    hfreal hgreal hf hg hmf hmg T
  have hi := elliptic_random_input_energy (κ:=κ) μ (zero_lt_one.trans_le hΛ) hρ.le
    f g m U T hfreal hgreal hf hg
  apply he.trans_lt
  apply (mul_le_mul_right hi _).trans_lt
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- Standard stochastic isometry is the sole stochastic input in this
interface. Its exact integrand is the constructed countable signed Haar
family, and its massive analytic estimate is proved above. -/
theorem signed_global_stochastic_energy_of_isometry {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f g : Ω → ℝ → CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ ω s, ∀ᵐ y ∂haarAddCircle, (f ω s y).im = 0)
    (hgreal : ∀ ω s, ∀ᵐ y ∂haarAddCircle, (g ω s y).im = 0)
    (hf : ∀ ω s, ∀ᵐ y ∂haarAddCircle, m ≤ (f ω s y).re ∧ (f ω s y).re ≤ U)
    (hg : ∀ ω s, ∀ᵐ y ∂haarAddCircle, m ≤ (g ω s y).re ∧ (g ω s y).re ≤ U)
    (hmf : ∀ ω, Measurable (f ω)) (hmg : ∀ ω, Measurable (g ω)) (T : ℝ)
    (Z : Ω → ℝ → CircleL2)
    (hIsometry : (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal (‖Z ω t‖ ^ 2)) ∂μ) =
      ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t,
        ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * globalSignedHeatEnergy (f ω s) (g ω s) (t-s))) ∂μ) :
    (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal (‖Z ω t‖ ^ 2)) ∂μ) ≤
      ENNReal.ofReal ((signedHeatSqConstant κ ρ m U * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) *
        ∫⁻ ω, (∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal
          (StepInput.negativeEnergy κ Λ ρ (f ω s-g ω s))) ∂μ := by
  rw [hIsometry]
  exact signed_global_random_causal_energy μ hκ hΛ hρ hρhalf f g m U hm
    hfreal hgreal hf hg hmf hmg T

end SHE.FiniteHaar
