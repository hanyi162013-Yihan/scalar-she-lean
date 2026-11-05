module

public import SHE.HaarTaylorHeat
public import SHE.HeatTorusKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.HeatMarkov
open Finset Set MeasureTheory AddCircle CircleHeat
open SHE.HeatLine SHE.HeatPeriodization SHE.HeatTorusKernel SHE.FourierHeatLine
open scoped ENNReal
local instance heatMarkov_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance heatMarkov_nativePos : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem singleHeat_span (t : ℝ) : heatEntire t 0 ∈
    Submodule.span ℂ (Set.range (fun _ : Fin 1 => heatEntire t 0)) :=
  Submodule.subset_span ⟨0,rfl⟩

/-- The actual continuous normalized positive Gaussian periodization. -/
def kernel (t : ℝ) (ht : 0 < t) : C(AddCircle (1:ℝ), ℂ) :=
  (heatMass t : ℂ)⁻¹ • circlePeriodize (fun _ : Fin 1 => t) (fun _ => 0)
    (fun _ => ht) (heatEntire t 0) (singleHeat_span t)

theorem kernel_fourierCoeff {t : ℝ} (ht : 0 < t) (n : ℤ) :
    fourierCoeff (kernel t ht) n = heatWeight t n := by
  change fourierCoeff ((heatMass t : ℂ)⁻¹ •
    (circlePeriodize (fun _ : Fin 1 => t) (fun _ => 0) (fun _ => ht)
      (heatEntire t 0) (singleHeat_span t) : AddCircle (1:ℝ) → ℂ)) n = _
  rw [fourierCoeff.const_smul, fourierCoeff_circlePeriodize, fourier_heatEntire ht, Complex.ofReal_intCast,
    HeatTorusKernel.frequencyGaussian_integer]
  simp only [smul_eq_mul, AddCircle.coe_zero, fourier_eval_zero, one_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (heatMass_pos ht).ne'), one_mul]
  unfold heatWeight
  rw [max_eq_left ht.le]
  rw [show -(4*Real.pi^2*t)*(n:ℝ)^2 = -t*(2*Real.pi*(n:ℝ))^2 by ring]

theorem kernel_real_nonneg {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    (kernel t ht x).im = 0 ∧ 0 ≤ (kernel t ht x).re := by
  induction x using Quotient.inductionOn with
  | _ r =>
    change ((heatMass t : ℂ)⁻¹ *
      circlePeriodize (fun _ : Fin 1 => t) (fun _ => 0) (fun _ => ht)
        (heatEntire t 0) (singleHeat_span t) (r : AddCircle (1:ℝ))).im = 0 ∧
      0 ≤ ((heatMass t : ℂ)⁻¹ *
      circlePeriodize (fun _ : Fin 1 => t) (fun _ => 0) (fun _ => ht)
        (heatEntire t 0) (singleHeat_span t) (r : AddCircle (1:ℝ))).re
    rw [circlePeriodize_coe]
    unfold periodize
    have he (n : ℤ) : heatEntire t 0 ((r+(n:ℝ) : ℝ) : ℂ) =
        (Real.exp (-((r+(n:ℝ))^2)/(4*t)) : ℂ) := by
      simp only [heatEntire, Complex.ofReal_zero, sub_zero]
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      rfl
    simp_rw [he]
    rw [← Complex.ofReal_tsum, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    exact ⟨Complex.ofReal_im _, by
      change 0 ≤ (heatMass t)⁻¹ * ∑' n : ℤ, Real.exp (-((r+(n:ℝ))^2)/(4*t))
      exact mul_nonneg (inv_nonneg.mpr (heatMass_pos ht).le) (tsum_nonneg (fun _ => (Real.exp_pos _).le))⟩

theorem kernel_norm_eq_re {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    ‖kernel t ht x‖ = (kernel t ht x).re := by
  have hh := kernel_real_nonneg ht x
  rw [← Complex.re_add_im (kernel t ht x), hh.1, Complex.ofReal_zero, zero_mul, add_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh.2, Complex.ofReal_re]

theorem kernel_integral {t : ℝ} (ht : 0 < t) :
    (∫ x : AddCircle (1:ℝ), kernel t ht x ∂haarAddCircle) = 1 := by
  have he := kernel_fourierCoeff ht 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, heatWeight, Int.cast_zero,
    mul_zero, zero_pow (by norm_num : 2 ≠ 0), Real.exp_zero, Complex.ofReal_one] using he

theorem kernel_norm_mass {t : ℝ} (ht : 0 < t) :
    (∫ x : AddCircle (1:ℝ), ‖kernel t ht x‖ ∂haarAddCircle) = 1 := by
  simp_rw [kernel_norm_eq_re ht]
  change (∫ x : AddCircle (1:ℝ), RCLike.re (kernel t ht x) ∂haarAddCircle) = 1
  have hi : Integrable (kernel t ht) haarAddCircle := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (kernel t ht).continuous.continuousOn.integrableOn_compact (K := univ) isCompact_univ
  rw [integral_re hi, kernel_integral ht]
  rfl

theorem kernelL2_eq {t : ℝ} (ht : 0 < t) :
    ContinuousMap.toLp 2 haarAddCircle ℂ (kernel t ht) = unitHeatKernel t 0 := by
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr]
  rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _), kernel_fourierCoeff ht,
    fourierCoeff_unitHeatKernel ht]
  simp only [fourier_eval_zero, one_mul]
  unfold heatWeight
  rw [max_eq_left ht.le]
  rw [show -t*(2*Real.pi*(n:ℝ))^2 = -(4*Real.pi^2*t)*(n:ℝ)^2 by ring]

theorem unitHeatKernel_ae {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    unitHeatKernel t x =ᵐ[haarAddCircle] (fun y => kernel t ht (y-x)) := by
  have hpres := (measurePreserving_sub_right haarAddCircle x).quasiMeasurePreserving
  have hK : unitHeatKernel t 0 =ᵐ[haarAddCircle] kernel t ht := by
    rw [← kernelL2_eq ht]
    exact ContinuousMap.coeFn_toLp _ _
  have ht' := translate_unitHeatKernel ht 0 x
  rw [zero_add] at ht'
  rw [← ht']
  filter_upwards [translate_ae x (unitHeatKernel t 0), hpres.ae hK] with y hy hk
  exact hy.trans hk

theorem push_unitHeatKernel (t : ℝ) (x : AddCircle (1:ℝ)) :
    CircleNormalization.push (unitHeatKernel t x) =
      StoppedFourier.circleHeat (4*Real.pi^2*t) (CircleNormalization.scale 1 (2*Real.pi) x) := by
  change CircleNormalization.pull (2*Real.pi) 1 (CircleNormalization.pull 1 (2*Real.pi) _) = _
  exact CircleNormalization.pull_inverse _ _ _

theorem kernel_inner_ae {t : ℝ} (ht : 0 < t) (f : CircleL2) :
    (fun x : AddCircle (1:ℝ) => inner ℂ (unitHeatKernel t x) f) =ᵐ[haarAddCircle]
      (heat t f : AddCircle (1:ℝ) → ℂ) := by
  let H : ℝ := 4*Real.pi^2*t
  have hH : 0 < H := by dsimp [H]; positivity
  have heH : H = (2*Real.pi)^2*t := by dsimp [H]; ring
  have hpres := (CircleNormalization.scale_measurePreserving 1 (2*Real.pi)).quasiMeasurePreserving
  have hae := hpres.ae (StoppedFourier.heat_kernel_inner_ae hH (CircleNormalization.push f))
  have hOp : CircleNormalization.pull 1 (2*Real.pi)
      (StoppedFourier.circleHeatOperator H hH.le (CircleNormalization.push f)) = heat t f := by
    have hp : CircleNormalization.push (heat t f) =
        StoppedFourier.circleHeatOperator H hH.le (CircleNormalization.push f) := by
      simpa only [← heH] using CircleNormalization.push_heat t ht.le f
    rw [← hp]
    change CircleNormalization.pull 1 (2*Real.pi) (CircleNormalization.pull (2*Real.pi) 1 _) = _
    exact CircleNormalization.pull_inverse _ _ _
  have hpull := CircleNormalization.pull_ae 1 (2*Real.pi)
    (StoppedFourier.circleHeatOperator H hH.le (CircleNormalization.push f))
  rw [hOp] at hpull
  filter_upwards [hae,hpull] with x hx hp
  rw [hp]
  rw [← CircleNormalization.push.inner_map_map, push_unitHeatKernel]
  exact hx

theorem kernel_inner_integral {t : ℝ} (ht : 0 < t) (f : CircleL2) (x : AddCircle (1:ℝ)) :
    inner ℂ (unitHeatKernel t x) f =
      ∫ y : AddCircle (1:ℝ), kernel t ht (y-x) * f y ∂haarAddCircle := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [unitHeatKernel_ae ht x] with y hy
  rw [hy, RCLike.inner_apply]
  have hc : (starRingEnd ℂ) (kernel t ht (y-x)) = kernel t ht (y-x) := by
    apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im, (kernel_real_nonneg ht (y-x)).1, neg_zero]
  rw [hc]
  ring

/-- The complete Fourier heat operator is literally convolution with the
continuous positive Gaussian periodization of mass one. -/
theorem heat_convolution_ae {t : ℝ} (ht : 0 < t) (f : CircleL2) :
    (heat t f : AddCircle (1:ℝ) → ℂ) =ᵐ[haarAddCircle]
      (fun x => ∫ y : AddCircle (1:ℝ), kernel t ht (y-x) * f y ∂haarAddCircle) := by
  filter_upwards [kernel_inner_ae ht f] with x hx
  exact hx.symm.trans (kernel_inner_integral ht f x)

def normOne (f : CircleL2) : ℝ := ∫ x : AddCircle (1:ℝ), ‖f x‖ ∂haarAddCircle

theorem normOne_nonneg (f : CircleL2) : 0 ≤ normOne f := integral_nonneg (fun _ => norm_nonneg _)

theorem kernel_norm_product_integrable {t : ℝ} (ht : 0 < t) (f : CircleL2) :
    Integrable (fun p : AddCircle (1:ℝ) × AddCircle (1:ℝ) =>
      ‖kernel t ht (p.2-p.1)‖ * ‖f p.2‖) (haarAddCircle.prod haarAddCircle) := by
  have hfi : Integrable (f : AddCircle (1:ℝ) → ℂ) haarAddCircle :=
    (Lp.memLp f).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hfn := hfi.norm.comp_snd (haarAddCircle (T := 1))
  apply (hfn.const_mul ‖kernel t ht‖).mono'
  · exact (((kernel t ht).continuous.comp (continuous_snd.sub continuous_fst)).norm.aestronglyMeasurable).mul
      hfn.aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right ((kernel t ht).norm_coe_le_norm _) (norm_nonneg _)

theorem kernel_norm_reverse_mass {t : ℝ} (ht : 0 < t) (y : AddCircle (1:ℝ)) :
    (∫ x : AddCircle (1:ℝ), ‖kernel t ht (y-x)‖ ∂haarAddCircle) = 1 := by
  exact (integral_sub_left_eq_self (fun z : AddCircle (1:ℝ) => ‖kernel t ht z‖)
    haarAddCircle y).trans (kernel_norm_mass ht)

/-- Contractivity in the true spatial `L¹` norm, derived from the actual
positive normalized kernel and Fubini rather than assumed as a semigroup
axiom. It applies to every complex circle `L²` field. -/
theorem heat_normOne_le {t : ℝ} (ht : 0 < t) (f : CircleL2) : normOne (heat t f) ≤ normOne f := by
  have hF := kernel_norm_product_integrable ht f
  have hheat : Integrable (heat t f : AddCircle (1:ℝ) → ℂ) haarAddCircle :=
    (Lp.memLp (heat t f)).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  unfold normOne
  calc
    _ ≤ ∫ x : AddCircle (1:ℝ), ∫ y : AddCircle (1:ℝ),
        ‖kernel t ht (y-x)‖ * ‖f y‖ ∂haarAddCircle ∂haarAddCircle := by
      apply integral_mono_ae hheat.norm hF.integral_prod_left
      filter_upwards [heat_convolution_ae ht f] with x hx
      rw [hx]
      simpa only [norm_mul] using norm_integral_le_integral_norm
        (fun y : AddCircle (1:ℝ) => kernel t ht (y-x) * f y)
    _ = ∫ y : AddCircle (1:ℝ), ∫ x : AddCircle (1:ℝ),
        ‖kernel t ht (y-x)‖ * ‖f y‖ ∂haarAddCircle ∂haarAddCircle := integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_mul_const, kernel_norm_reverse_mass ht y, one_mul]

theorem integral_norm_mul_norm_le (u v : CircleL2) :
    (∫ x : AddCircle (1:ℝ), ‖u x‖ * ‖v x‖ ∂haarAddCircle) ≤ ‖u‖ * ‖v‖ := by
  have hh := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num)
    (by simpa only [ENNReal.ofReal_ofNat] using Lp.memLp u)
    (by simpa only [ENNReal.ofReal_ofNat] using Lp.memLp v)
  simpa only [Real.rpow_two, ← StoppedFourier.L2_norm_sq_eq_integral, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg v)] using hh

theorem normOne_le_norm (f : CircleL2) : normOne f ≤ ‖f‖ := by
  have hh := integral_norm_mul_norm_le f FiniteHaar.circleOne
  rw [FiniteHaar.circleOne_norm, mul_one] at hh
  apply le_trans (le_of_eq ?_) hh
  unfold normOne
  apply integral_congr_ae
  filter_upwards [FiniteHaar.circleOne_ae] with x hx
  rw [hx, norm_one, mul_one]

theorem normOne_pos_of_ne_zero (f : CircleL2) (hf : f ≠ 0) : 0 < normOne f := by
  apply lt_of_le_of_ne (normOne_nonneg f)
  intro hz
  apply hf
  have hi : Integrable (f : AddCircle (1:ℝ) → ℂ) haarAddCircle :=
    (Lp.memLp f).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have he : ∀ᵐ x ∂haarAddCircle, ‖f x‖ = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun _ => norm_nonneg _)) hi.norm).mp hz.symm
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_zero ℂ 2 (haarAddCircle (T := 1))] with x hx h0
  exact (norm_eq_zero.mp hx).trans h0.symm

theorem fourierCoeff_norm_le_normOne (f : CircleL2) (n : ℤ) : ‖fourierCoeff f n‖ ≤ normOne f := by
  unfold fourierCoeff normOne
  calc
    _ ≤ ∫ x : AddCircle (1:ℝ), ‖fourier (-n) x • f x‖ ∂haarAddCircle := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]

theorem normOne_supported (p : List Bool) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∉ FiniteHaar.nodeCell p → v y = 0) :
    normOne v ≤ Real.sqrt (FiniteHaar.nodeLength p) * ‖v‖ := by
  have hh := integral_norm_mul_norm_le (FiniteHaar.nodeIndicator p) v
  have hn : ‖FiniteHaar.nodeIndicator p‖ = Real.sqrt (FiniteHaar.nodeLength p) := by
    rw [← FiniteHaar.nodeIndicator_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hh
  apply le_trans (le_of_eq ?_) hh
  unfold normOne
  apply integral_congr_ae
  filter_upwards [FiniteHaar.nodeIndicator_ae p,hv] with x hx hv
  rw [hx]
  by_cases hm : x ∈ FiniteHaar.nodeCell p
  · rw [Set.indicator_of_mem hm, norm_one, one_mul]
  · rw [Set.indicator_of_notMem hm, norm_zero, zero_mul, hv hm, norm_zero]

end SHE.HeatMarkov
