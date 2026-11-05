module

public import SHE.StoppedHistory
public import SHE.HeatTrace
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section
set_option autoImplicit false

/-! Actual circle L² heat histories and their damping contraction. -/
noncomputable section
namespace SHE.StoppedFourier
open Set MeasureTheory AddCircle
open scoped ENNReal

abbrev HeatCircle := AddCircle (2 * Real.pi)
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev CircleL2 := Lp ℂ 2 (haarAddCircle (T := 2 * Real.pi))

def heatCoeff (t : ℝ) (x : HeatCircle) (n : ℤ) : ℂ :=
  fourier (-n) x * (Real.exp (-t * (n : ℝ) ^ 2) : ℂ)

 theorem heatCoeff_norm_sq (t : ℝ) (x : HeatCircle) (n : ℤ) :
    ‖heatCoeff t x n‖ ^ 2 = Real.exp (-(2 * t) * (n : ℝ) ^ 2) := by
  unfold heatCoeff
  have hphase : ‖fourier (-n) x‖ = 1 := Circle.norm_coe _
  rw [norm_mul, hphase, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), pow_two, ← Real.exp_add]
  congr 1
  ring

 theorem heatCoeff_memℓp {t : ℝ} (ht : 0 < t) (x : HeatCircle) : Memℓp (heatCoeff t x) 2 := by
  have hs := HeatTrace.multiplier_int_summable (Λ := 1) (ρ := 0) (t := 2 * t)
    (by norm_num) le_rfl (by linarith)
  simp only [HeatTrace.multiplier, neg_zero, Real.rpow_zero, one_mul] at hs
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, heatCoeff_norm_sq] using hs

/-- The actual torus heat kernel in L², built from the complete Fourier basis. -/
def circleHeat (t : ℝ) (x : HeatCircle) : CircleL2 :=
  if ht : 0 < t then fourierBasis.repr.symm ⟨heatCoeff t x, heatCoeff_memℓp ht x⟩ else 0

 theorem circleHeat_fourierCoeff {t : ℝ} (ht : 0 < t) (x : HeatCircle) (n : ℤ) :
    fourierCoeff (circleHeat t x) n = heatCoeff t x n := by
  rw [← fourierBasis_repr, circleHeat, dite_eq_left ht, LinearIsometryEquiv.apply_symm_apply]

/-- A finite physical-space family of stopped heat observations. -/
def historyF {ι : Type*} (I : Finset ι) (z : ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (u : ℝ) : CircleL2 :=
  ∑ i ∈ I, if u < σ i then z i • circleHeat (target i - u) (center i) else 0

/-- The same full family with the original stopping-age dampers. -/
def historyG {ι : Type*} (I : Finset ι) (z : ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (Λ u : ℝ) : CircleL2 :=
  ∑ i ∈ I, if u < σ i then (Real.exp (-Λ * (σ i - u)) : ℂ) •
    (z i • circleHeat (target i - u) (center i)) else 0

 theorem historyF_fourierCoeff {ι : Type*} (I : Finset ι) (z : ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i) (u : ℝ) (n : ℤ) :
    fourierCoeff (historyF I z σ target center u) n =
      ∑ i ∈ I, stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u • (z i * fourier (-n) (center i)) := by
  classical
  rw [← fourierBasis_repr]
  unfold historyF
  rw [map_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hu : u < σ i
  · rw [ite_eq_left hu, map_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [fourierBasis_repr, circleHeat_fourierCoeff (show 0 < target i - u by linarith [hages i hi])]
    simp only [heatCoeff, stoppedModeF, ite_eq_left hu, Complex.real_smul]
    ring
  · simp [hu, stoppedModeF]

 theorem historyG_fourierCoeff {ι : Type*} (I : Finset ι) (z : ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i) (Λ u : ℝ) (n : ℤ) :
    fourierCoeff (historyG I z σ target center Λ u) n =
      ∑ i ∈ I, (Real.exp (-Λ * (σ i - u)) * stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u) •
        (z i * fourier (-n) (center i)) := by
  classical
  rw [← fourierBasis_repr]
  unfold historyG
  rw [map_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hu : u < σ i
  · rw [ite_eq_left hu, map_smul, map_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [fourierBasis_repr, circleHeat_fourierCoeff (show 0 < target i - u by linarith [hages i hi])]
    simp only [heatCoeff, stoppedModeF, ite_eq_left hu, Complex.real_smul, Complex.ofReal_mul]
    ring
  · simp [hu, stoppedModeF]

theorem mode_family_square_integrable {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (κ q T : ℝ) :
    IntervalIntegrable (fun u => ‖∑ i ∈ I, stoppedModeF κ (σ i) (target i) u • z i‖ ^ 2) volume q T ∧
    IntervalIntegrable (fun u => ‖∑ i ∈ I,
      (Real.exp (-Λ * (σ i - u)) * stoppedModeF κ (σ i) (target i) u) • z i‖ ^ 2) volume q T := by
  have hfm : ∀ i ∈ I, AEStronglyMeasurable
      (fun u => stoppedModeF κ (σ i) (target i) u • z i) (volume.restrict (uIoc q T)) := by
    intro i hi
    exact (stoppedModeF_measurable κ (σ i) (target i)).aestronglyMeasurable.smul aestronglyMeasurable_const
  have hfi : ∀ i ∈ I, IntervalIntegrable
      (fun u => ‖stoppedModeF κ (σ i) (target i) u • z i‖ ^ 2) volume q T := by
    intro i hi
    have he := (stoppedModeF_square_integrable κ (σ i) (target i) q T).const_mul (‖z i‖ ^ 2)
    simpa only [norm_smul, mul_pow, mul_comm] using he
  have hgm : ∀ i ∈ I, AEStronglyMeasurable
      (fun u => (Real.exp (-Λ * (σ i - u)) * stoppedModeF κ (σ i) (target i) u) • z i)
        (volume.restrict (uIoc q T)) := by
    intro i hi
    have hde : Continuous (fun u : ℝ => Real.exp (-Λ * (σ i - u))) := by fun_prop
    exact (hde.measurable.mul (stoppedModeF_measurable κ (σ i) (target i))).aestronglyMeasurable.smul
      aestronglyMeasurable_const
  have hgi : ∀ i ∈ I, IntervalIntegrable
      (fun u => ‖(Real.exp (-Λ * (σ i - u)) * stoppedModeF κ (σ i) (target i) u) • z i‖ ^ 2) volume q T := by
    intro i hi
    apply (hfi i hi).mono_fun'
    · exact (hgm i hi).norm.pow 2
    · filter_upwards [] with u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hu : u < σ i
      · have hde : Real.exp (-Λ * (σ i - u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have hde0 := (Real.exp_pos (-Λ * (σ i - u))).le
        have hn : ‖(Real.exp (-Λ * (σ i - u)) * stoppedModeF κ (σ i) (target i) u) • z i‖ ≤
            ‖stoppedModeF κ (σ i) (target i) u • z i‖ := by
          rw [mul_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hde0]
          exact mul_le_of_le_one_left (norm_nonneg _) hde
        nlinarith [norm_nonneg ((Real.exp (-Λ * (σ i - u)) * stoppedModeF κ (σ i) (target i) u) • z i),
          norm_nonneg (stoppedModeF κ (σ i) (target i) u • z i)]
      · simp [stoppedModeF, hu]
  exact ⟨(finite_L2_sum I _ hfm hfi).2, (finite_L2_sum I _ hgm hgi).2⟩

theorem circle_parseval_ennreal (f : CircleL2) :
    ENNReal.ofReal (∫ x : HeatCircle, ‖f x‖ ^ 2 ∂haarAddCircle) =
      ∑' n : ℤ, ENNReal.ofReal (‖fourierCoeff f n‖ ^ 2) := by
  have hs := hasSum_sq_fourierCoeff f
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs.summable]

/-- Physical-space and time energy of the actual circle L² history. -/
def physicalEnergy (H : ℝ → CircleL2) (q T : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioc q T, ENNReal.ofReal (∫ x : HeatCircle, ‖(H u) x‖ ^ 2 ∂haarAddCircle)

/-- Full physical-space stopped-history damping contraction on the circle.
The fields are actual L² heat kernels, and the proof uses complete Parseval and Tonelli,
so no Fourier cutoff or assumed coefficient identification remains. -/
theorem physical_stopped_history_contraction {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) {Λ q T : ℝ}
    (hΛ : 0 < Λ) (hqT : q ≤ T) (hstops : ∀ i ∈ I, σ i ≤ T)
    (hages : ∀ i ∈ I, σ i ≤ target i) :
    physicalEnergy (historyG I z σ target center Λ) q T ≤
      physicalEnergy (historyF I z σ target center) q T := by
  let modes : ℤ → ι → ℂ := fun n i => z i * fourier (-n) (center i)
  have hFi : ∀ n : ℤ, IntervalIntegrable (fun u =>
      ‖∑ i ∈ I, stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u • modes n i‖ ^ 2) volume q T := by
    intro n
    exact (mode_family_square_integrable I (modes n) σ target hΛ.le ((n : ℝ) ^ 2) q T).1
  have hGi : ∀ n : ℤ, IntervalIntegrable (fun u => ‖∑ i ∈ I,
      (Real.exp (-Λ * (σ i - u)) * stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u) • modes n i‖ ^ 2) volume q T := by
    intro n
    exact (mode_family_square_integrable I (modes n) σ target hΛ.le ((n : ℝ) ^ 2) q T).2
  unfold physicalEnergy
  simp_rw [circle_parseval_ennreal, historyF_fourierCoeff I z σ target center hages,
    historyG_fourierCoeff I z σ target center hages]
  rw [lintegral_tsum (fun n => (hGi n).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal),
    lintegral_tsum (fun n => (hFi n).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  apply ENNReal.tsum_le_tsum
  intro n
  have he := finite_stopped_history_contraction I (modes n) σ target hΛ (sq_nonneg (n : ℝ)) hqT hstops
  rw [intervalIntegral.integral_of_le hqT, intervalIntegral.integral_of_le hqT] at he
  rw [← ofReal_integral_eq_lintegral_ofReal (hGi n).1 (ae_of_all _ (fun u => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal (hFi n).1 (ae_of_all _ (fun u => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal he

theorem circle_spatial_energy_eq_norm_sq (f : CircleL2) :
    (∫ x : HeatCircle, ‖f x‖ ^ 2 ∂haarAddCircle) = ‖f‖ ^ 2 := by
  have hs := lp.hasSum_norm (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (fourierBasis.repr f)
  have hs' : HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) (‖f‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, fourierBasis_repr, LinearIsometryEquiv.norm_map] using hs
  exact (hasSum_sq_fourierCoeff f).unique hs'

def heatConstant : ℝ := 2 * HeatTrace.fractionalGaussianIntegral 0

theorem heatConstant_pos : 0 < heatConstant := by
  exact mul_pos (by norm_num) (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ) < 1 / 2))

theorem circleHeat_norm_sq_bound {t : ℝ} (ht : 0 < t) (x : HeatCircle) :
    ‖circleHeat t x‖ ^ 2 ≤ 1 + heatConstant * t ^ (-(1 / 2 : ℝ)) := by
  have hs := hasSum_sq_fourierCoeff (circleHeat t x)
  rw [circle_spatial_energy_eq_norm_sq] at hs
  simp_rw [circleHeat_fourierCoeff ht, heatCoeff_norm_sq] at hs
  have hb := HeatTrace.centered_heat_trace_bound (Λ := 1) (ρ := 0) (t := 2 * t)
    (by norm_num) le_rfl (by norm_num) (by linarith)
  simp only [HeatTrace.multiplier, neg_zero, Real.rpow_zero, one_mul, zero_sub] at hb
  rw [hs.tsum_eq] at hb
  have hr : (2 * t) ^ (-(1 / 2 : ℝ)) ≤ t ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
  unfold heatConstant
  nlinarith [mul_le_mul_of_nonneg_left hr (mul_pos (by norm_num : (0 : ℝ) < 2)
    (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ) < 1 / 2))).le]

theorem norm_sq_finset_sum_le {ι E : Type*} [NormedAddCommGroup E]
    (I : Finset ι) (f : ι → E) :
    ‖∑ i ∈ I, f i‖ ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, ‖f i‖ ^ 2 := by
  have hn := norm_sum_le I f
  have hc := Finset.sum_mul_sq_le_sq_mul_sq I (fun _i => (1 : ℝ)) (fun i => ‖f i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hsum0 : 0 ≤ ∑ i ∈ I, ‖f i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  nlinarith [norm_nonneg (∑ i ∈ I, f i)]

theorem historyF_norm_sq_measurable {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i) :
    Measurable (fun u => ‖historyF I z σ target center u‖ ^ 2) := by
  have heq : (fun u => ‖historyF I z σ target center u‖ ^ 2) =
      fun u => ∑' n : ℤ, ‖∑ i ∈ I, stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u •
        (z i * fourier (-n) (center i))‖ ^ 2 := by
    funext u
    rw [← circle_spatial_energy_eq_norm_sq, ← tsum_sq_fourierCoeff]
    simp_rw [historyF_fourierCoeff I z σ target center hages]
  rw [heq]
  apply Measurable.tsum
  intro n
  apply Measurable.pow_const
  apply Measurable.norm
  apply Finset.measurable_fun_sum
  intro i hi
  exact (stoppedModeF_measurable _ _ _).smul measurable_const

/-- Actual undamped stopped circle histories have finite time-space energy,
including terminal target/stop collisions. -/
theorem historyF_norm_sq_intervalIntegrable {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    (q T : ℝ) : IntervalIntegrable (fun u => ‖historyF I z σ target center u‖ ^ 2) volume q T := by
  have hC : 0 ≤ heatConstant := heatConstant_pos.le
  have hprofile : ∀ i ∈ I, IntervalIntegrable (fun u : ℝ => ‖z i‖ ^ 2 *
      (1 + heatConstant * ‖(σ i - u) ^ (-(1 / 2 : ℝ))‖)) volume q T := by
    intro i hi
    have hp : IntervalIntegrable (fun u : ℝ => (σ i - u) ^ (-(1 / 2 : ℝ))) volume q T := by
      have he := (intervalIntegral.intervalIntegrable_rpow' (a := σ i - q) (b := σ i - T)
        (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).comp_sub_left (σ i)
      simpa only [sub_sub_cancel] using he
    exact ((intervalIntegrable_const.add (hp.norm.const_mul heatConstant)).const_mul (‖z i‖ ^ 2))
  apply ((IntervalIntegrable.sum I hprofile).const_mul (I.card : ℝ)).mono_fun'
  · exact (historyF_norm_sq_measurable I z σ target center hages).aestronglyMeasurable
  · filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold historyF
    apply (norm_sq_finset_sum_le I _).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simp only [Finset.sum_apply]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hu : u < σ i
    · rw [ite_eq_left hu, norm_smul, mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have ht : 0 < target i - u := by linarith [hages i hi]
      have hs : 0 < σ i - u := by linarith
      have hp : (target i - u) ^ (-(1 / 2 : ℝ)) ≤ (σ i - u) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hs (by linarith [hages i hi]) (by norm_num)
      have he := circleHeat_norm_sq_bound ht (center i)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hs.le _)]
      exact he.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp heatConstant_pos.le))
    · rw [ite_eq_right hu, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity

theorem physical_history_energy_finite {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    (q T : ℝ) : physicalEnergy (historyF I z σ target center) q T < ∞ := by
  unfold physicalEnergy
  simp_rw [circle_spatial_energy_eq_norm_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (historyF_norm_sq_intervalIntegrable I z σ target center hages q T).1
    (ae_of_all _ (fun u => sq_nonneg _))]
  exact ENNReal.ofReal_lt_top

theorem physical_damped_history_energy_finite {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) {Λ q T : ℝ}
    (hΛ : 0 < Λ) (hqT : q ≤ T) (hstops : ∀ i ∈ I, σ i ≤ T)
    (hages : ∀ i ∈ I, σ i ≤ target i) :
    physicalEnergy (historyG I z σ target center Λ) q T < ∞ :=
  (physical_stopped_history_contraction I z σ target center hΛ hqT hstops hages).trans_lt
    (physical_history_energy_finite I z σ target center hages q T)

def fullPhysicalEnergy (H : ℝ → CircleL2) (q : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ici q, ENNReal.ofReal (∫ x : HeatCircle, ‖(H u) x‖ ^ 2 ∂haarAddCircle)

theorem fullPhysicalEnergy_eq {H : ℝ → CircleL2} {q T : ℝ}
    (hzero : ∀ u, T ≤ u → H u = 0) :
    fullPhysicalEnergy H q = physicalEnergy H q T := by
  unfold fullPhysicalEnergy physicalEnergy
  rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [volume.ae_ne q] with u huq
  by_cases hqu : q ≤ u
  · by_cases huT : u ≤ T
    · have hlu : q < u := lt_of_le_of_ne hqu (Ne.symm huq)
      rw [indicator_of_mem (show u ∈ Ici q from hqu),
        indicator_of_mem (show u ∈ Ioc q T from ⟨hlu, huT⟩)]
    · have hZu : H u = 0 := hzero u (le_of_not_ge huT)
      rw [indicator_of_mem (show u ∈ Ici q from hqu),
        indicator_of_notMem (show u ∉ Ioc q T from fun hu => huT hu.2),
        circle_spatial_energy_eq_norm_sq, hZu]
      simp
  · have hnot : u ∉ Ioc q T := fun hu => hqu hu.1.le
    rw [indicator_of_notMem (show u ∉ Ici q from hqu), indicator_of_notMem hnot]

theorem historyF_zero_after {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) {T u : ℝ}
    (hstops : ∀ i ∈ I, σ i ≤ T) (hu : T ≤ u) : historyF I z σ target center u = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (not_lt_of_ge ((hstops i hi).trans hu))

theorem historyG_zero_after {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (Λ : ℝ) {T u : ℝ}
    (hstops : ∀ i ∈ I, σ i ≤ T) (hu : T ≤ u) : historyG I z σ target center Λ u = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (not_lt_of_ge ((hstops i hi).trans hu))

/-- The manuscript's full half-line stopped-history contraction on the torus,
with actual physical L² fields and finite energies on both sides. -/
theorem full_stopped_history_contraction {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) {Λ q : ℝ}
    (hΛ : 0 < Λ) (hages : ∀ i ∈ I, σ i ≤ target i) :
    fullPhysicalEnergy (historyG I z σ target center Λ) q ≤
      fullPhysicalEnergy (historyF I z σ target center) q ∧
      fullPhysicalEnergy (historyF I z σ target center) q < ∞ ∧
      fullPhysicalEnergy (historyG I z σ target center Λ) q < ∞ := by
  let T : ℝ := q + ∑ i ∈ I, |σ i - q|
  have hqT : q ≤ T := by
    dsimp [T]
    linarith [Finset.sum_nonneg (fun i (_hi : i ∈ I) => abs_nonneg (σ i - q))]
  have hstops : ∀ i ∈ I, σ i ≤ T := by
    intro i hi
    have hb : |σ i - q| ≤ ∑ j ∈ I, |σ j - q| :=
      Finset.single_le_sum (fun j (_hj : j ∈ I) => abs_nonneg (σ j - q)) hi
    dsimp [T]
    linarith [le_abs_self (σ i - q)]
  have hF : fullPhysicalEnergy (historyF I z σ target center) q =
      physicalEnergy (historyF I z σ target center) q T :=
    fullPhysicalEnergy_eq (fun u hu => historyF_zero_after I z σ target center hstops hu)
  have hG : fullPhysicalEnergy (historyG I z σ target center Λ) q =
      physicalEnergy (historyG I z σ target center Λ) q T :=
    fullPhysicalEnergy_eq (fun u hu => historyG_zero_after I z σ target center Λ hstops hu)
  rw [hF, hG]
  exact ⟨physical_stopped_history_contraction I z σ target center hΛ hqT hstops hages,
    physical_history_energy_finite I z σ target center hages q T,
    physical_damped_history_energy_finite I z σ target center hΛ hqT hstops hages⟩

theorem norm_sq_le_of_fourierCoeff {f g : CircleL2}
    (h : ∀ n : ℤ, ‖fourierCoeff f n‖ ^ 2 ≤ ‖fourierCoeff g n‖ ^ 2) : ‖f‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  have hsF := hasSum_sq_fourierCoeff f
  have hsG := hasSum_sq_fourierCoeff g
  have he := hsF.summable.tsum_le_tsum h hsG.summable
  rw [hsF.tsum_eq, hsG.tsum_eq, circle_spatial_energy_eq_norm_sq, circle_spatial_energy_eq_norm_sq] at he
  exact he

theorem mode_propagation {κ σ target q u : ℝ} (hqu : q ≤ u) (hu : u < σ) :
    stoppedModeF κ σ target q = Real.exp (-(u - q) * κ) * stoppedModeF κ σ target u := by
  simp only [stoppedModeF, ite_eq_left hu, ite_eq_left (hqu.trans_lt hu)]
  rw [← Real.exp_add]
  congr 1
  ring

theorem damped_mode_propagation {Λ κ σ target q u : ℝ} (hqu : q ≤ u) (hu : u < σ) :
    Real.exp (-Λ * (σ - q)) * stoppedModeF κ σ target q =
      Real.exp (-(u - q) * (Λ + κ)) *
        (Real.exp (-Λ * (σ - u)) * stoppedModeF κ σ target u) := by
  simp only [stoppedModeF, ite_eq_left hu, ite_eq_left (hqu.trans_lt hu)]
  simp only [← Real.exp_add]
  congr 1
  ring

theorem historyF_before_first_stop {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {q u : ℝ} (hqu : q ≤ u) (hactive : ∀ i ∈ I, u < σ i) :
    ‖historyF I z σ target center q‖ ^ 2 ≤ ‖historyF I z σ target center u‖ ^ 2 := by
  apply norm_sq_le_of_fourierCoeff
  intro n
  rw [historyF_fourierCoeff I z σ target center hages,
    historyF_fourierCoeff I z σ target center hages]
  have heq : (∑ i ∈ I, stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) q •
      (z i * fourier (-n) (center i))) = Real.exp (-(u - q) * (n : ℝ) ^ 2) •
      (∑ i ∈ I, stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u • (z i * fourier (-n) (center i))) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mode_propagation hqu (hactive i hi), mul_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hc : Real.exp (-(u - q) * (n : ℝ) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (n : ℝ)])
  have hn := norm_nonneg (∑ i ∈ I, stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u •
    (z i * fourier (-n) (center i)))
  have hmul := mul_le_of_le_one_left hn hc
  exact (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le hn) hn).mpr hmul

theorem historyG_before_first_stop {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {Λ q u : ℝ} (hΛ : 0 ≤ Λ) (hqu : q ≤ u) (hactive : ∀ i ∈ I, u < σ i) :
    ‖historyG I z σ target center Λ q‖ ^ 2 ≤ ‖historyG I z σ target center Λ u‖ ^ 2 := by
  apply norm_sq_le_of_fourierCoeff
  intro n
  rw [historyG_fourierCoeff I z σ target center hages,
    historyG_fourierCoeff I z σ target center hages]
  have heq : (∑ i ∈ I, (Real.exp (-Λ * (σ i - q)) *
      stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) q) • (z i * fourier (-n) (center i))) =
      Real.exp (-(u - q) * (Λ + (n : ℝ) ^ 2)) •
      (∑ i ∈ I, (Real.exp (-Λ * (σ i - u)) *
        stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u) • (z i * fourier (-n) (center i))) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [damped_mode_propagation hqu (hactive i hi), mul_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hc : Real.exp (-(u - q) * (Λ + (n : ℝ) ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (n : ℝ)])
  have hn := norm_nonneg (∑ i ∈ I, (Real.exp (-Λ * (σ i - u)) *
    stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u) • (z i * fourier (-n) (center i)))
  have hmul := mul_le_of_le_one_left hn hc
  exact (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le hn) hn).mpr hmul

theorem current_row_average {H : ℝ → CircleL2} {q δ : ℝ} (_hδ : 0 < δ)
    (hmon : ∀ u ∈ Ioc q (q + δ / 2), ‖H q‖ ^ 2 ≤ ‖H u‖ ^ 2) :
    ENNReal.ofReal ((δ / 2) * ‖H q‖ ^ 2) ≤ fullPhysicalEnergy H q := by
  have heq : (∫⁻ _u in Ioc q (q + δ / 2), ENNReal.ofReal (‖H q‖ ^ 2)) =
      ENNReal.ofReal ((δ / 2) * ‖H q‖ ^ 2) := by
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc,
      show q + δ / 2 - q = δ / 2 by ring, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [← heq]
  calc
    _ ≤ ∫⁻ u in Ioc q (q + δ / 2), ENNReal.ofReal (‖H u‖ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact ENNReal.ofReal_le_ofReal (hmon u hu)
    _ ≤ ∫⁻ u in Ici q, ENNReal.ofReal (‖H u‖ ^ 2) := lintegral_mono_set (fun u hu => hu.1.le)
    _ = fullPhysicalEnergy H q := by simp only [fullPhysicalEnergy, circle_spatial_energy_eq_norm_sq]

/-- The genuine undamped current-row Gram bound, with no conditioning-number assumption. -/
theorem stopped_current_row_bound {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {q δ : ℝ} (hδ : 0 < δ) (hstop : ∀ i ∈ I, q + δ ≤ σ i) :
    ‖historyF I z σ target center q‖ ^ 2 ≤ (2 / δ) *
      (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  have hfinite := (full_stopped_history_contraction I z σ target center
    (Λ := 1) (q := q) (by norm_num) hages).2.1
  have he := current_row_average (H := historyF I z σ target center) (q := q) hδ (by
    intro u hu
    apply historyF_before_first_stop I z σ target center hages hu.1.le
    intro i hi
    linarith [hstop i hi, hu.2])
  have hr := (ENNReal.ofReal_le_iff_le_toReal hfinite.ne).mp he
  calc
    _ ≤ (2 * (fullPhysicalEnergy (historyF I z σ target center) q).toReal) / δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith)
    _ = _ := by ring

/-- The damped current row is bounded by the original full-history Gram. -/
theorem stopped_damped_current_row_bound {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {Λ q δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ) (hstop : ∀ i ∈ I, q + δ ≤ σ i) :
    ‖historyG I z σ target center Λ q‖ ^ 2 ≤ (2 / δ) *
      (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  have hcontract := full_stopped_history_contraction I z σ target center (q := q) hΛ hages
  have he := current_row_average (H := historyG I z σ target center Λ) (q := q) hδ (by
    intro u hu
    apply historyG_before_first_stop I z σ target center hages hΛ.le hu.1.le
    intro i hi
    linarith [hstop i hi, hu.2])
  have hr := (ENNReal.ofReal_le_iff_le_toReal hcontract.2.1.ne).mp (he.trans hcontract.1)
  calc
    _ ≤ (2 * (fullPhysicalEnergy (historyF I z σ target center) q).toReal) / δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith)
    _ = _ := by ring

theorem history_current_difference_coeff {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    (Λ q : ℝ) (n : ℤ) :
    fourierCoeff (historyF I z σ target center q - historyG I z σ target center Λ q) n =
      ∑ i ∈ I, ((1 - Real.exp (-Λ * (σ i - q))) *
        stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) q) • (z i * fourier (-n) (center i)) := by
  rw [← fourierBasis_repr, map_sub]
  simp only [lp.coeFn_sub, Pi.sub_apply, fourierBasis_repr]
  rw [historyF_fourierCoeff I z σ target center hages,
    historyG_fourierCoeff I z σ target center hages, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sub_smul]
  congr 1
  ring

theorem historyF_energy_fourier_sum {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    (q T : ℝ) : physicalEnergy (historyF I z σ target center) q T =
      ∑' n : ℤ, ∫⁻ u in Ioc q T, ENNReal.ofReal
        (‖∑ i ∈ I, stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u • (z i * fourier (-n) (center i))‖ ^ 2) := by
  unfold physicalEnergy
  simp_rw [circle_parseval_ennreal, historyF_fourierCoeff I z σ target center hages]
  apply lintegral_tsum
  intro n
  exact (mode_family_square_integrable I (fun i => z i * fourier (-n) (center i)) σ target
    (Λ := 1) (by norm_num) ((n : ℝ) ^ 2) q T).1.1.aestronglyMeasurable.aemeasurable.ennreal_ofReal

/-- The physical current defect gains the square of the mass times the full stopping horizon. -/
theorem stopped_current_difference_small {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {Λ q T : ℝ} (hΛ : 0 < Λ) (hqT : q < T) (hstops : ∀ i ∈ I, σ i ≤ T) :
    ‖historyF I z σ target center q - historyG I z σ target center Λ q‖ ^ 2 ≤
      (Λ ^ 2 * (T - q)) * (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  let R : CircleL2 := historyF I z σ target center q - historyG I z σ target center Λ q
  let C : ℝ := Λ ^ 2 * (T - q)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE := physical_history_energy_finite I z σ target center hages q T
  have he : ENNReal.ofReal (‖R‖ ^ 2) ≤
      ENNReal.ofReal C * physicalEnergy (historyF I z σ target center) q T := by
    rw [← circle_spatial_energy_eq_norm_sq, circle_parseval_ennreal,
      historyF_energy_fourier_sum I z σ target center hages, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro n
    have hFi := (mode_family_square_integrable I (fun i => z i * fourier (-n) (center i))
      σ target hΛ.le ((n : ℝ) ^ 2) q T).1
    have hb := finite_stopped_resolvent_boundary I (fun i => z i * fourier (-n) (center i))
      σ target hΛ (sq_nonneg (n : ℝ)) hqT hstops
    rw [history_current_difference_coeff I z σ target center hages Λ q n]
    rw [intervalIntegral.integral_of_le hqT.le] at hb
    rw [← ofReal_integral_eq_lintegral_ofReal hFi.1 (ae_of_all _ (fun u => sq_nonneg _)),
      ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hb
  have hscaled : ENNReal.ofReal C * physicalEnergy (historyF I z σ target center) q T =
      ENNReal.ofReal (C * (physicalEnergy (historyF I z σ target center) q T).toReal) := by
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hE.ne]
  rw [hscaled] at he
  have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC ENNReal.toReal_nonneg)).mp he
  have hfull := fullPhysicalEnergy_eq (q := q) (fun u hu => historyF_zero_after I z σ target center hstops hu)
  rw [hfull]
  exact hr

/-- The large-mass current defect follows from the two genuine current-row bounds. -/
theorem stopped_current_difference_large {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {Λ q δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ) (hstop : ∀ i ∈ I, q + δ ≤ σ i) :
    ‖historyF I z σ target center q - historyG I z σ target center Λ q‖ ^ 2 ≤
      (8 / δ) * (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  have hF := stopped_current_row_bound I z σ target center hages hδ hstop
  have hG := stopped_damped_current_row_bound I z σ target center hages hΛ hδ hstop
  have hn := norm_sub_le (historyF I z σ target center q) (historyG I z σ target center Λ q)
  have hnF := norm_nonneg (historyF I z σ target center q)
  have hnG := norm_nonneg (historyG I z σ target center Λ q)
  have hnR := norm_nonneg (historyF I z σ target center q - historyG I z σ target center Λ q)
  have hR : ‖historyF I z σ target center q - historyG I z σ target center Λ q‖ ^ 2 ≤
      2 * ‖historyF I z σ target center q‖ ^ 2 + 2 * ‖historyG I z σ target center Λ q‖ ^ 2 := by
    nlinarith [sq_nonneg (‖historyF I z σ target center q‖ - ‖historyG I z σ target center Λ q‖)]
  calc
    _ ≤ 2 * ‖historyF I z σ target center q‖ ^ 2 + 2 * ‖historyG I z σ target center Λ q‖ ^ 2 := hR
    _ ≤ 2 * ((2 / δ) * (fullPhysicalEnergy (historyF I z σ target center) q).toReal) +
        2 * ((2 / δ) * (fullPhysicalEnergy (historyF I z σ target center) q).toReal) := by linarith
    _ = _ := by ring

/-- The full clipped current-difference Gram bound on comparable stopping ages.
Target ages retain their original values and need no upper comparability assumption. -/
theorem stopped_current_difference_clipped {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {Λ q w M : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hM : 1 ≤ M)
    (hlower : ∀ i ∈ I, q + w ≤ σ i) (hupper : ∀ i ∈ I, σ i ≤ q + M * w) :
    ‖historyF I z σ target center q - historyG I z σ target center Λ q‖ ^ 2 ≤
      max M 8 * min 1 (Λ * w) ^ 2 * w⁻¹ *
        (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  have hE : 0 ≤ (fullPhysicalEnergy (historyF I z σ target center) q).toReal := ENNReal.toReal_nonneg
  by_cases hsmall : Λ * w ≤ 1
  · have hqT : q < q + M * w := by nlinarith
    have hb := stopped_current_difference_small I z σ target center hages hΛ hqT hupper
    rw [show q + M * w - q = M * w by ring] at hb
    rw [min_eq_right hsmall]
    calc
      _ ≤ (Λ ^ 2 * (M * w)) * (fullPhysicalEnergy (historyF I z σ target center) q).toReal := hb
      _ = M * (Λ * w) ^ 2 * w⁻¹ * (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
        field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hw.le)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · have hb := stopped_current_difference_large I z σ target center hages hΛ hw hlower
    rw [min_eq_left (le_of_not_ge hsmall), one_pow, mul_one]
    calc
      _ ≤ (8 / w) * (fullPhysicalEnergy (historyF I z σ target center) q).toReal := hb
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hE
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.mpr hw.le)

theorem historyF_current_row {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) {q : ℝ} (hstop : ∀ i ∈ I, q < σ i) :
    historyF I z σ target center q = ∑ i ∈ I, z i • circleHeat (target i - q) (center i) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact ite_eq_left (hstop i hi)

theorem history_difference_current_row {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (Λ : ℝ) {q : ℝ} (hstop : ∀ i ∈ I, q < σ i) :
    historyF I z σ target center q - historyG I z σ target center Λ q =
      ∑ i ∈ I, ((1 - (Real.exp (-Λ * (σ i - q)) : ℂ)) * z i) •
        circleHeat (target i - q) (center i) := by
  unfold historyF historyG
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ite_eq_left (hstop i hi), ite_eq_left (hstop i hi), smul_smul, ← sub_smul]
  congr 1
  ring

theorem historyF_stronglyMeasurable {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i) :
    StronglyMeasurable (historyF I z σ target center) := by
  have hcoeff : ∀ n : ℤ, Measurable (fun u => fourierCoeff (historyF I z σ target center u) n) := by
    intro n
    simp_rw [historyF_fourierCoeff I z σ target center hages]
    exact Finset.measurable_fun_sum I (fun i _ => (stoppedModeF_measurable _ _ _).smul measurable_const)
  apply StronglyMeasurable.hasSum (L := SummationFilter.unconditional ℤ)
    (f := fun n u => fourierCoeff (historyF I z σ target center u) n • fourierBasis n)
  · intro n
    exact (hcoeff n).stronglyMeasurable.smul stronglyMeasurable_const
  · intro u
    simpa only [fourierBasis_repr] using fourierBasis.hasSum_repr (historyF I z σ target center u)

theorem historyF_memLp_time {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    (q : ℝ) : MemLp (historyF I z σ target center) 2 (volume.restrict (Ici q)) := by
  have hm : AEStronglyMeasurable (historyF I z σ target center) (volume.restrict (Ici q)) :=
    (historyF_stronglyMeasurable I z σ target center hages).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨hm.norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun u => sq_nonneg _))).mpr
  simpa only [fullPhysicalEnergy, circle_spatial_energy_eq_norm_sq] using
    (full_stopped_history_contraction I z σ target center (Λ := 1) (q := q) (by norm_num) hages).2.1

theorem historyF_memLp_interval {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    (q T : ℝ) : MemLp (historyF I z σ target center) 2 (volume.restrict (Ioc q T)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (historyF_stronglyMeasurable I z σ target center hages).aestronglyMeasurable).mpr
  exact (historyF_norm_sq_intervalIntegrable I z σ target center hages q T).1

theorem L2_norm_sq_eq_integral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {μ : Measure α} (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have he := congrArg (fun z : ℂ => RCLike.re z) (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re] at he
  · simpa only [← norm_sq_eq_re_inner] using he
  · exact L2.integrable_inner f f

theorem toLp_norm_sq_eq_integral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem toLp_inner_eq_integral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {μ : Measure α} {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℂ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem historyF_time_norm_sq {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i) (q : ℝ) :
    ‖(historyF_memLp_time I z σ target center hages q).toLp (historyF I z σ target center)‖ ^ 2 =
      (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  rw [toLp_norm_sq_eq_integral]
  have hi := (memLp_two_iff_integrable_sq_norm
    (historyF_memLp_time I z σ target center hages q).aestronglyMeasurable).mp
      (historyF_memLp_time I z σ target center hages q)
  unfold fullPhysicalEnergy
  simp_rw [circle_spatial_energy_eq_norm_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun u => sq_nonneg _)),
    ENNReal.toReal_ofReal (integral_nonneg (fun u => sq_nonneg _))]

theorem interval_history_energy_le_full {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {q a b : ℝ} (hqa : q ≤ a) (hab : a ≤ b) :
    (∫ u in a..b, ‖historyF I z σ target center u‖ ^ 2) ≤
      (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  have hi := historyF_norm_sq_intervalIntegrable I z σ target center hages a b
  have hfinite := (full_stopped_history_contraction I z σ target center
    (Λ := 1) (q := q) (by norm_num) hages).2.1
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite.ne).mp
  rw [intervalIntegral.integral_of_le hab,
    ofReal_integral_eq_lintegral_ofReal hi.1 (ae_of_all _ (fun u => sq_nonneg _))]
  unfold fullPhysicalEnergy
  simp_rw [circle_spatial_energy_eq_norm_sq]
  exact lintegral_mono_set (fun u hu => hqa.trans hu.1.le)

/-- Actual older stopped histories have the canonical small early-time energy fraction. -/
theorem older_history_prefix_bound {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {q a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (hstops : ∀ i ∈ I, q + a ≤ σ i) :
    (∫ u in q..q + b, ‖historyF I z σ target center u‖ ^ 2) ≤
      (b / (a - b)) * (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  let f : ℝ → ℝ := fun s => ‖historyF I z σ target center (q + s)‖ ^ 2
  have hi : IntervalIntegrable f volume 0 a := by
    have he := (historyF_norm_sq_intervalIntegrable I z σ target center hages q (q + a)).comp_add_left q
    simpa only [add_sub_cancel_left, sub_self] using he
  have hmono : MonotoneOn f (Ico 0 a) := by
    intro u hu v hv huv
    apply historyF_before_first_stop I z σ target center hages (by linarith)
    intro i hi
    linarith [hstops i hi, hv.2]
  have he := early_history_fraction_open hb hba hi hmono
  have hleft : (∫ s in (0 : ℝ)..b, f s) = ∫ u in q..q + b, ‖historyF I z σ target center u‖ ^ 2 := by
    rw [show f = (fun s => (fun u => ‖historyF I z σ target center u‖ ^ 2) (q + s)) by rfl,
      intervalIntegral.integral_comp_add_left]
    simp only [add_zero]
  have hright : (∫ s in b..a, f s) = ∫ u in q + b..q + a, ‖historyF I z σ target center u‖ ^ 2 := by
    exact intervalIntegral.integral_comp_add_left (fun u => ‖historyF I z σ target center u‖ ^ 2) q
  rw [hleft, hright] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    (interval_history_energy_le_full I z σ target center hages (by linarith) (by linarith))
    (div_nonneg hb (by linarith)))

theorem older_history_age_separation {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {q a b A : ℝ} (hb : 0 ≤ b) (hba : b < a) (hA : 1 < A) (hsep : A * b ≤ a)
    (hstops : ∀ i ∈ I, q + a ≤ σ i) :
    (∫ u in q..q + b, ‖historyF I z σ target center u‖ ^ 2) ≤
      (A - 1)⁻¹ * (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  have he := older_history_prefix_bound I z σ target center hages hb hba hstops
  have hfrac : b / (a - b) ≤ (A - 1)⁻¹ := by
    rw [← one_div]
    apply (div_le_div_iff₀ (by linarith : 0 < a - b) (by linarith : 0 < A - 1)).mpr
    nlinarith
  exact he.trans (mul_le_mul_of_nonneg_right hfrac ENNReal.toReal_nonneg)

theorem indicator_time_norm_sq {H : ℝ → CircleL2} {q b : ℝ} (hb : 0 ≤ b)
    (hm : MemLp H 2 (volume.restrict (Ici q))) :
    let hi := MemLp.indicator (s := Ioc q (q + b)) measurableSet_Ioc.nullMeasurableSet hm
    ‖hi.toLp ((Ioc q (q + b)).indicator H)‖ ^ 2 = ∫ u in q..q + b, ‖H u‖ ^ 2 := by
  dsimp only
  rw [toLp_norm_sq_eq_integral]
  have heq : (fun u => ‖(Ioc q (q + b)).indicator H u‖ ^ 2) =
      (Ioc q (q + b)).indicator (fun u => ‖H u‖ ^ 2) := by
    funext u
    by_cases hu : u ∈ Ioc q (q + b) <;> simp [hu]
  rw [heq, integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc q (q + b) ⊆ Ici q from fun u hu => hu.1.le),
    intervalIntegral.integral_of_le (show q ≤ q + b by linarith)]

def historyPairing (Y O : ℝ → CircleL2) (q : ℝ) : ℂ :=
  ∫ u in Ici q, inner ℂ (Y u) (O u)

/-- The canonical-correlation bound for two actual separated-age physical heat-history groups.
It is stated in squared form to avoid any division by a possibly zero group energy. -/
theorem separated_history_correlation_sq {ιY ιO : Type*}
    (IY : Finset ιY) (zY : ιY → ℂ) (σY targetY : ιY → ℝ) (centerY : ιY → HeatCircle)
    (IO : Finset ιO) (zO : ιO → ℂ) (σO targetO : ιO → ℝ) (centerO : ιO → HeatCircle)
    (hagesY : ∀ i ∈ IY, σY i ≤ targetY i) (hagesO : ∀ i ∈ IO, σO i ≤ targetO i)
    {q a b A : ℝ} (hb : 0 ≤ b) (hba : b < a) (hA : 1 < A) (hsep : A * b ≤ a)
    (hyoung : ∀ i ∈ IY, σY i ≤ q + b) (holder : ∀ i ∈ IO, q + a ≤ σO i) :
    ‖historyPairing (historyF IY zY σY targetY centerY) (historyF IO zO σO targetO centerO) q‖ ^ 2 ≤
      (A - 1)⁻¹ * (fullPhysicalEnergy (historyF IY zY σY targetY centerY) q).toReal *
        (fullPhysicalEnergy (historyF IO zO σO targetO centerO) q).toReal := by
  let Y := historyF IY zY σY targetY centerY
  let O := historyF IO zO σO targetO centerO
  have hY := historyF_memLp_time IY zY σY targetY centerY hagesY q
  have hO := historyF_memLp_time IO zO σO targetO centerO hagesO q
  let OE : ℝ → CircleL2 := (Ioc q (q + b)).indicator O
  have hOE : MemLp OE 2 (volume.restrict (Ici q)) :=
    MemLp.indicator measurableSet_Ioc.nullMeasurableSet hO
  have hpair : historyPairing Y O q = inner ℂ (hY.toLp Y) (hOE.toLp OE) := by
    rw [toLp_inner_eq_integral]
    unfold historyPairing
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici, ae_restrict_of_ae (volume.ae_ne q)] with u hu huq
    by_cases huE : u ∈ Ioc q (q + b)
    · simp only [OE, indicator_of_mem huE]
    · have hafter : q + b ≤ u := by
        have hstrict : q < u := lt_of_le_of_ne hu (Ne.symm huq)
        by_contra hlt
        exact huE ⟨hstrict, (lt_of_not_ge hlt).le⟩
      have hYu : Y u = 0 := historyF_zero_after IY zY σY targetY centerY hyoung hafter
      simp only [hYu, inner_zero_left]
  have hn := norm_inner_le_norm (𝕜 := ℂ) (hY.toLp Y) (hOE.toLp OE)
  have hnprod : 0 ≤ ‖hY.toLp Y‖ * ‖hOE.toLp OE‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg (inner ℂ (hY.toLp Y) (hOE.toLp OE))) hnprod).mpr hn
  rw [mul_pow] at hsq
  have hYnorm := historyF_time_norm_sq IY zY σY targetY centerY hagesY q
  have hOEnorm := indicator_time_norm_sq hb hO
  have hprefix := older_history_age_separation IO zO σO targetO centerO hagesO hb hba hA hsep holder
  rw [hYnorm, hOEnorm] at hsq
  rw [hpair]
  calc
    _ ≤ (fullPhysicalEnergy Y q).toReal * (∫ u in q..q + b, ‖O u‖ ^ 2) := hsq
    _ ≤ (fullPhysicalEnergy Y q).toReal *
        ((A - 1)⁻¹ * (fullPhysicalEnergy O q).toReal) :=
      mul_le_mul_of_nonneg_left hprefix ENNReal.toReal_nonneg
    _ = _ := by ring

end SHE.StoppedFourier
