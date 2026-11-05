module

public import SHE.SignedPrefix
public import SHE.DampedEnergy
public import SHE.ConvolutionEnergy
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.CircleHeat
open MeasureTheory AddCircle
open scoped ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The actual heat energy is continuous in its age, including age zero.
The proof uses the summable Fourier energy of the input as a uniform
dominator, rather than assuming a measurable energy profile. -/
theorem continuous_heat_energy (f : CircleL2) :
    Continuous (fun t : ℝ => ‖heat t f‖ ^ 2) := by
  have hc (n : ℤ) : Continuous (fun t : ℝ =>
      ‖heatWeight t n * fourierCoeff f n‖ ^ 2) := by
    unfold heatWeight
    fun_prop
  have hb (n : ℤ) (t : ℝ) :
      ‖‖heatWeight t n * fourierCoeff f n‖ ^ 2‖ ≤ ‖fourierCoeff f n‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have hw := heatWeight_norm_le t n
    have hw0 := norm_nonneg (heatWeight t n)
    have hs : ‖heatWeight t n‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖fourierCoeff f n‖]
  have hh := continuous_tsum hc (summable_fourier_sq f) hb
  convert hh using 1
  funext t
  rw [norm_sq_fourier]
  apply tsum_congr
  intro n
  rw [heat_fourierCoeff]

/-- Strong continuity of the literal circle heat semigroup for every L²
input. Fourier convergence is dominated by four times the true input
energy, so the statement includes the initial age. -/
theorem continuous_heat_apply (f : CircleL2) : Continuous (fun t : ℝ => heat t f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hc (n : ℤ) : Continuous (fun t : ℝ =>
      ‖(heatWeight t n-heatWeight s n) * fourierCoeff f n‖ ^ 2) := by
    unfold heatWeight
    fun_prop
  have hb (n : ℤ) (t : ℝ) :
      ‖‖(heatWeight t n-heatWeight s n) * fourierCoeff f n‖ ^ 2‖ ≤
        4 * ‖fourierCoeff f n‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have hw : ‖heatWeight t n-heatWeight s n‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [heatWeight_norm_le t n, heatWeight_norm_le s n])
    have hw0 := norm_nonneg (heatWeight t n-heatWeight s n)
    have hs : ‖heatWeight t n-heatWeight s n‖ ^ 2 ≤ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hseries := continuous_tsum hc ((summable_fourier_sq f).mul_left 4) hb
  have he : (fun t : ℝ => ‖heat t f-heat s f‖ ^ 2) =
      (fun t : ℝ => ∑' n : ℤ, ‖(heatWeight t n-heatWeight s n)*fourierCoeff f n‖ ^ 2) := by
    funext t
    rw [norm_sq_fourier]
    apply tsum_congr
    intro n
    rw [← fourierBasis_repr, map_sub]
    change ‖fourierBasis.repr (heat t f) n-fourierBasis.repr (heat s f) n‖ ^ 2 = _
    rw [fourierBasis_repr, fourierBasis_repr, heat_fourierCoeff, heat_fourierCoeff, sub_mul]
  have hn : Continuous (fun t : ℝ => ‖heat t f-heat s f‖ ^ 2) := by
    rw [he]
    exact hseries
  have hl : Filter.Tendsto (fun t : ℝ => ‖heat t f-heat s f‖) (nhds s) (nhds 0) := by
    have hh := (hn.tendsto s).sqrt
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), Real.sqrt_zero,
      Real.sqrt_sq (norm_nonneg _)] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hl

/-- The heat action is jointly continuous in age and physical L² input.
Uniform contraction controls a changing input while strong continuity
controls a changing age. -/
theorem continuous_heat_action :
    Continuous (fun p : ℝ × CircleL2 => heat p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hu : Continuous (fun p : ℝ × CircleL2 => dist p.2 p₀.2 +
      dist (heat p.1 p₀.2) (heat p₀.1 p₀.2)) :=
    (continuous_snd.dist continuous_const).add
      (((continuous_heat_apply p₀.2).comp continuous_fst).dist continuous_const)
  have hl : Filter.Tendsto (fun p : ℝ × CircleL2 => dist p.2 p₀.2 +
      dist (heat p.1 p₀.2) (heat p₀.1 p₀.2)) (nhds p₀) (nhds 0) := by
    simpa only [dist_self, zero_add] using hu.tendsto p₀
  apply squeeze_zero (fun p => dist_nonneg) _ hl
  intro p
  calc
    _ ≤ dist (heat p.1 p.2) (heat p.1 p₀.2) + dist (heat p.1 p₀.2) (heat p₀.1 p₀.2) :=
      dist_triangle _ _ _
    _ ≤ _ := by
      apply add_le_add_left
      simpa only [dist_eq_norm, ← map_sub] using heat_contraction p.1 (p.2-p₀.2)

end SHE.CircleHeat

namespace SHE.FiniteHaar
open MeasureTheory AddCircle CircleHeat
open scoped ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Squared Hilbert--Schmidt energy of the genuine finite signed factor. -/
def signedHeatEnergy (n : ℕ) (c d : Grid n → ℝ) (t : ℝ) : ℝ :=
  ‖heatedSignedColumns n c d t‖ ^ 2

theorem signedHeatEnergy_nonneg (n : ℕ) (c d : Grid n → ℝ) (t : ℝ) :
    0 ≤ signedHeatEnergy n c d t := sq_nonneg _

theorem continuous_signedHeatEnergy (n : ℕ) (c d : Grid n → ℝ) :
    Continuous (signedHeatEnergy n c d) := by
  have hh : Continuous (fun t : ℝ => ∑ j : Option (DetailIndex n),
      ‖heat t (signedColumn n c d j)‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => continuous_heat_energy _)
  convert hh using 1
  funext t
  exact heatedSignedColumns_norm_sq n c d t

/-- Increasing the outer heat age contracts every genuine factor column.
This gives the large-age tail directly from the semigroup. -/
theorem signedHeatEnergy_antitone (n : ℕ) (c d : Grid n → ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    signedHeatEnergy n c d t ≤ signedHeatEnergy n c d s := by
  unfold signedHeatEnergy
  rw [heatedSignedColumns_norm_sq, heatedSignedColumns_norm_sq]
  apply Finset.sum_le_sum
  intro j hj
  have he : heat t = (heat (t-s)).comp (heat s) := by
    rw [← heat_semigroup (sub_nonneg.mpr hst) hs, sub_add_cancel]
  rw [he, ContinuousLinearMap.comp_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (heat_contraction _ _) 2

/-- The full pointwise heat majorant, including the actual large-age tail. -/
theorem signedHeatEnergy_bound {t κ Λ ρ : ℝ} (ht : 0 < t)
    (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    signedHeatEnergy n c d t ≤
      signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (gridStep n (c-d)) *
        (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1)) := by
  have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
  have hC : 0 ≤ signedHeatSqConstant κ ρ m U :=
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
      (mul_nonneg (div_nonneg hU (sq_nonneg m)) (inverseConstant_nonneg hκ hρ hρhalf)))
      (sq_nonneg _)
  have hCF := mul_nonneg hC (negativeEnergy_nonneg κ ρ hΛ.le (gridStep n (c-d)))
  unfold signedHeatEnergy
  rw [heatedSignedColumns_norm_sq]
  by_cases ht1 : t ≤ 1
  · apply (signed_heat_finite_HS_sq ht ht1 hκ hΛ hρ hρhalf n c d m U hm hc hd).trans
    apply mul_le_mul_of_nonneg_left _ hCF
    exact le_add_of_nonneg_right (by positivity)
  · apply (signed_heat_finite_HS_tail (le_of_lt (lt_of_not_ge ht1))
      hκ hΛ hρ hρhalf n c d m U hm hc hd).trans
    apply mul_le_mul_of_nonneg_left _ hCF
    exact le_add_of_nonneg_left (by positivity)

/-- The actual finite-grid signed Haar energy is integrable over the whole
positive time axis with exponential damping. The negative-input constant
and damping power are uniform in the fine grid. No heat-energy estimate
or measurability condition is left as an analytic premise. -/
theorem damped_signedHeatEnergy {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    IntegrableOn (fun t => Real.exp (-2*Λ*t) * signedHeatEnergy n c d t) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0:ℝ), Real.exp (-2*Λ*t) * signedHeatEnergy n c d t) ≤
        (signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (gridStep n (c-d)) *
          signedDampingConstant ρ) * Λ ^ (ρ-1/2) := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
  have hC : 0 ≤ signedHeatSqConstant κ ρ m U :=
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
      (mul_nonneg (div_nonneg hU (sq_nonneg m)) (inverseConstant_nonneg hκ hρ hρhalf)))
      (sq_nonneg _)
  have hCF := mul_nonneg hC (negativeEnergy_nonneg κ ρ hΛp.le (gridStep n (c-d)))
  have hh := damped_signed_energy_of_heat_bound (F:=1) hΛ hρ.le hρhalf hCF
    (continuous_signedHeatEnergy n c d).aestronglyMeasurable
    (Filter.Eventually.of_forall (signedHeatEnergy_nonneg n c d)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [one_pow, mul_one] using
        signedHeatEnergy_bound ht hκ hΛp hρ hρhalf n c d m U hm hc hd)
  simpa only [one_pow, mul_one] using hh

end SHE.FiniteHaar

namespace SHE
open MeasureTheory Set
open scoped ENNReal

/-- The causal, damped majorant used for actual finite Haar columns. -/
def signedDampedKernel (Λ ρ : ℝ) : ℝ → ℝ≥0∞ :=
  (Ioi 0).indicator (fun t => ENNReal.ofReal (Real.exp (-2*Λ*t) *
    (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))))

theorem measurable_signedDampedKernel (Λ ρ : ℝ) : Measurable (signedDampedKernel Λ ρ) := by
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

/-- The causal majorant has the exact uniform massive damping power. -/
theorem signedDampedKernel_mass {Λ ρ : ℝ}
    (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1/2) :
    (∫⁻ t : ℝ, signedDampedKernel Λ ρ t) ≤
      ENNReal.ofReal (signedDampingConstant ρ * Λ ^ (ρ-1/2)) := by
  unfold signedDampedKernel
  rw [lintegral_indicator measurableSet_Ioi]
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hi := signed_heat_majorant_integrable hΛp hρ1
  have hp : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      0 ≤ Real.exp (-2*Λ*t) *
        (Λ ^ ρ * t ^ (-(1/2:ℝ)) + t ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hp]
  exact ENNReal.ofReal_le_ofReal (signed_heat_majorant_integral hΛ hρ0 hρ1)

end SHE

namespace SHE.FiniteHaar
open MeasureTheory AddCircle CircleHeat Set
open scoped ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The physical dyadic step synthesis is continuous on its actual finite
coefficient space. -/
theorem continuous_gridStep (n : ℕ) : Continuous (gridStep n) := by
  have hs := (StepInput.stepLinearMap (2 ^ n)).continuous_of_finiteDimensional
  exact hs.comp (continuous_pi (fun j => continuous_apply ((gridCellEquiv n).symm j)))

/-- A bounded physical step field has the same L² bound independently of
the number of dyadic cells. -/
theorem gridStep_sq_le (n : ℕ) (f : Grid n → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) : ‖gridStep n f‖ ^ 2 ≤ B ^ 2 := by
  rw [gridStep_norm_sq]
  have hp : (0:ℝ) < (2 ^ n : ℕ) := by positivity
  calc
    _ ≤ (((2 ^ n : ℕ):ℝ))⁻¹ * ∑ _x : Grid n, B ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp.le)
      apply Finset.sum_le_sum
      intro x hx
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hf x)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_grid]; field_simp

/-- Bounded elliptic coefficients have finite true negative input energy;
the estimate is independent of the grid resolution. -/
theorem bounded_negative_input {κ Λ ρ : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ)
    (n : ℕ) (c d : Grid n → ℝ) {m U : ℝ}
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    StepInput.negativeEnergy κ Λ ρ (gridStep n (c-d)) ≤ Λ ^ (-ρ) * (U-m) ^ 2 := by
  have hB : 0 ≤ U-m := by linarith [(hc (firstLeaf n)).1, (hc (firstLeaf n)).2]
  apply (negativeEnergy_le_L2 hΛ hρ _).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hΛ.le _)
  apply gridStep_sq_le n (c-d) hB
  intro x
  apply abs_le.mpr
  constructor <;> dsimp only [Pi.sub_apply] <;>
    linarith [(hc x).1, (hc x).2, (hd x).1, (hd x).2]

/-- Actual signed finite-grid columns on the true ordered time triangle.
After stochastic isometry, this is the deterministic estimate needed for
the damping-energy inequality. The coefficient fields need only be
measurable; no independence of coefficients is used. -/
theorem signed_finite_causal_energy {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (c d : ℝ → Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ s x, m ≤ c s x ∧ c s x ≤ U)
    (hd : ∀ s x, m ≤ d s x ∧ d s x ≤ U)
    (hmc : Measurable c) (hmd : Measurable d) (T : ℝ) :
    (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t,
      ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * signedHeatEnergy n (c s) (d s) (t-s))) ≤
      ENNReal.ofReal ((signedHeatSqConstant κ ρ m U * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) *
        ∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal
          (StepInput.negativeEnergy κ Λ ρ (gridStep n (c s-d s))) := by
  let C := signedHeatSqConstant κ ρ m U
  let F := fun s => ENNReal.ofReal (StepInput.negativeEnergy κ Λ ρ (gridStep n (c s-d s)))
  let K := fun t => ENNReal.ofReal C * signedDampedKernel Λ ρ t
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hF : Measurable F :=
    ENNReal.continuous_ofReal.measurable.comp
      (((continuous_negativeEnergy hΛp hρ.le).comp (continuous_gridStep n)).measurable.comp
        (hmc.sub hmd))
  have hU : 0 ≤ U := hm.le.trans ((hc 0 (firstLeaf n)).1.trans (hc 0 (firstLeaf n)).2)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
      (mul_nonneg (div_nonneg hU (sq_nonneg m)) (inverseConstant_nonneg hκ hρ hρhalf)))
      (sq_nonneg _)
  have hK : Measurable K := measurable_const.mul (measurable_signedDampedKernel Λ ρ)
  have hmass : (∫⁻ t : ℝ, K t) ≤
      ENNReal.ofReal ((C * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) := by
    dsimp only [K]
    rw [lintegral_const_mul _ (measurable_signedDampedKernel Λ ρ)]
    calc
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (signedDampingConstant ρ * Λ ^ (ρ-1/2)) :=
        mul_le_mul_right (signedDampedKernel_mass hΛ hρ.le hρhalf) _
      _ = _ := by rw [← ENNReal.ofReal_mul hC]; congr 1; ring
  have hpoint (t s : ℝ) (hs : s ∈ Ioo (0:ℝ) t) :
      ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * signedHeatEnergy n (c s) (d s) (t-s)) ≤
        K (t-s) * F s := by
    have hage : 0 < t-s := sub_pos.mpr hs.2
    have hh := signedHeatEnergy_bound hage hκ hΛp hρ hρhalf n (c s) (d s) m U hm (hc s) (hd s)
    have hmaj : 0 ≤ Real.exp (-2*Λ*(t-s)) *
        (Λ ^ ρ * (t-s) ^ (-(1/2:ℝ)) + (t-s) ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1)) := by positivity
    apply (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le)).trans_eq
    dsimp only [K, F, signedDampedKernel]
    rw [Set.indicator_of_mem (show t-s ∈ Ioi (0:ℝ) from hage)]
    rw [show Real.exp (-2*Λ*(t-s)) * (signedHeatSqConstant κ ρ m U *
      StepInput.negativeEnergy κ Λ ρ (gridStep n (c s-d s)) *
        (Λ ^ ρ * (t-s) ^ (-(1/2:ℝ)) + (t-s) ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) =
      C * (Real.exp (-2*Λ*(t-s)) *
        (Λ ^ ρ * (t-s) ^ (-(1/2:ℝ)) + (t-s) ^ (-(1/2:ℝ)-ρ) + (Λ ^ ρ+1))) *
          StepInput.negativeEnergy κ Λ ρ (gridStep n (c s-d s)) by dsimp only [C]; ring]
    rw [ENNReal.ofReal_mul (mul_nonneg hC hmaj), ENNReal.ofReal_mul hC]
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

/-- The same estimate holds after expectation for arbitrary dependent
random coefficient fields. The time kernel is deterministic, so no
independence assertion is needed. -/
theorem signed_finite_random_causal_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (c d : Ω → ℝ → Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ ω s x, m ≤ c ω s x ∧ c ω s x ≤ U)
    (hd : ∀ ω s x, m ≤ d ω s x ∧ d ω s x ≤ U)
    (hmc : ∀ ω, Measurable (c ω)) (hmd : ∀ ω, Measurable (d ω)) (T : ℝ) :
    (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t,
      ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * signedHeatEnergy n (c ω s) (d ω s) (t-s))) ∂μ) ≤
      ENNReal.ofReal ((signedHeatSqConstant κ ρ m U * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) *
        ∫⁻ ω, (∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal
          (StepInput.negativeEnergy κ Λ ρ (gridStep n (c ω s-d ω s)))) ∂μ := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((signedHeatSqConstant κ ρ m U * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) *
        (∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal
          (StepInput.negativeEnergy κ Λ ρ (gridStep n (c ω s-d ω s)))) ∂μ :=
      lintegral_mono (fun ω => signed_finite_causal_energy hκ hΛ hρ hρhalf n
        (c ω) (d ω) m U hm (hc ω) (hd ω) (hmc ω) (hmd ω) T)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- On a probability space, bounded coefficients give finite integrated
negative input energy automatically, with no mesh-dependent constant. -/
theorem bounded_random_input_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {κ Λ ρ : ℝ}
    (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (n : ℕ) (c d : Ω → ℝ → Grid n → ℝ) (m U T : ℝ)
    (hc : ∀ ω s x, m ≤ c ω s x ∧ c ω s x ≤ U)
    (hd : ∀ ω s x, m ≤ d ω s x ∧ d ω s x ≤ U) :
    (∫⁻ ω, (∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal
      (StepInput.negativeEnergy κ Λ ρ (gridStep n (c ω s-d ω s)))) ∂μ) ≤
        ENNReal.ofReal (Λ ^ (-ρ) * (U-m) ^ 2) * ENNReal.ofReal T := by
  calc
    _ ≤ ∫⁻ _ω : Ω, (∫⁻ _s in Ioc (0:ℝ) T, ENNReal.ofReal (Λ ^ (-ρ) * (U-m) ^ 2)) ∂μ := by
      apply lintegral_mono
      intro ω
      apply lintegral_mono
      intro s
      exact ENNReal.ofReal_le_ofReal (bounded_negative_input hΛ hρ n (c ω s) (d ω s) (hc ω s) (hd ω s))
    _ = _ := by simp [Real.volume_Ioc]

/-- The actual expected causal column energy is finite for bounded
measurable coefficients. Thus its damping estimate cannot hold merely
as a comparison between two infinite energies. -/
theorem signed_finite_random_causal_energy_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (c d : Ω → ℝ → Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ ω s x, m ≤ c ω s x ∧ c ω s x ≤ U)
    (hd : ∀ ω s x, m ≤ d ω s x ∧ d ω s x ≤ U)
    (hmc : ∀ ω, Measurable (c ω)) (hmd : ∀ ω, Measurable (d ω)) (T : ℝ) :
    (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t,
      ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * signedHeatEnergy n (c ω s) (d ω s) (t-s))) ∂μ) < ∞ := by
  have he := signed_finite_random_causal_energy μ hκ hΛ hρ hρhalf n c d m U hm hc hd hmc hmd T
  have hi := bounded_random_input_energy (κ:=κ) μ (zero_lt_one.trans_le hΛ) hρ.le n c d m U T hc hd
  apply he.trans_lt
  apply (mul_le_mul_right hi _).trans_lt
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- Precise finite-noise stochastic-isometry interface. The stochastic
isometry is an explicit standard input; the signed analytic energy
estimate on its actual column integrand is proved in this development. -/
theorem signed_finite_stochastic_energy_of_isometry {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (c d : Ω → ℝ → Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ ω s x, m ≤ c ω s x ∧ c ω s x ≤ U)
    (hd : ∀ ω s x, m ≤ d ω s x ∧ d ω s x ≤ U)
    (hmc : ∀ ω, Measurable (c ω)) (hmd : ∀ ω, Measurable (d ω)) (T : ℝ)
    (Z : Ω → ℝ → CircleL2)
    (hIsometry : (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal (‖Z ω t‖ ^ 2)) ∂μ) =
      ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t,
        ENNReal.ofReal (Real.exp (-2*Λ*(t-s)) * signedHeatEnergy n (c ω s) (d ω s) (t-s))) ∂μ) :
    (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal (‖Z ω t‖ ^ 2)) ∂μ) ≤
      ENNReal.ofReal ((signedHeatSqConstant κ ρ m U * signedDampingConstant ρ) * Λ ^ (ρ-1/2)) *
        ∫⁻ ω, (∫⁻ s in Ioc (0:ℝ) T, ENNReal.ofReal
          (StepInput.negativeEnergy κ Λ ρ (gridStep n (c ω s-d ω s)))) ∂μ := by
  rw [hIsometry]
  exact signed_finite_random_causal_energy μ hκ hΛ hρ hρhalf n c d m U hm hc hd hmc hmd T

end SHE.FiniteHaar
