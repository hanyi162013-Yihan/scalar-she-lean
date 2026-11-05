module

public import SHE.HaarDifferentiability
public import SHE.HaarL2Heat
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE
open Finset Filter Topology

/-- A countable squared-energy estimate passes to actual derivatives
by finite sums of difference quotients. -/
theorem derivative_square_sum_bound {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → ι → E) (g : ι → E) (C : ℝ)
    (hd : ∀ i, HasDerivAt (fun s => F s i) (g i) 0)
    (hb : ∀ᶠ s in 𝓝[≠] (0 : ℝ), ∀ u : Finset ι,
      (∑ i ∈ u, ‖F s i - F 0 i‖ ^ 2) ≤ C * s ^ 2) :
    Summable (fun i => ‖g i‖ ^ 2) ∧ (∑' i, ‖g i‖ ^ 2) ≤ C := by
  classical
  have hfinite (u : Finset ι) : (∑ i ∈ u, ‖g i‖ ^ 2) ≤ C := by
    have ht : Tendsto (fun s : ℝ => ∑ i ∈ u, ‖s⁻¹ • (F s i - F 0 i)‖ ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (∑ i ∈ u, ‖g i‖ ^ 2)) := by
      apply tendsto_finsetSum
      intro i hi
      simpa only [zero_add] using ((hd i).tendsto_slope_zero.norm.pow 2)
    apply le_of_tendsto ht
    filter_upwards [hb, self_mem_nhdsWithin] with s hs hs0
    have hsne : s ≠ 0 := hs0
    simp only [norm_smul, Real.norm_eq_abs, mul_pow]
    rw [← Finset.mul_sum]
    calc
      _ ≤ |s⁻¹| ^ 2 * (C * s ^ 2) := mul_le_mul_of_nonneg_left (hs u) (sq_nonneg _)
      _ = C := by rw [sq_abs, inv_pow]; field_simp
  exact ⟨summable_of_sum_le (fun i => sq_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun i => sq_nonneg _) hfinite⟩

namespace FiniteHaar
open MeasureTheory AddCircle CircleHeat
local instance haarDerivativeHeat_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem affine_field_real (f h : CircleL2) (s : ℝ)
    (hf : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hh : ∀ᵐ y ∂haarAddCircle, (h y).im = 0) :
    ∀ᵐ y ∂haarAddCircle, ((f + s • h) y).im = 0 := by
  filter_upwards [Lp.coeFn_add f (s • h), Lp.coeFn_smul s h, hf, hh] with y ha hs hf hh
  rw [ha]
  change (f y + (s • h) y).im = 0
  rw [hs]
  change (f y + (s : ℂ) * h y).im = 0
  simp [Complex.add_im, Complex.mul_im, hf, hh]

theorem affine_field_bounds (f h : CircleL2) (m U M s : ℝ)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) (hs : |s| * M ≤ m / 2) :
    ∀ᵐ y ∂haarAddCircle, m / 2 ≤ ((f + s • h) y).re ∧ ((f + s • h) y).re ≤ U + m / 2 := by
  filter_upwards [Lp.coeFn_add f (s • h), Lp.coeFn_smul s h, hf, hh] with y ha hsm hf hh
  have hp : |s * (h y).re| ≤ m / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hh) (abs_nonneg s)).trans hs
  rw [abs_le] at hp
  rw [ha]
  change m / 2 ≤ (f y + (s • h) y).re ∧ (f y + (s • h) y).re ≤ U + m / 2
  rw [hsm]
  change m / 2 ≤ (f y + (s : ℂ) * h y).re ∧ (f y + (s : ℂ) * h y).re ≤ U + m / 2
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  constructor <;> linarith [hf.1, hf.2, hp.1, hp.2]

theorem affine_field_bounds_eventually (f h : CircleL2) (m U M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᵐ y ∂haarAddCircle,
      m / 2 ≤ ((f + s • h) y).re ∧ ((f + s • h) y).re ≤ U + m / 2 := by
  have hδ : 0 < m / (2 * (M + 1)) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs
  apply affine_field_bounds f h m U M s hf hh
  change dist s 0 < m / (2 * (M + 1)) at hs
  rw [dist_zero_right, Real.norm_eq_abs] at hs
  have hhM : |s| * M ≤ |s| * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
  have hsmall : |s| * (M + 1) < m / 2 := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2)).mpr
    have := (lt_div_iff₀ (by positivity : 0 < 2 * (M+1))).mp hs
    nlinarith
  exact hhM.trans hsmall.le

/-- The literal first derivative of the infinite physical Haar factor
has square-summable heated columns, with the integrable age `t^(-1/2)`.
The estimate follows from the actual same-Haar signed bound, not an
assumed derivative inequality. -/
theorem global_columnDerivative_heat_L2 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (f h : CircleL2) (m U M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hhreal : ∀ᵐ y ∂haarAddCircle, (h y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hhbound : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) :
    Summable (fun q : HaarNode => ‖heat t (columnDifferential q f h)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (columnDifferential q f h)‖ ^ 2) ≤
        signedL2HeatConstant (m / 2) (U + m / 2) * t ^ (-(1 / 2 : ℝ)) * ‖h‖ ^ 2 := by
  let C := signedL2HeatConstant (m / 2) (U + m / 2) * t ^ (-(1 / 2 : ℝ)) * ‖h‖ ^ 2
  apply derivative_square_sum_bound (fun s q => heat t (globalHaarColumn q (f + s • h)))
    (fun q => heat t (columnDifferential q f h)) C
  · intro q
    have hd := hasDerivAt_globalHaarColumn_line q f h
      (fun x => hm.trans_le (localAverage_bounds_ae (nodeDepth q) f m U hfbound x).1)
    exact ((heat t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  · have hfwide : ∀ᵐ y ∂haarAddCircle, m / 2 ≤ (f y).re ∧ (f y).re ≤ U + m / 2 :=
      hfbound.mono (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    filter_upwards [(affine_field_bounds_eventually f h m U M hm hM hfbound hhbound).filter_mono nhdsWithin_le_nhds] with s hs
    intro u
    have hb := global_signed_heat_L2 ht ht1 (f + s • h) f (m/2) (U+m/2) (by positivity)
      (affine_field_real f h s hfreal hhreal) hfreal hs hfwide
    have he : ‖f + s • h - f‖ ^ 2 = s ^ 2 * ‖h‖ ^ 2 := by
      rw [add_sub_cancel_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hh := (hb.1.sum_le_tsum u (fun q hq => sq_nonneg _)).trans hb.2
    simpa only [globalSignedColumn, map_sub, zero_smul, add_zero, he, C, mul_assoc, mul_left_comm, mul_comm] using hh

theorem weightedFourierSq_real_smul (w : ℤ → ℝ) (s : ℝ) (f : CircleL2) :
    weightedFourierSq w (s • f) = s ^ 2 * weightedFourierSq w f := by
  have hc (n : ℤ) : fourierCoeff (s • f) n = (s : ℂ) * fourierCoeff f n := by
    change fourierCoeff ((s : ℂ) • f) n = _
    rw [← fourierBasis_repr, map_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, fourierBasis_repr]
  unfold weightedFourierSq
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [hc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- Actual first derivatives inherit the genuine massive negative-input
signed heat estimate, with no derivative transport premise. -/
theorem global_columnDerivative_heat_negative {t κ Λ ρ : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hκ : 0 ≤ κ) (hΛ : 0 < Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (f h : CircleL2) (m U M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hhreal : ∀ᵐ y ∂haarAddCircle, (h y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hhbound : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) :
    Summable (fun q : HaarNode => ‖heat t (columnDifferential q f h)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (columnDifferential q f h)‖ ^ 2) ≤
        signedHeatSqConstant κ ρ (m / 2) (U + m / 2) * StepInput.negativeEnergy κ Λ ρ h *
          (Λ ^ ρ * t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ) - ρ)) := by
  let C := signedHeatSqConstant κ ρ (m / 2) (U + m / 2) * StepInput.negativeEnergy κ Λ ρ h *
    (Λ ^ ρ * t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ) - ρ))
  apply derivative_square_sum_bound (fun s q => heat t (globalHaarColumn q (f + s • h)))
    (fun q => heat t (columnDifferential q f h)) C
  · intro q
    have hd := hasDerivAt_globalHaarColumn_line q f h
      (fun x => hm.trans_le (localAverage_bounds_ae (nodeDepth q) f m U hfbound x).1)
    exact ((heat t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  · have hfwide : ∀ᵐ y ∂haarAddCircle, m / 2 ≤ (f y).re ∧ (f y).re ≤ U + m / 2 :=
      hfbound.mono (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    filter_upwards [(affine_field_bounds_eventually f h m U M hm hM hfbound hhbound).filter_mono nhdsWithin_le_nhds] with s hs
    intro u
    have hb := global_signed_heat ht ht1 hκ hΛ hρ hρhalf (f + s • h) f (m/2) (U+m/2) (by positivity)
      (affine_field_real f h s hfreal hhreal) hfreal hs hfwide
    have he : StepInput.negativeEnergy κ Λ ρ (f + s • h - f) = s ^ 2 * StepInput.negativeEnergy κ Λ ρ h := by
      rw [add_sub_cancel_left, StepInput.negativeEnergy, weightedFourierSq_real_smul]
      rfl
    have hh := (hb.1.sum_le_tsum u (fun q hq => sq_nonneg _)).trans hb.2
    simpa only [globalSignedColumn, map_sub, zero_smul, add_zero, he, C, mul_assoc, mul_left_comm, mul_comm] using hh

/-- Every genuine derivative detail still annihilates every coarser
dyadic step test. In particular its spatial integral vanishes. -/
theorem columnDifferential_coarse_zero (q : HaarNode) (f h : CircleL2)
    (m U M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hhreal : ∀ᵐ y ∂haarAddCircle, (h y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hhbound : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M)
    (k : ℕ) (b : Grid k → ℝ) (hq : k < nodeDepth q) :
    inner ℂ (gridStep k b) (columnDifferential q f h) = 0 := by
  have hd := ((innerSL ℂ (gridStep k b)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_globalHaarColumn_line q f h
      (fun x => hm.trans_le (localAverage_bounds_ae (nodeDepth q) f m U hfbound x).1))
  have he : (fun s : ℝ => inner ℂ (gridStep k b) (globalHaarColumn q (f + s • h))) =ᶠ[𝓝 0]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [affine_field_bounds_eventually f h m U M hm hM hfbound hhbound] with s hs
    exact globalHaarColumn_coarse_zero (f + s • h) (m / 2) (U + m / 2) (by positivity)
      (affine_field_real f h s hfreal hhreal) hs k b q hq
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq he)

end FiniteHaar
end SHE
