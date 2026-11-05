module

public import SHE.HaarUnitary
public import SHE.CircleNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar
open MeasureTheory AddCircle CircleHeat
local instance observationFactor_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance observationFactor_nativePeriodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The bracket of the actual common-Haar observation rows equals the
true multiplication covariance for arbitrary physical `L²` tests. -/
theorem factorAnalysis_cross_inner (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (u v : CircleL2) :
    inner ℂ (factorAnalysis f m U hm hfreal hfbound u) (factorAnalysis f m U hm hfreal hfbound v) =
      inner ℂ u (CircleMultiplier.operator f U
        (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound) v) := by
  rw [← factor_adjoint f m U hm hfreal hfbound,
    ContinuousLinearMap.adjoint_inner_left]
  exact congrArg (fun A : CircleL2 →L[ℂ] CircleL2 => inner ℂ u (A v))
    (factor_covariance f m U hm hfreal hfbound)

theorem factorAnalysis_cross_integral (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (u v : CircleL2) :
    inner ℂ (factorAnalysis f m U hm hfreal hfbound u) (factorAnalysis f m U hm hfreal hfbound v) =
      ∫ y : AddCircle (1 : ℝ), starRingEnd ℂ (u y) * (f y * v y) ∂haarAddCircle := by
  rw [factorAnalysis_cross_inner, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [CircleMultiplier.operator_ae f U
    (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound) v] with y hy
  rw [hy]
  rw [RCLike.inner_apply]
  ring

theorem factorAnalysis_real_cross_integral (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (u v : CircleL2)
    (hu : ∀ᵐ y ∂haarAddCircle, (u y).im = 0) (hv : ∀ᵐ y ∂haarAddCircle, (v y).im = 0) :
    (inner ℂ (factorAnalysis f m U hm hfreal hfbound u) (factorAnalysis f m U hm hfreal hfbound v)).re =
      ∫ y : AddCircle (1 : ℝ), (f y).re * (u y).re * (v y).re ∂haarAddCircle := by
  rw [factorAnalysis_cross_inner, L2.inner_def]
  change RCLike.re (∫ y : AddCircle (1 : ℝ), inner ℂ (u y)
    (CircleMultiplier.operator f U (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound) v y) ∂haarAddCircle) = _
  rw [← integral_re (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [CircleMultiplier.operator_ae f U
    (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound) v, hfreal, hu, hv] with y hy hf hu hv
  rw [hy, RCLike.inner_apply]
  change ((f y * v y) * starRingEnd ℂ (u y)).re = _
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, hf, hu, hv,
    zero_mul, mul_zero, sub_zero]
  ring

def nativeFactorAnalysis (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    StoppedFourier.CircleL2 →L[ℂ] HaarInput :=
  (factorAnalysis f m U hm hfreal hfbound).comp
    CircleNormalization.push.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The same genuine Haar rows give the literal period-`2π` bracket,
with the coefficient pushed by the exact normalized-Haar isometry. -/
theorem nativeFactorAnalysis_cross_integral (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (u v : StoppedFourier.CircleL2) :
    inner ℂ (nativeFactorAnalysis f m U hm hfreal hfbound u)
        (nativeFactorAnalysis f m U hm hfreal hfbound v) =
      ∫ y : AddCircle (2 * Real.pi), starRingEnd ℂ (u y) * (CircleNormalization.push f y * v y) ∂haarAddCircle := by
  change inner ℂ (factorAnalysis f m U hm hfreal hfbound (CircleNormalization.push.symm u))
      (factorAnalysis f m U hm hfreal hfbound (CircleNormalization.push.symm v)) = _
  rw [factorAnalysis_cross_integral]
  rw [← (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1).integral_comp
    (CircleNormalization.scaleMeasurableEquiv (2 * Real.pi) 1).measurableEmbedding
    (fun x : AddCircle (1 : ℝ) => starRingEnd ℂ (CircleNormalization.push.symm u x) *
      (f x * CircleNormalization.push.symm v x))]
  have hu := CircleNormalization.push_ae (CircleNormalization.push.symm u)
  have hv := CircleNormalization.push_ae (CircleNormalization.push.symm v)
  rw [LinearIsometryEquiv.apply_symm_apply] at hu hv
  apply integral_congr_ae
  filter_upwards [hu, hv, CircleNormalization.push_ae f] with y hu hv hf
  rw [hu, hv, hf]

end SHE.FiniteHaar
