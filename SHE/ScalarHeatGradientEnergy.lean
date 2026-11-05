module

public import SHE.ScalarHeatGradientDifference
public import SHE.ClippedDisplacementSquare
public import SHE.PolynomialGaussianDecay

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
namespace SHE.ScalarHeatGradientEnergy
open Set MeasureTheory ProbabilityTheory Real ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

theorem decay_variance {r σ lo s : ℝ} (hr : 0<r) (hlo : 0<lo) (hs : 0≤s) (hσ : lo≤σ) :
    decay r σ s≤decay r lo s := by
  exact min_le_min_left 1 (rpow_le_rpow_of_nonpos (div_pos hlo (sq_pos_of_pos hr))
    (div_le_div_of_nonneg_right hσ (sq_nonneg r)) (neg_nonpos.mpr hs))

/-- The literal gradient-displacement multiplier has its clipped L²
state gain BEFORE any stochastic or spatial averaging. Future variance,
current means and every coefficient may be mutually dependent. -/
theorem gradient_energy {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ x y : X→ℝ)
    (hσm : Measurable σ) (hxm : Measurable x) (hym : Measurable y)
    (hσ : ∀ᵐ z∂ν,lo≤σ z) (hi : Integrable (fun z=>(y z-x z)^2) ν) (j : ℕ) :
    let g:=fun z=>deriv (heat (σ z).toNNReal (ScalarHeatBands.band a (j+1))) (y z)-
      deriv (heat (σ z).toNNReal (ScalarHeatBands.band a (j+1))) (x z)
    let r:=CompactMollifier.radius (j+1)
    let C:=(2*H*ScalarHeatGradientDifference.constant β)*r^(β-1)*decay r lo ((3-β)/2)
    Integrable (fun z=>|g z|^2) ν ∧
      (∫ z,|g z|^2 ∂ν)≤C^2*min 1 ((∫ z,(y z-x z)^2 ∂ν)/r^2) := by
  let g:=fun z=>deriv (heat (σ z).toNNReal (ScalarHeatBands.band a (j+1))) (y z)-
    deriv (heat (σ z).toNNReal (ScalarHeatBands.band a (j+1))) (x z)
  let r:=CompactMollifier.radius (j+1)
  let C:=(2*H*ScalarHeatGradientDifference.constant β)*r^(β-1)*decay r lo ((3-β)/2)
  have hr : 0<r:=CompactMollifier.radius_pos (j+1)
  have hclip:=ClippedDisplacementSquare.integral_clip ν (hym.sub hxm) hi hr
  have hgm : Measurable g:=
    (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ y hσm hym).sub
      (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ x hσm hxm)
  have hs : 0≤(3-β)/2:=by linarith
  have hcoef : 0≤(2*H*ScalarHeatGradientDifference.constant β)*r^(β-1):=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH) (ScalarHeatGradientDifference.constant_nonneg β))
      (rpow_nonneg hr.le _)
  have hC : 0≤C:=mul_nonneg hcoef (le_min zero_le_one (rpow_nonneg (div_nonneg hlo.le (sq_nonneg r)) _))
  have hpoint : ∀ᵐ z∂ν,|g z|^2≤C^2*(min 1 (|y z-x z|/r))^2 := by
    filter_upwards [hσ] with z hz
    have hz0 : 0<σ z:=hlo.trans_le hz
    have hh':=ScalarHeatGradientDifference.gradient_difference ha hH hβ hβ1 hh (σ z).toNNReal
      (Real.toNNReal_pos.mpr hz0) j (x z) (y z)
    rw [Real.coe_toNNReal _ hz0.le] at hh'
    have hdec:=decay_variance hr hlo hs hz
    have hclip0 : 0≤min 1 (|y z-x z|/r):=le_min zero_le_one (div_nonneg (abs_nonneg _) hr.le)
    have hbound : |g z|≤C*min 1 (|y z-x z|/r):=hh'.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdec hcoef) hclip0)
    simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hbound 2
  have hg : Integrable (fun z=>|g z|^2) ν:=by
    apply (hclip.1.const_mul (C^2)).mono'
      ((continuous_abs.measurable.comp hgm).pow_const 2).aestronglyMeasurable
    filter_upwards [hpoint] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _),Function.comp_def,Pi.sub_apply] using hz
  refine ⟨hg,?_⟩
  calc
    _≤∫ z,C^2*(min 1 (|y z-x z|/r))^2 ∂ν:=integral_mono_ae hg (hclip.1.const_mul (C^2)) hpoint
    _=C^2*∫ z,(min 1 (|y z-x z|/r))^2 ∂ν:=integral_const_mul _ _
    _≤_:=mul_le_mul_of_nonneg_left hclip.2 (sq_nonneg C)

end SHE.ScalarHeatGradientEnergy
