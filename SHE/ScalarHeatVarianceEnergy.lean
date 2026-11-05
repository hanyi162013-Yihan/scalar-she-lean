module

public import SHE.ScalarHeatVarianceDifference
public import SHE.PolynomialGaussianDecay

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
namespace SHE.ScalarHeatVarianceEnergy
open Set MeasureTheory ProbabilityTheory Real ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal
variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- Actual changed-variance Gaussian gradient energy, on an arbitrary
common measure space. Variance and mean may be fully dependent. -/
theorem energy {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    (σ0 σ1 m : X→ℝ) (h0m : Measurable σ0) (h1m : Measurable σ1) (hmm : Measurable m)
    (h0 : ∀ᵐ z∂ν,lo≤σ0 z) (h1 : ∀ᵐ z∂ν,lo≤σ1 z)
    (hi : Integrable (fun z=>(σ1 z-σ0 z)^2) ν) :
    let g:=fun z=>deriv (heat (σ1 z).toNNReal (ScalarHeatBands.band a (j+1))) (m z)-
      deriv (heat (σ0 z).toNNReal (ScalarHeatBands.band a (j+1))) (m z)
    let r:=CompactMollifier.radius (j+1)
    let C:=(1/2:ℝ)*H*constant β 2*r^(β-3)*decay r lo ((5-β)/2)
    Integrable (fun z=>|g z|^2) ν ∧
      (∫ z,|g z|^2 ∂ν)≤C^2*(∫ z,(σ1 z-σ0 z)^2 ∂ν) := by
  intro g r C
  have hgm : Measurable g:=
    (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ1 m h1m hmm).sub
      (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ0 m h0m hmm)
  have hpoint : ∀ᵐ z∂ν,|g z|^2≤C^2*(σ1 z-σ0 z)^2 := by
    filter_upwards [h0,h1] with z hz0 hz1
    have hd:=ScalarHeatVarianceDifference.gradient_difference ha hH hβ hβ1 hlo hh j (m z) hz0 hz1
    have hs:=pow_le_pow_left₀ (abs_nonneg _) hd 2
    simpa only [g,r,C,mul_pow,sq_abs] using hs
  have hg : Integrable (fun z=>|g z|^2) ν:=by
    apply (hi.const_mul (C^2)).mono' ((continuous_abs.measurable.comp hgm).pow_const 2).aestronglyMeasurable
    filter_upwards [hpoint] with z hz
    simpa only [Function.comp_def,Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨hg,?_⟩
  calc
    _≤∫ z,C^2*(σ1 z-σ0 z)^2 ∂ν:=integral_mono_ae hg (hi.const_mul (C^2)) hpoint
    _=_:=integral_const_mul _ _

end SHE.ScalarHeatVarianceEnergy
