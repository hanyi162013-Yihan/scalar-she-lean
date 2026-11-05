module
public import SHE.OrdinaryPhysicalGradient

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.OrdinaryGradientScaling
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  WordRecursion OrthogonalItoChannels CutoffWordLevel GaussianItoTest
open scoped NNReal ENNReal
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L Q:Level R Y n)

theorem raw_smul(w:ℝ)(p:Y)(hobs:L.observations.observations p=Q.observations.observations p)
    (htime:L.terminal p=Q.terminal p)(hF:L.test p=w • Q.test p)(z:ℝ≥0×Ω):
    OrdinaryPhysicalGradient.raw m L (p,z)=w • OrdinaryPhysicalGradient.raw m Q (p,z):=by
  have hb(t:ℝ):backward (L.window p) (L.test p) t=w • backward (Q.window p) (Q.test p) t:=by
    change GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (covariance R.reference (L.observations.observations p)
        (ClippedCovariance.clip R.base (L.terminal p) t) (L.terminal p))) (L.test p)=_
    rw [hobs,htime,hF,NormalizedInsertion.average_smul]
    rfl
  have hm:OrdinaryPhysicalGradient.mean m L (p,z)=OrdinaryPhysicalGradient.mean m Q (p,z):=by
    unfold OrdinaryPhysicalGradient.mean
    rw [hobs]
  rw [OrdinaryPhysicalGradient.raw,OrdinaryPhysicalGradient.raw,htime]
  by_cases hz:R.base<(z.1:ℝ)∧(z.1:ℝ)<Q.terminal p
  · rw [if_pos hz,if_pos hz,hb,fderiv_const_smul_field,hm,hobs,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ContinuousLinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,smul_smul]
  · rw [if_neg hz,if_neg hz,smul_zero]

end SHE.OrdinaryGradientScaling
