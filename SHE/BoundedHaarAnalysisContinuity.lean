module
public import SHE.HaarMeasurable
public import SHE.NativeRowTargetContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.BoundedHaarAnalysisContinuity
open Set MeasureTheory AddCircle CircleHeat FiniteHaar
open scoped NNReal ENNReal
local instance period : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance fieldSigma : MeasurableSpace CircleL2:=borel _
local instance fieldBorel : BorelSpace CircleL2:=⟨rfl⟩

theorem analysis_eq_inverse (m U:ℝ)(hm:0<m)(f:EllipticField m U)(v:CircleL2):
    factorAnalysis f.1 m U hm f.2.1 f.2.2 v=
      (fieldFactorEquivalence m U hm f).symm
        (CircleMultiplier.operator f.1 U (CircleMultiplier.elliptic_norm_bound f.1 m U hm f.2.1 f.2.2) v):=by
  apply (fieldFactorEquivalence m U hm f).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have he:=congrArg (fun A:CircleL2→L[ℂ] CircleL2=>A v)
    (factor_covariance f.1 m U hm f.2.1 f.2.2)
  change factor f.1 m U hm f.2.1 f.2.2 (factorAnalysis f.1 m U hm f.2.1 f.2.2 v)=_
  simpa only [ContinuousLinearMap.comp_apply,factor_adjoint] using he

theorem multiplier_commutes (f:CircleL2)(U:ℝ)(hf:∀ᵐy∂haarAddCircle,‖f y‖≤U)
    (v:CircleL2)(B:ℝ)(hv:∀ᵐy∂haarAddCircle,‖v y‖≤B):
    CircleMultiplier.operator f U hf v=CircleMultiplier.operator v B hv f:=by
  apply Lp.ext
  filter_upwards [CircleMultiplier.operator_ae f U hf v,CircleMultiplier.operator_ae v B hv f] with y h₁ h₂
  rw [h₁,h₂,mul_comm]

/-- The genuine infinite Haar analysis is strongly continuous in the
elliptic coefficient on every bounded physical test. This uses the
proved inverse factor and exact multiplication covariance. -/
theorem continuous_analysis (m U:ℝ)(hm:0<m)(v:CircleL2)(B:ℝ)
    (hv:∀ᵐy∂haarAddCircle,‖v y‖≤B):
    Continuous (fun f:EllipticField m U=>factorAnalysis f.1 m U hm f.2.1 f.2.2 v):=by
  have hm':Continuous (fun f:EllipticField m U=>
      CircleMultiplier.operator f.1 U (CircleMultiplier.elliptic_norm_bound f.1 m U hm f.2.1 f.2.2) v):=by
    have he:(fun f:EllipticField m U=>
        CircleMultiplier.operator f.1 U (CircleMultiplier.elliptic_norm_bound f.1 m U hm f.2.1 f.2.2) v)=
        fun f=>CircleMultiplier.operator v B hv f.1:=by
      funext f
      exact multiplier_commutes f.1 U _ v B hv
    rw [he]
    exact (CircleMultiplier.operator v B hv).continuous.comp continuous_subtype_val
  have hh:=(continuous_fieldInverse_joint m U hm).comp (continuous_id.prodMk hm')
  convert! hh using 1
  funext f
  exact analysis_eq_inverse m U hm f v

end SHE.BoundedHaarAnalysisContinuity
