module

public import SHE.ControlledProfileParameter

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The actual controlled profile derivative supplies both time rates
needed by positive score transfer: a coarse pointwise dominator and the
sharper spatial L² rate, with its zero extension beyond the horizon. -/
namespace SHE.ControlledScoreRates
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileVariance
  ProfileParameter ProfilePointwise ProfileStability ProfileL2 ControlledProfile
open scoped NNReal
local instance : Fact (0<2*π):=⟨by positivity⟩

def coarseConstant (P:CanonicalCovariance.ProfileParameters)(d:CircleL2):ℝ:=
  2*(meanConstant P.lower P.holder P.exponent*sqrt (1+heatConstant)*‖d‖)

def sharpConstant (P:CanonicalCovariance.ProfileParameters)(d:CircleL2):ℝ:=
  2*(meanConstant P.lower P.holder P.exponent*‖d‖)

theorem coarseConstant_nonneg (P:CanonicalCovariance.ProfileParameters)(d:CircleL2):0≤coarseConstant P d:=by
  unfold coarseConstant
  positivity [meanConstant_nonneg (β:=P.exponent) P.lower_pos.le P.holder_nonneg]

theorem sharpConstant_nonneg (P:CanonicalCovariance.ProfileParameters)(d:CircleL2):0≤sharpConstant P d:=by
  unfold sharpConstant
  positivity [meanConstant_nonneg (β:=P.exponent) P.lower_pos.le P.holder_nonneg]

theorem derivative_outside (P:CanonicalCovariance.ProfileParameters)(Λ:ℝ)(u d:CircleL2)
    (p:ProfileParameter.Domain)(hp:p.1∉Ioc 0 P.horizon)(θ:ℝ):
    ControlledProfile.derivative P Λ u d (p,θ)=0:=by
  unfold ControlledProfile.derivative
  have heq:(fun r=>profile P Λ u d (r,p))=fun _=>P.lower:=
    funext (fun r=>profile_outside P Λ u d r hp)
  rw[heq,deriv_const]

theorem derivative_coarse_power (P:CanonicalCovariance.ProfileParameters){Λ:ℝ}(hΛ:0≤Λ)(u d:CircleL2)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (θ:ℝ)(p:ProfileParameter.Domain)(hp:0≤p.1):
    |ControlledProfile.derivative P Λ u d (p,θ)|≤coarseConstant P d*p.1^((P.exponent-2)/4):=by
  have hh:=derivative_bound P hΛ u d hsmall p θ
  have hdom:curveBound P.lower P.holder P.exponent P.horizon d p≤
      coarseConstant P d*p.1^((P.exponent-2)/4):=by
    unfold curveBound
    split_ifs with ht
    · unfold pointwiseConstant coarseConstant
      exact le_of_eq (by ring)
    · exact mul_nonneg (coarseConstant_nonneg P d) (rpow_nonneg hp _)
  exact hh.trans hdom

/-- The literal derivative field has its sharp L² rate on the entire
nonnegative time line, rather than only inside the fixed-point horizon. -/
theorem ae_derivative_sharp_power (P:CanonicalCovariance.ProfileParameters){Λ:ℝ}(hΛ:0≤Λ)(u d:CircleL2)
    (hsmallPoint:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2):
    ∀ᵐθ ∂volume,∀ᵐr ∂volume.restrict (Ici (0:ℝ)),
      normTwo haarAddCircle (fun x=>ControlledProfile.derivative P Λ u d ((r,x),θ))≤
        sharpConstant P d*r^((P.exponent-1)/4):=by
  have hh:=ae_derivative_l2 P hΛ u d hsmallPoint hsmallL2
  filter_upwards[hh] with θ hθ
  rw[ae_restrict_iff' measurableSet_Ioc] at hθ
  filter_upwards[ae_restrict_of_ae hθ,ae_restrict_mem measurableSet_Ici] with r hr hr0
  by_cases hp:r∈Ioc 0 P.horizon
  · exact (hr hp).2
  · have hz:(fun x=>ControlledProfile.derivative P Λ u d ((r,x),θ))=fun _=>0:=
      funext (fun x=>derivative_outside P Λ u d (r,x) hp θ)
    rw[hz]
    simp only[normTwo,zero_pow (by decide:2≠0),integral_zero,sqrt_zero]
    exact mul_nonneg (sharpConstant_nonneg P d) (rpow_nonneg hr0 _)

end SHE.ControlledScoreRates
