module

public import SHE.ScalarCovarianceTailScale
public import SHE.ControlledProfile
public import SHE.ProfileL2
public import SHE.VariableObservations

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledScalarCovarianceTail
open Set MeasureTheory AddCircle StoppedFourier WordRecursion ProfileVariance ProfileL2
  ControlledProfile ProfileStability
open scoped NNReal
local instance tail_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance tail_circleSigma : MeasurableSpace CircleL2:=borel _
local instance tail_circleBorel : BorelSpace CircleL2:=⟨rfl⟩

/-- The genuine heat-square remaining-window map preserves a uniform
spatial L2 difference with the sharp square-root future-age gain. -/
theorem variance_difference {c d:ℝ×HeatCircle→ℝ} {r M D:ℝ}
    (hc:Measurable c) (hd:Measurable d) (hr:0<r) (hr1:r≤1)
    (hM:0≤M) (hD:0≤D)
    (hcB:∀s∈Ioo 0 r,∀x,|c (s,x)|≤M)
    (hdB:∀s∈Ioo 0 r,∀x,|d (s,x)|≤M)
    (hDiff:∀s∈Ioo 0 r,normTwo haarAddCircle (fun x=>c (s,x)-d (s,x))≤D):
    normTwo haarAddCircle (fun x=>varianceMap c r x-varianceMap d r x)≤
      ((1+heatConstant)*ProfileVolterra.powerConstant 0)*D*r^(1/2:ℝ):=by
  have h1:=varianceMap_normTwo_lipschitz hc hd hr hr1 hM hcB hdB
  have h2:=ProfileVolterra.singular_convolution_bound (a:=0) (by norm_num) hr hD
    (spatial_normTwo_measurable (hc.sub hd)) (fun s hs=>normTwo_nonneg _ _)
    (fun s hs=>by simpa only [Real.rpow_zero,mul_one,Pi.sub_apply] using hDiff s hs)
  have he:=h1.trans (mul_le_mul_of_nonneg_left h2.2
    (show 0≤1+heatConstant by linarith [heatConstant_pos]))
  convert he using 1 <;> simp only [zero_add] <;> ring

variable (P:CanonicalCovariance.ProfileParameters)

def constant:ℝ:=((1+heatConstant)*ProfileVolterra.powerConstant 0)*
  (2*meanConstant P.lower P.holder P.exponent)

theorem constant_nonneg:0≤constant P:=by
  unfold constant
  exact mul_nonneg
    (mul_nonneg (by linarith [heatConstant_pos])
      (ProfileVolterra.powerConstant_pos (by norm_num : (-1:ℝ)<0)).le)
    (mul_nonneg (by norm_num) (meanConstant_nonneg P.lower_pos.le P.holder_nonneg))

/-- Literal controlled canonical remaining covariance for a scalar
observation at the terminal time. The profile retains its original
initial-age clock based at v, while covariance starts at q. -/
def tail (Λ v q b θ:ℝ) (u d:CircleL2) (x:HeatCircle):ℝ:=
  covariance (fun p=>ControlledProfile.profile P Λ u d (θ,(p.1-v,p.2)))
    (ScalarCovarianceTailScale.observation b x) q b 0 0

/-- ACTUAL remaining covariance changes retain BOTH clocks: sqrt(b-q)
from the future integration and (q-v)^((beta-1)/4) from the original
canonical-profile stability. No future-only stability is substituted. -/
theorem tail_difference {Λ v q b:ℝ} (hΛ:0≤Λ) (hvq:v<q) (hqb:q<b)
    (hspan:b-v≤P.horizon)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (u d:CircleL2) (θ η:ℝ):
    normTwo haarAddCircle (fun x=>tail P Λ v q b θ u d x-tail P Λ v q b η u d x)≤
      constant P*|θ-η| * ‖d‖*(q-v)^((P.exponent-1)/4)*(b-q)^(1/2:ℝ):=by
  let c:ℝ×HeatCircle→ℝ:=fun p=>ControlledProfile.profile P Λ u d (θ,(p.1+q-v,p.2))
  let e:ℝ×HeatCircle→ℝ:=fun p=>ControlledProfile.profile P Λ u d (η,(p.1+q-v,p.2))
  have hm:Measurable (fun p:ℝ×HeatCircle=>(p.1+q-v,p.2)):=
    ((measurable_fst.add_const q).sub_const v).prodMk measurable_snd
  have hc:Measurable c:=(ControlledProfile.profile_measurable P Λ u d).comp
    (measurable_const.prodMk hm)
  have he:Measurable e:=(ControlledProfile.profile_measurable P Λ u d).comp
    (measurable_const.prodMk hm)
  have hb (ξ:ℝ) (p:ℝ×HeatCircle):
      |ControlledProfile.profile P Λ u d (ξ,(p.1+q-v,p.2))|≤P.upper:=by
    rw [abs_of_nonneg (P.lower_pos.le.trans (ControlledProfile.profile_bounds P Λ u d _).1)]
    exact (ControlledProfile.profile_bounds P Λ u d _).2
  let D:=2*(meanConstant P.lower P.holder P.exponent*(|θ-η| * ‖d‖))*
    (q-v)^((P.exponent-1)/4)
  have hD:0≤D:=by
    dsimp only [D]
    positivity [meanConstant_nonneg (β:=P.exponent) P.lower_pos.le P.holder_nonneg]
  have hdiff:∀s∈Ioo 0 (b-q),normTwo haarAddCircle (fun x=>c (s,x)-e (s,x))≤D:=by
    intro s hs
    have hr:s+q-v∈Ioc 0 P.horizon:=⟨by linarith [hs.1],by linarith [hs.2]⟩
    have ht:=ControlledProfile.profile_l2_stability P hΛ u d θ η hsmall hr
    have hp:(s+q-v)^((P.exponent-1)/4)≤(q-v)^((P.exponent-1)/4):=
      Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hvq) (by linarith [hs.1])
        (by linarith [P.exponent_le_one])
    exact ht.trans (mul_le_mul_of_nonneg_left hp
      (by positivity [meanConstant_nonneg (β:=P.exponent) P.lower_pos.le P.holder_nonneg]))
  have ht:=variance_difference hc he (sub_pos.mpr hqb)
    (by linarith [P.horizon_le_one]) P.upper_nonneg hD
    (fun s hs x=>hb θ (s,x)) (fun s hs x=>hb η (s,x)) hdiff
  have heq (ξ:ℝ):tail P Λ v q b ξ u d=
      varianceMap (fun p=>ControlledProfile.profile P Λ u d (ξ,(p.1+q-v,p.2))) (b-q):=by
    funext x
    exact ScalarCovarianceTailScale.diagonal_eq _ hqb.le x
  rw [heq θ,heq η]
  convert ht using 1 <;> dsimp only [D,constant] <;> ring

end SHE.ControlledScalarCovarianceTail
