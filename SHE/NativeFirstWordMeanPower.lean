module

public import SHE.NativeFirstWordMeanTree
public import SHE.FirstWordPowers

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Literal fixed-gap n=1 physical Gaussian word mean derivative with its final root and
new-input powers. This is the instantaneous mean/baseline leg; covariance-profile marking
and parameter integration of the full profile path remain separate. -/
namespace SHE.NativeFirstWordMeanPower
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore HeatHistoryScore HeatTorus HeatTorusKernel GaussianGramScore GaussianIncrement
  MeasurableGaussianScores NativeMeanFields NativeMeanScoreKernel MeasurableGeneralizedInverse
  GaussianWordFields NativeGaussianFirstWord GaussianAudit NativeOldRoot NativeFirstWordMeanTree GaussianWordMeanDerivative
  ProfileVariance OldFractionHeatScale FirstWordPowers ProfileL2
open scoped InnerProductSpace NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable [MeasurableSpace HeatTorus.CircleL2] [BorelSpace HeatTorus.CircleL2]

def meanDerivativeField (target:Fin 2 → ℝ)(Λ:ℝ)(t:Fin 2 → ℝ)
    (hage:∀i,target i=4*π^2*t i)(act:∀i,0<target i)
    (c:(UnitAddCircle×UnitAddCircle)×Domain → ℝ)(d:HeatTorus.CircleL2)
    (m:UnitAddCircle×UnitAddCircle → State 2)(v:ℝ≥0)(f b:ℝ → ℝ)(p:UnitAddCircle×UnitAddCircle):ℝ:=
  let A:=covarianceField target relativeCenters c 0
  let D:=directionField target relativeCenters 0 Λ t (fun i=>by simpa using hage i) act (fun _=>d)
  firstMeanScore (A p) (D p) v f b (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) (m p)

/-- Actual fixed-gap physical n=1 word estimate. Every scalar/time exponent
on the right is derived from the actual Gaussian moments and heat masses. -/
theorem native_firstWord_mean_derivative_power:
    ∃h C:ℝ,0<h ∧ h≤1 ∧ 0<C ∧
      ∀(target:Fin 2 → ℝ)(ht1:∀i,target i≤1)(Λ:ℝ),0<Λ → 
      ∀(t:Fin 2 → ℝ)(ht:∀i,0<t i),(∀i,t i≤h) → 
      ∀(hage:∀i,target i=4*π^2*t i)(s:ℝ)(hs:0<s)(hmin:∀i,s≤target i)(hleaf:target 1=s)
      (c:(UnitAddCircle×UnitAddCircle)×Domain → ℝ)(hc:Measurable c)(U ell:ℝ)
      (hcb:∀p r,0≤c (p,r) ∧ c (p,r)≤U),0<ell → (∀p r,ell≤c (p,r)) → 
      ∀(d:HeatTorus.CircleL2)(m:UnitAddCircle×UnitAddCircle → State 2),Measurable m → 
      ∀(r ellOld:ℝ)(hr:0<r)(hr1:r≤1)(hellOld:0<ellOld), 
      ∀(f f' b:ℝ → ℝ)(A0 ν M H β:ℝ),
      0≤A0 → 0≤ν → (∀z,HasDerivAt f (f' z) z) → (∀z,|f z|≤A0) → (∀z,|f' z|≤A0*ν) → 
      Measurable b → (∀z,|b z|≤M) → 0≤H → 0≤β → (∀z w,|b z-b w|≤H*|z-w|^β) → 
      let act:∀i,0<target i:=fun i=>hs.trans_le (hmin i)
      let F:=meanDerivativeField target Λ t hage act c d m (oldVariance ellOld r) f b
      normTwo haarAddCircle (fun x=>∫y,‖HeatMarkov.kernel (r/(4*π^2)) (by positivity) y‖^2*F (y,x) ∂haarAddCircle)≤
        4*A0*rootScaleConstant ellOld*roughConstant U H β*sqrt (C/ell)*
          SHE.rootKernel ν r*s^((β-1)/4)*‖d‖:=by
  obtain ⟨h,C,hh,hh1,hC,he⟩:=native_firstWord_heat_mean_derivative_energy
  refine ⟨h,C,hh,hh1,hC,?_⟩
  intro target ht1 Λ hΛ t ht hth hage s hs hmin hleaf c hc U ell hcb hell hcl d m hm
    r ellOld hr hr1 hellOld f f' b A0 ν M H β hA0 hν hf hfb hfD hb hbB hH hβ hholder
  let act:∀i,0<target i:=fun i=>hs.trans_le (hmin i)
  let F:=meanDerivativeField target Λ t hage act c d m (oldVariance ellOld r) f b
  have hU:0≤U:=(hcb (0,0) (0,0)).1.trans (hcb (0,0) (0,0)).2
  have heword:=he target ht1 Λ hΛ t ht hth hage s hs hmin c hc U ell hcb hell hcl d m hm
    (r/(4*π^2)) (by positivity) (oldVariance ellOld r) f f' b A0 ν M H β
    hA0 hν hf hfb hfD hb hbB hH hβ hholder
  have hE:(∫x,(∫y,‖HeatMarkov.kernel (r/(4*π^2)) (by positivity) y‖^2*F (y,x) ∂haarAddCircle)^2 ∂haarAddCircle)≤
      ‖unitHeatKernel (r/(4*π^2)) 0‖^4*
      (4*A0*rootClipMass (oldVariance ellOld r) ν*
        sqrt (H^2*(upperConstant*U*s^(1/2:ℝ))^β*gaussianAbsMoment (2*β)))^2*
      ((C/ell)*(sqrt s)⁻¹)*‖d‖^2:=by
    convert! heword.2 using 1
    rw[hleaf]
  exact physical_energy_to_power haarAddCircle _ hellOld hell hC.le hr hr1 hs hU hA0 hν (norm_nonneg d) hE

end SHE.NativeFirstWordMeanPower
