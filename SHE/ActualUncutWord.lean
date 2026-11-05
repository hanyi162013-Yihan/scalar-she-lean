module
public import SHE.ActualUncutRemainder
public import SHE.JointInsertionIntegrability

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.ActualUncutWord
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers UncutWordEvaluation PhysicalIto GaussianItoTest CovarianceEndpoint
local instance actualUncutWord_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance actualUncutWord_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance actualUncutWord_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)
variable (U:Ω×ℝ→CircleL2)(X:Ω×(ℝ×HeatCircle)→ℝ)

theorem inserted_test_smul (W:EndpointWindow n)(a:ℝ→ℝ)(F:WordRecursion.State n→ℝ)
    (w:ℝ)(ω:Ω)(t:ℝ)(x:HeatCircle):
    insertedWord W a (fun s=>U (ω,s)) (fun q=>X (ω,q)) (w • F) t x=
      w*insertedWord W a (fun s=>U (ω,s)) (fun q=>X (ω,q)) F t x:=by
  have hb:backward W (w • F) t=w • backward W F t:=by
    change GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0 (W.path t).val) (w • F)=
      w • GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0 (W.path t).val) F
    rw [NormalizedInsertion.average_smul]
  unfold insertedWord
  rw [insertion_observe,insertion_observe,hb]
  change (1/2:ℝ)*(a (X (ω,(t,x)))-W.coefficient (t,x))*
      GaussianTaylor.hessian (w • backward W F t)
        (observe (fun s=>U (ω,s)) (fun q=>X (ω,q)) W.observations t)
        (heatRow W.observations t x) (heatRow W.observations t x)=_
  rw [NormalizedInsertion.hessian_smul]
  simp only [Pi.smul_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  simp only [WordRecursion.directionalSecond,WordRecursion.hessian,GaussianTaylor.hessian]
  ring

theorem remainder_test_smul (W:EndpointWindow n)(a:ℝ→ℝ)(F:WordRecursion.State n→ℝ)
    (w:ℝ)(ω:Ω):
    wordRemainder W a (fun s=>U (ω,s)) (fun q=>X (ω,q)) (w • F)=
      w*wordRemainder W a (fun s=>U (ω,s)) (fun q=>X (ω,q)) F:=by
  unfold wordRemainder
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x=>inserted_test_smul U X W a F w ω t x)

/-- The weighted normalized remainder is exactly the physical remainder
of the original full word. No normalization or sign is discarded. -/
theorem value_eq_full (a:ℝ→ℝ)(k:ℕ)(p:History P k)(ω:Ω):
    ActualUncutRemainder.value L a U X k p ω=
      wordRemainder ((carrier L k).window p) a (fun s=>U (ω,s)) (fun q=>X (ω,q))
        (UncutSmoothWords.test L k p):=by
  rw [UncutSmoothWords.test_eq_weight_normalized,remainder_test_smul]
  rfl

def spatial (a:ℝ→ℝ)(p:P)(ω:Ω)(t:ℝ):ℝ:=
  ∫x:HeatCircle,insertedWord (L.window p) a (fun s=>U (ω,s)) (fun q=>X (ω,q))
    (L.test p) t x ∂AddCircle.haarAddCircle

theorem time_integrable (a:ℝ→ℝ)(ha:Measurable a){A:ℝ}(hAn:0≤A)(hA:∀z,|a z|≤A)
    (hU:Measurable U)(hX:Measurable X)(p:P)(ω:Ω):
    IntervalIntegrable (spatial L U X a p ω) volume R.base (L.terminal p):=by
  have hm:=(ActualVarianceLevel.insertion_measurable L a ha U hU X hX).comp
    (((measurable_const (a:=(p,ω))).prodMk measurable_fst).prodMk measurable_snd)
  have ht:=hm.stronglyMeasurable.integral_prod_right' (ν:=AddCircle.haarAddCircle)
  obtain ⟨C,_,hC⟩:=L.test_uniform.norm_bound
  obtain ⟨D,_,hD⟩:=L.test_uniform.fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩:=L.test_uniform.fderiv.fderiv.norm_bound
  let K:=(1/2:ℝ)*(A+R.upper)*B*n
  have hd:IntervalIntegrable (fun t=>K*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))))
      volume R.base (L.terminal p):=CovarianceEndpoint.endpoint_majorant_integrable K
  apply hd.mono_fun' ht.aestronglyMeasurable
  rw [uIoc_of_le (L.terminal_base p)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (L.terminal p))] with t htin hne
  have hW:t∈Ioo (L.window p).left (L.window p).right:=⟨htin.1,lt_of_le_of_ne htin.2 hne⟩
  exact PhysicalRemainderBound.inserted_spatial_norm_bound (L.window p) hAn hA hBn
    (fun s=>U (ω,s)) (fun q=>X (ω,q)) hW (backward (L.window p) (L.test p) t)
    (fun z=>BackwardRegularity.gaussian_state_hessian_bound _
      ((L.test_uniform.smooth p).of_le (by simp)) (hC p) (hD p) (hB p) z)

/-- The actual-minus-reference remainder is the time integral of the
literal difference of their spatial insertions. -/
theorem remainder_sub (a c:ℝ→ℝ)(ha:Measurable a)(hc:Measurable c)
    {A C:ℝ}(hAn:0≤A)(hA:∀z,|a z|≤A)(hCn:0≤C)(hC:∀z,|c z|≤C)
    (hU:Measurable U)(hX:Measurable X)(p:P)(ω:Ω):
    wordRemainder (L.window p) a (fun s=>U (ω,s)) (fun q=>X (ω,q)) (L.test p)-
      wordRemainder (L.window p) c (fun s=>U (ω,s)) (fun q=>X (ω,q)) (L.test p)=
        ∫t in R.base..L.terminal p,spatial L U X a p ω t-spatial L U X c p ω t:=
  (intervalIntegral.integral_sub
    (time_integrable L U X a ha hAn hA hU hX p ω)
    (time_integrable L U X c hc hCn hC hU hX p ω)).symm

end SHE.ActualUncutWord
