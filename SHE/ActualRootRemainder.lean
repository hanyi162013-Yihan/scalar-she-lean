module
public import SHE.ActualRootSpatial

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ActualRootRemainder
open scoped NNReal
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  RootHeatBounds RootHeatTargets Filter Topology PhysicalIto PhysicalRemainderBound PhysicalRemainderMass
local instance actualRootRemainder_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance actualRootRemainder_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance actualRootRemainder_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type*}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)(δ:ℝ)(hδ:0<δ)
variable (a:ℝ→ℝ)(ha:Measurable a){A:ℝ}(hAn:0≤A)(hA:∀z,|a z|≤A)
variable (U:Ω×ℝ→CircleL2)(X:Ω×(ℝ×HeatCircle)→ℝ)

def remainder (ε:ℝ≥0)(k:ℕ)(p:History P k)(ω:Ω):ℝ:=
  wordRemainder ((level L δ hδ ε k).window p) a
    (fun t=>U (ω,t)) (fun q=>X (ω,q)) ((level L δ hδ ε k).test p)

include hAn hA in
theorem uniform_spatial_bound (k:ℕ):∃K:ℝ,0≤K∧∀ε:ℝ≥0,∀p ω t,
    t∈Ioo R.base ((level L δ hδ 0 k).terminal p)→
      ‖ActualRootSpatial.spatial L δ hδ a U X ε k p ω t‖≤
        K*(1+heatConstant*((level L δ hδ 0 k).terminal p-t)^(-(1/2:ℝ))):=by
  obtain ⟨C,_,hC⟩:=(test_uniform L δ hδ k).norm_bound
  obtain ⟨D,_,hD⟩:=(test_uniform L δ hδ k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩:=(test_uniform L δ hδ k).fderiv.fderiv.norm_bound
  let K:=(1/2:ℝ)*(A+R.upper)*B*((n+k:ℕ):ℝ)
  refine ⟨K,mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (add_nonneg hAn R.upper_nonneg)) hBn) (Nat.cast_nonneg _),fun ε p ω t ht=>?_⟩
  have hte:t∈Ioo ((level L δ hδ ε k).window p).left ((level L δ hδ ε k).window p).right:=by
    change t∈Ioo R.base ((level L δ hδ ε k).terminal p)
    rw [terminal_eq L δ hδ ε 0 k p]
    exact ht
  have hHb:∀z,‖GaussianTaylor.hessian (GaussianItoTest.backward
      ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) z‖≤B:=
    fun z=>BackwardRegularity.gaussian_state_hessian_bound _
      (((level L δ hδ ε k).test_uniform.smooth p).of_le (by simp)) (hC (ε,p)) (hD (ε,p)) (hB (ε,p)) z
  have hh:=inserted_spatial_norm_bound ((level L δ hδ ε k).window p) hAn hA hBn
    (fun t=>U (ω,t)) (fun q=>X (ω,q)) hte
    (GaussianItoTest.backward ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) hHb
  change ‖ActualRootSpatial.spatial L δ hδ a U X ε k p ω t‖≤
    K*(1+heatConstant*((level L δ hδ ε k).terminal p-t)^(-(1/2:ℝ))) at hh
  rw [terminal_eq L δ hδ ε 0 k p] at hh
  exact hh

include hAn hA in
theorem uniform_remainder_bound (k:ℕ):∃K:ℝ,0≤K∧∀ε:ℝ≥0,∀p ω,
    ‖remainder L δ hδ a U X ε k p ω‖≤K:=by
  obtain ⟨C,_,hC⟩:=(test_uniform L δ hδ k).norm_bound
  obtain ⟨D,_,hD⟩:=(test_uniform L δ hδ k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩:=(test_uniform L δ hδ k).fderiv.fderiv.norm_bound
  let K:=((1/2:ℝ)*(A+R.upper)*B*((n+k:ℕ):ℝ))*heatMass R.horizon
  have hhorizon:0≤R.horizon:=R.base_nonneg.trans R.ordered
  refine ⟨K,mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (add_nonneg hAn R.upper_nonneg)) hBn) (Nat.cast_nonneg _))
    (heatMass_nonneg hhorizon),fun ε p ω=>?_⟩
  exact remainder_horizon_bound ((level L δ hδ ε k).window p) hAn hA hBn le_rfl
    R.base_nonneg ((level L δ hδ ε k).terminal_horizon p) (fun t=>U (ω,t)) (fun q=>X (ω,q))
    (((level L δ hδ ε k).test_uniform.smooth p).of_le (by simp)) (hC (ε,p)) (hD (ε,p)) (hB (ε,p))

include ha hAn hA in
/-- Actual merely measurable bracket remainder has the genuine
zero-heat limit; its time domination is the integrable row-square mass. -/
theorem continuous_remainder (hU:Measurable U)(hX:Measurable X)
    (k:ℕ)(p:History P k)(ω:Ω):
    Continuous (fun ε:ℝ≥0=>remainder L δ hδ a U X ε k p ω):=by
  obtain ⟨K,hK,hKb⟩:=uniform_spatial_bound L δ hδ a hAn hA U X k
  let s:=(level L δ hδ 0 k).terminal p
  have hs:R.base≤s:=(level L δ hδ 0 k).terminal_base p
  have he:(fun ε:ℝ≥0=>remainder L δ hδ a U X ε k p ω)=
      fun ε=>∫t,ActualRootSpatial.spatial L δ hδ a U X ε k p ω t ∂volume.restrict (Ioc R.base s):=by
    funext ε
    change (∫t in R.base..(level L δ hδ ε k).terminal p,ActualRootSpatial.spatial L δ hδ a U X ε k p ω t)=_
    rw [terminal_eq L δ hδ ε 0 k p,intervalIntegral.integral_of_le hs]
  rw [he]
  apply continuous_of_dominated (bound:=fun t:ℝ=>K*(1+heatConstant*(s-t)^(-(1/2:ℝ))))
  · intro ε
    have hp:Measurable (fun t:ℝ=>((p,ω),t)):=measurable_const.prodMk measurable_id
    exact ((ActualRootSpatial.spatial_measurable L δ hδ a ha U X hU hX ε k).comp hp).aestronglyMeasurable
  · intro ε
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    exact hKb ε p ω t ⟨ht.1,lt_of_le_of_ne ht.2 hts⟩
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q:=R.base) (s:=s) K).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    exact ActualRootSpatial.continuous_spatial L δ hδ a ha hAn hA U X hU hX k p ω
      ⟨ht.1,lt_of_le_of_ne ht.2 hts⟩

include ha hAn hA in
theorem integrated_difference_tendsto_zero (hU:Measurable U)(hX:Measurable X)
    (ν:Measure P)[IsFiniteMeasure ν](μ:Measure Ω)[IsFiniteMeasure μ](k:ℕ):
    Tendsto (fun ε:ℝ=>∫z:History P k×Ω,
      |remainder L δ hδ a U X ε.toNNReal k z.1 z.2-remainder L δ hδ a U X 0 k z.1 z.2|
        ∂(historyMeasure R ν k).prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  obtain ⟨K,hK,hKb⟩:=uniform_remainder_bound L δ hδ a hAn hA U X k
  have hm(ε:ℝ):Measurable (fun z:History P k×Ω=>
      |remainder L δ hδ a U X ε.toNNReal k z.1 z.2-remainder L δ hδ a U X 0 k z.1 z.2|):=
    ((ActualVarianceLevel.remainder_measurable (level L δ hδ ε.toNNReal k) a ha U hU X hX (fun _ _ _=>0)).sub
      (ActualVarianceLevel.remainder_measurable (level L δ hδ 0 k) a ha U hU X hX (fun _ _ _=>0))).norm
  have ht(z:History P k×Ω):Tendsto (fun ε:ℝ=>
      |remainder L δ hδ a U X ε.toNNReal k z.1 z.2-remainder L δ hδ a U X 0 k z.1 z.2|)
        (𝓝[>] (0:ℝ)) (𝓝 0):=by
    have hc:=(continuous_remainder L δ hδ a ha hAn hA U X hU hX k z.1 z.2).comp continuous_real_toNNReal
    have hh:=((hc.tendsto (0:ℝ)).sub_const (remainder L δ hδ a U X 0 k z.1 z.2)).norm
    simpa only [Function.comp_def,Real.toNNReal_zero,sub_self,norm_zero,Real.norm_eq_abs] using
      hh.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hi:=tendsto_integral_filter_of_dominated_convergence (μ:=(historyMeasure R ν k).prod μ)
    (fun _=>2*K) (Filter.Eventually.of_forall (fun ε=>(hm ε).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun ε=>Filter.Eventually.of_forall (fun z=>by
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans ((add_le_add (hKb ε.toNNReal z.1 z.2) (hKb 0 z.1 z.2)).trans_eq (by ring)))))
    (integrable_const _) (Filter.Eventually.of_forall ht)
  simpa only [integral_zero] using hi

end SHE.ActualRootRemainder
