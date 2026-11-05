module
public import SHE.ControlledOrdinaryPhysicalGradient
public import SHE.OrdinaryTerminalGradientBound
public import SHE.NativeWeightedTerminalCap

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ControlledOrdinaryPhysicalSections
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels Filter Topology
open scoped NNReal ENNReal
local instance controlledOrdinaryPhysicalSections_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledOrdinaryPhysicalSections_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance controlledOrdinaryPhysicalSections_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance controlledOrdinaryPhysicalSections_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance controlledOrdinaryPhysicalSections_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance controlledOrdinaryPhysicalSections_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance controlledOrdinaryPhysicalSections_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(A:ℝ→ℝ)(hA:BoundedSmooth A)
variable (Λ θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable {Y:Type}[MeasurableSpace Y]{n:ℕ}(Z:VariableObservations.Family Y n)
variable (htarget:∀y i,(b:ℝ)≤(Z.observations y i).target)(hstop:∀y i,(b:ℝ)≤(Z.observations y i).stop)
variable (F:Y→WordRecursion.State n→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun q:Y×WordRecursion.State n=>F q.1 q.2))
local notation "Base"=>ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm
local notation "NL"=>(fun p k=>UncutWordEvaluation.normalizedLevel (Base p) k)
local notation "R₀"=>referenceData P A hA Λ θ v b hvb (0,0)
variable {Ω:Type}[MeasurableSpace Ω]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable(k:ℕ)
local notation "Raw"=>(fun p:Inputs=>OrdinaryUncutPhysicalGradient.raw m (Base p) k)
local notation "W"=>UncutSmoothWords.weight (Base (0,0)) k

/-- One actual history/current/sample envelope controls all past-input
members, retaining the integrable singular original history weight. -/
theorem uniform_integrable_bound(hbH:b≤H)(hb1:(b:ℝ)≤1)(ν:Measure Y)[IsFiniteMeasure ν]:
    let σ:=historyMeasure R₀ ν k
    ∃B:History Y k×(ℝ≥0×Ω)→ℝ,Integrable B (σ.prod (energyMeasure μ H))∧∀p z,‖Raw p z‖≤B z:=by
  intro σ
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  have hWi:Integrable W σ:=UncutHistoryMass.weight_integrable (Base (0,0)) ν k
  have hJ:=ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k
  obtain ⟨C₀,_,hB₀⟩:=hJ.norm_bound
  obtain ⟨C,hC,hB₁⟩:=hJ.fderiv.norm_bound
  have hg(p:Inputs)(h:History Y k)(t:ℝ)(y:WordRecursion.State (n+k)):
      ‖fderiv ℝ (GaussianItoTest.backward ((NL p k).window h) ((NL p k).test h) t) y‖≤C:=
    BackwardRegularity.gaussian_state_gradient_bound _
      (((NL p k).test_uniform.smooth h).of_le (by simp)) (hB₀ (p,h)) (hB₁ (p,h)) y
  let N:ℝ:=((n+k:ℕ):ℝ)*C
  have hN:0≤N:=by dsimp only [N];positivity
  let T:=(NL (0,0) k).terminal
  let cap:=fun z:History Y k×(ℝ≥0×Ω)=>
    if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)) else 0
  let B:=fun z=>N*(W z.1+W z.1*cap z)
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have hm:0≤κ+M:=add_nonneg m.additive_pos.le hM
  have hi:Integrable (fun z:History Y k×(ℝ≥0×Ω)=>W z.1*cap z) (σ.prod (energyMeasure μ H)):=
    NativeWeightedTerminalCap.integrable σ μ H T (NL (0,0) k).terminal_measurable
      (fun h=>v.2.trans ((NL (0,0) k).terminal_base h))
      (fun h=>((NL (0,0) k).terminal_horizon h).trans (by exact_mod_cast hbH))
      (fun h=>((NL (0,0) k).terminal_horizon h).trans hb1) hm
      W (UncutSmoothWords.weight_measurable _ _) (UncutSmoothWords.weight_nonneg _ _) hWi
  refine ⟨B,((hWi.comp_fst (energyMeasure μ H)).add hi).const_mul N,?_⟩
  intro p z
  have ht:(NL p k).terminal z.1=T z.1:=ControlledReferenceFamilyBounds.carrier_terminal_eq
    P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k z.1
  have hw:UncutSmoothWords.weight (Base p) k z.1=W z.1:=ControlledReferenceFamilyBounds.weight_eq
    P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k z.1
  have hw0:0≤W z.1:=UncutSmoothWords.weight_nonneg _ _ _
  have hbase:(referenceData P A hA Λ θ v b hvb p).base=(v:ℝ):=rfl
  by_cases hz:(v:ℝ)<(z.2.1:ℝ)∧(z.2.1:ℝ)<T z.1
  · have hzp:(referenceData P A hA Λ θ v b hvb p).base<(z.2.1:ℝ)∧(z.2.1:ℝ)<(NL p k).terminal z.1:=by rwa [hbase,ht]
    have hn:=OrdinaryTerminalGradientBound.raw_terminal_cap m (NL p k) hC (hg p) z hzp
    rw [ht] at hn
    have hcap:=NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hz.2)
    have hs:Real.sqrt (NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)))≤
        1+NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)):=by
      nlinarith [Real.sq_sqrt hcap,sq_nonneg (Real.sqrt (NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)))-1)]
    change ‖UncutSmoothWords.weight (Base p) k z.1 • OrdinaryPhysicalGradient.raw m (NL p k) z‖≤B z
    rw [norm_smul,hw,Real.norm_eq_abs,abs_of_nonneg hw0]
    apply (mul_le_mul_of_nonneg_left hn hw0).trans
    dsimp only [B,cap,N]
    rw [if_pos hz.2]
    nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hw0 hN)]
  · have hB:0≤B z:=by
      dsimp only [B,cap]
      apply mul_nonneg hN
      apply add_nonneg hw0
      apply mul_nonneg hw0
      split_ifs with hq
      · exact NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq)
      · norm_num
    simpa only [OrdinaryUncutPhysicalGradient.raw,OrdinaryPhysicalGradient.raw,hbase,ht,if_neg hz,smul_zero,norm_zero] using hB

variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
include hsmall in
theorem average_parameter_continuous(hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)(ν:Measure Y)[IsFiniteMeasure ν]:
    ∀ᵐz∂energyMeasure μ H,Continuous (fun p:Inputs=>∫h,Raw p (h,z) ∂historyMeasure R₀ ν k):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  let σ:=historyMeasure R₀ ν k
  obtain ⟨B,hBi,hB⟩:=uniform_integrable_bound P A hA Λ θ v b hvb Z htarget hstop F hF hFm m k hbH hb1 ν
  have hm(p:Inputs):Measurable (Raw p):=by
    have hh:=OrdinaryUncutPhysicalGradient.raw_predictable m (Base p) k
    have hmap:@Measurable (History Y k×(ℝ≥0×Ω)) (History Y k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (History Y k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact hh.comp hmap
  filter_upwards [hBi.prod_left_ae] with z hz
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_integral_filter_of_dominated_convergence (μ:=σ) (fun h=>B (h,z))
    (Eventually.of_forall (fun p'=>(hm p').comp (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable))
    (Eventually.of_forall (fun p'=>Eventually.of_forall (fun h=>hB p' (h,z)))) hz
    (Eventually.of_forall (fun h=>(ControlledOrdinaryPhysicalGradient.raw_parameter_continuous
      P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall m hΛ k (h,z)).continuousAt.tendsto))

end SHE.ControlledOrdinaryPhysicalSections
