module
public import SHE.OrdinaryRootGradientContinuity
public import SHE.OrdinaryTerminalGradientBound
public import SHE.NativeVariableTerminalCap

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryRootGradientLimit
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation WordRecursion OrthogonalItoChannels CutoffWordLevel CutoffWordHistories Filter Topology
open scoped NNReal ENNReal
local instance ordinaryRootGradientLimit_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryRootGradientLimit_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryRootGradientLimit_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryRootGradientLimit_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryRootGradientLimit_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)(δ:ℝ)(hδ:0<δ)(k:ℕ)
local notation "Q"=>RootHeatBounds.level L δ hδ
local notation "Raw"=>(fun ε:ℝ≥0=>OrdinaryPhysicalGradient.raw m (Q ε k))

/-- Genuine original-history/current/sample domination, uniform down
to zero root heat. The terminal singularity is kept integrable. -/
theorem uniform_integrable_bound(hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)
    (ν:Measure (History Y k))[IsFiniteMeasure ν]:
    ∃B:History Y k×(ℝ≥0×Ω)→ℝ,Integrable B (ν.prod (energyMeasure μ H))∧∀ε z,‖Raw ε z‖≤B z:=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨C₀,_,hB₀⟩:=(RootHeatBounds.test_uniform L δ hδ k).norm_bound
  obtain ⟨C,hC,hB₁⟩:=(RootHeatBounds.test_uniform L δ hδ k).fderiv.norm_bound
  have hg(ε:ℝ≥0)(p:History Y k)(t:ℝ)(z:WordRecursion.State (n+k)):
      ‖fderiv ℝ (GaussianItoTest.backward ((Q ε k).window p) ((Q ε k).test p) t) z‖≤C:=
    BackwardRegularity.gaussian_state_gradient_bound _
      (((Q ε k).test_uniform.smooth p).of_le (by simp)) (hB₀ (ε,p)) (hB₁ (ε,p)) z
  let N:ℝ:=((n+k:ℕ):ℝ)*C
  have hN:0≤N:=by dsimp only [N];positivity
  let T:=(Q 0 k).terminal
  let cap:=fun z:History Y k×(ℝ≥0×Ω)=>
    if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)) else 0
  let B:=fun z=>N*(1+cap z)
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have hm:0≤κ+M:=add_nonneg m.additive_pos.le hM
  have hT0(p:History Y k):0≤T p:=R.base_nonneg.trans ((Q 0 k).terminal_base p)
  have hi:Integrable cap (ν.prod (energyMeasure μ H)):=
    NativeVariableTerminalCap.integrable ν μ H T (Q 0 k).terminal_measurable hT0
      (fun p=>((Q 0 k).terminal_horizon p).trans hh)
      (fun p=>((Q 0 k).terminal_horizon p).trans hh1) hm
  refine ⟨B,((integrable_const 1).add hi).const_mul N,?_⟩
  intro ε z
  have ht:(Q ε k).terminal z.1=T z.1:=RootHeatBounds.terminal_eq L δ hδ ε 0 k z.1
  by_cases hz:R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<(Q ε k).terminal z.1
  · have hq:(z.2.1:ℝ)<T z.1:=by have hq:=hz.2;rwa [ht] at hq
    have hcap:=NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq)
    have hn:=OrdinaryTerminalGradientBound.raw_terminal_cap m (Q ε k) hC (hg ε) z hz
    rw [ht] at hn
    apply hn.trans
    dsimp only [B,cap,N]
    rw [if_pos hq]
    apply mul_le_mul_of_nonneg_left _ hN
    nlinarith [Real.sq_sqrt hcap,sq_nonneg (Real.sqrt (NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)))-1)]
  · change ‖OrdinaryPhysicalGradient.raw m (Q ε k) z‖≤N*(1+cap z)
    rw [OrdinaryPhysicalGradient.raw,if_neg hz,norm_zero]
    apply mul_nonneg hN
    dsimp only [cap]
    split_ifs with hq
    · exact add_nonneg zero_le_one (NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq))
    · norm_num

theorem average_tendsto(hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)
    (ν:Measure (History Y k))[IsFiniteMeasure ν](e:ℕ→ℝ≥0)(he:Tendsto e atTop (𝓝 0)):
    ∀ᵐz∂energyMeasure μ H,Tendsto (fun j=>∫p,Raw (e j) (p,z) ∂ν)
      atTop (𝓝 (∫p,Raw 0 (p,z) ∂ν)):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨B,hBi,hB⟩:=uniform_integrable_bound m L δ hδ k hh hh1 ν
  have hm(ε:ℝ≥0):Measurable (Raw ε):=by
    have h:=OrdinaryPhysicalGradient.raw_predictable m (Q ε k)
    have hmap:@Measurable (History Y k×(ℝ≥0×Ω)) (History Y k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (History Y k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact h.comp hmap
  filter_upwards [hBi.prod_left_ae] with z hz
  apply tendsto_integral_of_dominated_convergence (μ:=ν) (fun p=>B (p,z))
    (fun j=>(hm (e j)).comp (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable)
    hz (fun j=>Eventually.of_forall (fun p=>hB _ _))
  exact Eventually.of_forall (fun p=>
    (OrdinaryRootGradientContinuity.raw_continuous m L δ hδ k (p,z)).continuousAt.tendsto.comp he)

end SHE.OrdinaryRootGradientLimit
