module
public import SHE.OrdinaryUncutPhysicalGradient
public import SHE.OrdinaryTerminalGradientBound
public import SHE.NativeWeightedTerminalCap

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryUncutPhysicalLimit
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  WordRecursion OrthogonalItoChannels CutoffWordLevel CutoffWordHistories Filter Topology
open scoped NNReal ENNReal
local instance ordinaryUncutPhysicalLimit_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryUncutPhysicalLimit_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryUncutPhysicalLimit_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryUncutPhysicalLimit_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryUncutPhysicalLimit_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)(k:ℕ)
local notation "NL"=>UncutWordEvaluation.normalizedLevel L k
local notation "W"=>UncutSmoothWords.weight L k
local notation "Raw"=>OrdinaryUncutPhysicalGradient.raw m L k
local notation "Cut"=>(fun δ:ℝ=>fun hδ:0<δ=>OrdinaryPhysicalGradient.raw m (RecursiveHeatBounds.level L δ hδ 0 k))

theorem uniform_integrable_bound(hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)
    (ν:Measure (History Y k))[IsFiniteMeasure ν](hWi:Integrable W ν):
    ∃B:History Y k×(ℝ≥0×Ω)→ℝ,Integrable B (ν.prod (energyMeasure μ H))∧
      (∀z,‖Raw z‖≤B z)∧∀δ hδ z,‖Cut δ hδ z‖≤B z:=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨C,hC,hCb⟩:=OrdinaryGradientBounds.gradient_bound NL
  let N:ℝ:=((n+k:ℕ):ℝ)*C
  have hN:0≤N:=by dsimp only [N];positivity
  let T:=(NL).terminal
  let cap:=fun z:History Y k×(ℝ≥0×Ω)=>
    if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)) else 0
  let B:=fun z=>N*(W z.1+W z.1*cap z)
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have hm:0≤κ+M:=add_nonneg m.additive_pos.le hM
  have hi:Integrable (fun z:History Y k×(ℝ≥0×Ω)=>W z.1*cap z) (ν.prod (energyMeasure μ H)):=
    NativeWeightedTerminalCap.integrable ν μ H T (NL).terminal_measurable
      (fun p=>R.base_nonneg.trans ((NL).terminal_base p))
      (fun p=>((NL).terminal_horizon p).trans hh) (fun p=>((NL).terminal_horizon p).trans hh1) hm
      W (UncutSmoothWords.weight_measurable L k) (UncutSmoothWords.weight_nonneg L k) hWi
  have hb(z:History Y k×(ℝ≥0×Ω)):‖Raw z‖≤B z:=by
    have hw:0≤W z.1:=UncutSmoothWords.weight_nonneg L k z.1
    by_cases hz:R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<T z.1
    · have hn:=OrdinaryTerminalGradientBound.raw_terminal_cap m NL hC hCb z hz
      have hcap:=NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hz.2)
      have hs:Real.sqrt (NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)))≤
          1+NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)):=by
        nlinarith [Real.sq_sqrt hcap,sq_nonneg (Real.sqrt (NativeObservationCaps.cap (κ+M) (T z.1-(z.2.1:ℝ)))-1)]
      rw [OrdinaryUncutPhysicalGradient.raw,norm_smul,Real.norm_eq_abs,abs_of_nonneg hw]
      apply (mul_le_mul_of_nonneg_left hn hw).trans
      dsimp only [B,cap,N]
      rw [if_pos hz.2]
      nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hw hN)]
    · have hB:0≤B z:=by
        dsimp only [B,cap]
        apply mul_nonneg hN
        apply add_nonneg hw
        apply mul_nonneg hw
        split_ifs with hq
        · exact NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq)
        · norm_num
      have hz':¬(R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<(NL).terminal z.1):=hz
      simpa only [OrdinaryUncutPhysicalGradient.raw,OrdinaryPhysicalGradient.raw,if_neg hz',smul_zero,norm_zero] using hB
  refine ⟨B,((hWi.comp_fst (energyMeasure μ H)).add hi).const_mul N,hb,?_⟩
  intro δ hδ z
  change ‖OrdinaryPhysicalGradient.raw m (RecursiveHeatBounds.level L δ hδ 0 k) z‖≤B z
  rw [OrdinaryUncutPhysicalGradient.cutoff_eq m L k δ hδ z]
  split_ifs
  · exact hb z
  · exact (norm_zero).le.trans ((norm_nonneg (Raw z)).trans (hb z))

theorem average_tendsto(hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)
    (ν:Measure (History Y k))[IsFiniteMeasure ν](hWi:Integrable W ν)
    (d:ℕ→ℝ)(hd:∀j,0<d j)(ht:Tendsto d atTop (𝓝[>] (0:ℝ))):
    ∀ᵐz∂energyMeasure μ H,Tendsto (fun j=>∫p,Cut (d j) (hd j) (p,z) ∂ν)
      atTop (𝓝 (∫p,Raw (p,z) ∂ν)):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨B,hBi,hG,hB⟩:=uniform_integrable_bound m L k hh hh1 ν hWi
  have hm(j:ℕ):Measurable (Cut (d j) (hd j)):=by
    have h:=OrdinaryPhysicalGradient.raw_predictable m (RecursiveHeatBounds.level L (d j) (hd j) 0 k)
    have hmap:@Measurable (History Y k×(ℝ≥0×Ω)) (History Y k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (History Y k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact h.comp hmap
  filter_upwards [hBi.prod_left_ae] with z hz
  apply tendsto_integral_of_dominated_convergence (μ:=ν) (fun p=>B (p,z))
    (fun j=>(hm j).comp (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable)
    hz (fun j=>Eventually.of_forall (fun p=>hB _ _ _))
  exact Eventually.of_forall (fun p=>by
    obtain ⟨η,hη,heq⟩:=OrdinaryUncutPhysicalGradient.eventually_eq m L k (p,z)
    apply tendsto_const_nhds.congr'
    filter_upwards [ht.eventually ((eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds)] with j hj
    exact (heq _ (hd j) hj).symm)

end SHE.OrdinaryUncutPhysicalLimit
