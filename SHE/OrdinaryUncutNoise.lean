module
public import SHE.OrdinaryLevelOriginalNoise
public import SHE.ActualVarianceScaling
public import SHE.ActualUncutRemainder
public import SHE.WeightedHistoryL2Limit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryUncutNoise
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers CutoffUncutComparison UncutWordEvaluation GaussianItoTest IntegratedPhysicalStep Topology
open scoped NNReal
open Classical
local instance ordinaryUncutNoise_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryUncutNoise_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)

def version (p:P)(ω:Ω):ℝ:=(OrdinaryLevelOriginalNoise.data m L (fun _ _ _=>0)).noiseVersion p ω

theorem conditions:AnalyticConditions (OrdinaryLevelOriginalNoise.data m L (fun _ _ _=>0)):=by
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have hcap(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  exact ActualVarianceLevel.analyticConditions L (fun z=>κ+a z) (measurable_const.add m.variance_measurable)
    m.physicalState m.physicalState_measurable m.physicalField m.physicalField_measurable (fun _ _ _=>0)
    (add_nonneg m.additive_pos.le hM) hcap

theorem version_measurable:Measurable (fun z:P×Ω=>version m L z.1 z.2):=
  (((conditions m L).leaf_measurable.sub (conditions m L).reference_measurable).sub (conditions m L).remainder_measurable)

theorem version_bound:∃C:ℝ,0≤C ∧∀p ω,‖version m L p ω‖≤C:=by
  obtain ⟨C,hC,hCb⟩:=uniform_level_bound _ (conditions m L)
  exact ⟨C,hC,fun p ω=>(hCb p ω).2.2.2⟩

theorem version_smul (Q:Level R P n)(w:ℝ)(p:P)(ω:Ω)
    (hobs:L.observations.observations p=Q.observations.observations p)
    (htime:L.terminal p=Q.terminal p)(hF:L.test p=w • Q.test p):
    version m L p ω=w*version m Q p ω:=by
  have hb(t:ℝ):backward (L.window p) (L.test p) t=w • backward (Q.window p) (Q.test p) t:=by
    change GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (covariance R.reference (L.observations.observations p)
        (ClippedCovariance.clip R.base (L.terminal p) t) (L.terminal p))) (L.test p)=_
    rw [hobs,htime,hF,NormalizedInsertion.average_smul]
    rfl
  let DL:=OrdinaryLevelOriginalNoise.data m L (fun _ _ _=>0)
  let DQ:=OrdinaryLevelOriginalNoise.data m Q (fun _ _ _=>0)
  have hl:DL.leaf p ω=w*DQ.leaf p ω:=by
    change L.test p (observe _ _ (L.observations.observations p) (L.terminal p))=_
    rw [hF,hobs,htime]
    rfl
  have hr:DL.reference p ω=w*DQ.reference p ω:=by
    change backward (L.window p) (L.test p) R.base
      (observe _ _ (L.observations.observations p) R.base)=_
    rw [hb,hobs]
    rfl
  have hc:=ActualVarianceScaling.remainder_smul L Q (fun z=>κ+a z) m.physicalState m.physicalField
    w p ω hobs htime hF
  change DL.remainder p ω=w*DQ.remainder p ω at hc
  change DL.noiseVersion p ω=w*DQ.noiseVersion p ω
  dsimp only [LevelData.noiseVersion]
  rw [hl,hr,hc]
  ring

def value (k:ℕ)(p:History P k)(ω:Ω):ℝ:=
  UncutSmoothWords.weight L k p*version m (normalizedLevel L k) p ω
def cutoff (δ:ℝ)(k:ℕ)(p:History P k)(ω:Ω):ℝ:=
  if hδ:0<δ then version m (RecursiveHeatBounds.level L δ hδ 0 k) p ω else 0

theorem cutoff_eq {δ:ℝ}(hδ:0<δ)(k:ℕ)(p:History P k)(ω:Ω):
    cutoff m L δ k p ω=if Active L δ k p then value m L k p ω else 0:=by
  rw [cutoff,dif_pos hδ]
  by_cases hp:Active L δ k p
  · rw [if_pos hp]
    exact version_smul m _ (normalizedLevel L k) (UncutSmoothWords.weight L k p) p ω
      (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
      (by rw [test_eq_active L hδ k p,if_pos hp,UncutSmoothWords.test_eq_weight_normalized];rfl)
  · rw [if_neg hp]
    have he:=version_smul m (RecursiveHeatBounds.level L δ hδ 0 k) (normalizedLevel L k) 0 p ω
      (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
      (by rw [test_eq_active L hδ k p,if_neg hp,zero_smul])
    simpa only [zero_mul] using he

theorem bound (k:ℕ):∃C:ℝ,0≤C∧∀p ω,‖value m L k p ω‖≤C*UncutSmoothWords.weight L k p:=by
  obtain ⟨C,hC,hCb⟩:=version_bound m (normalizedLevel L k)
  refine ⟨C,hC,fun p ω=>?_⟩
  rw [value,norm_mul,Real.norm_eq_abs,abs_of_nonneg (UncutSmoothWords.weight_nonneg L k p)]
  exact (mul_le_mul_of_nonneg_left (hCb p ω) (UncutSmoothWords.weight_nonneg L k p)).trans_eq (mul_comm _ _)

theorem value_measurable (k:ℕ):Measurable (fun z:History P k×Ω=>value m L k z.1 z.2):=
  ((UncutSmoothWords.weight_measurable L k).comp measurable_fst).mul (version_measurable m (normalizedLevel L k))

/-- Strong time-gap removal for the COMPLETE actual ordinary-U noise,
retaining the original integrable history weight before averaging. -/
theorem averaged_limit (ν:Measure P)[IsFiniteMeasure ν](k:ℕ):
    let E:=fun δ:ℝ=>fun ω=>∫p,cutoff m L δ k p ω-value m L k p ω ∂historyMeasure R ν k
    (∀δ,Integrable (fun ω=>‖E δ ω‖^2) μ) ∧
      Tendsto (fun δ=>∫ω,‖E δ ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  obtain ⟨C,hC,hCb⟩:=bound m L k
  let W:=UncutSmoothWords.weight L k
  have hW:Integrable W (historyMeasure R ν k):=UncutHistoryMass.weight_integrable L ν k
  have hm:=value_measurable m L k
  have hfm(δ:ℝ):Measurable (fun z:History P k×Ω=>cutoff m L δ k z.1 z.2):=by
    by_cases hδ:0<δ
    · simpa only [cutoff,dif_pos hδ] using version_measurable m (RecursiveHeatBounds.level L δ hδ 0 k)
    · simp only [cutoff,dif_neg hδ]
      exact measurable_const
  have hb(δ:ℝ)(p:History P k)(ω:Ω):‖cutoff m L δ k p ω‖≤C*W p:=by
    by_cases hδ:0<δ
    · rw [cutoff_eq m L hδ]
      split_ifs
      · exact hCb p ω
      · exact (norm_zero).le.trans (mul_nonneg hC (UncutSmoothWords.weight_nonneg L k p))
    · rw [cutoff,dif_neg hδ,norm_zero]
      exact mul_nonneg hC (UncutSmoothWords.weight_nonneg L k p)
  have he(z:History P k×Ω):∃η:ℝ,0<η∧∀δ>0,δ<η→cutoff m L δ k z.1 z.2=value m L k z.1 z.2:=by
    obtain ⟨η,hη,hEq⟩:=eventually_test_eq L k z.1
    refine ⟨η,hη,fun δ hδ hd=>?_⟩
    rw [cutoff,dif_pos hδ]
    exact version_smul m _ (normalizedLevel L k) (UncutSmoothWords.weight L k z.1) z.1 z.2
      (observations_eq L hδ zero_lt_one k z.1) (CutoffCarriers.terminal_eq L hδ zero_lt_one k z.1)
      (by rw [hEq δ hδ hd,UncutSmoothWords.test_eq_weight_normalized];rfl)
  have ht:=DominatedCutoffLimit.integral_abs_sub_tendsto_zero ((historyMeasure R ν k).prod μ)
    (W:=fun z=>W z.1) (M:=C) (hW.comp_fst μ) hm (fun δ _=>hfm δ)
    (fun z=>hCb z.1 z.2) (fun δ _ z=>hb δ z.1 z.2) he
  exact WeightedHistoryL2Limit.averaged_limit (historyMeasure R ν k) μ
    (fun δ:ℝ=>fun z=>cutoff m L δ k z.1 z.2) (fun z=>value m L k z.1 z.2)
    hfm hm W hW (UncutSmoothWords.weight_nonneg L k) hC hb hCb (𝓝[>] (0:ℝ))
    (by simpa only [Real.norm_eq_abs] using ht)

end SHE.OrdinaryUncutNoise
