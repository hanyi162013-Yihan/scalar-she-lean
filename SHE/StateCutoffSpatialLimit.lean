module

public import SHE.HeatFieldWeightedLimit
public import SHE.PredictableWordState

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.StateCutoffSpatialLimit
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffWordAnalytic HeatFieldWeightedLimit PredictableWordState NativeHeatObservation
open SmoothWords GaussianTaylor Filter Topology
open DyadicApproximation
open scoped NNReal ENNReal
local instance heatCutoffSpatialLimit_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance heatCutoffSpatialLimit_realSigma : MeasurableSpace RealL2 := borel RealL2
local instance heatCutoffSpatialLimit_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance heatCutoffSpatialLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance heatCutoffSpatialLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩

variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n)
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Measure Ω} [IsProbabilityMeasure τ]
variable {h : ℝ≥0} (m : Data 𝓕 τ h)

def nodeClock (q : (P × Ω) × ℝ) : ℝ := ClippedCovariance.clip R.base (L.terminal q.1.1) q.2

theorem nodeClock_measurable : Measurable (nodeClock (Ω := Ω) L) :=
  measurable_const.max ((L.terminal_measurable.comp measurable_fst.fst).min measurable_snd)

def nodeState (q : (P × Ω) × ℝ) : RealL2 := m.state ((nodeClock L q).toNNReal,q.1.2)

theorem nodeState_measurable : Measurable (nodeState L m) := by
  have hu : Measurable m.state := (m.state_predictable.mono (PredictableL2.predictable_le_product 𝓕)).measurable
  exact hu.comp (((measurable_real_toNNReal.comp (nodeClock_measurable L)).prodMk measurable_fst.snd))

def oldState (q : (P × Ω) × ℝ) : WordRecursion.State n :=
  observe (fun t => m.physicalState (q.1.2,t)) (fun z => m.physicalField (q.1.2,z))
    (L.observations.observations q.1.1) (nodeClock L q)

theorem oldState_measurable : Measurable (oldState L m) := by
  have hm := physical_observe_measurable L m.physicalState_measurable m.physicalField_measurable
  exact hm.comp (measurable_fst.prodMk (nodeClock_measurable L))

def historyPoint (q : (((P × Ω) × ℝ) × HeatCircle)) : P × (ℝ × HeatCircle) :=
  (q.1.1.1,(q.1.2,q.2))

theorem historyPoint_measurable : Measurable (historyPoint (P := P) (Ω := Ω)) :=
  measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)

def weight (δ : ℝ) (q : (((P × Ω) × ℝ) × HeatCircle)) : ℝ :=
  (1/2:ℝ)*directionalSecond (L.averagedTest (historyPoint q)) (oldState L m q.1)
    (L.cutoffRow δ (historyPoint q))

theorem weight_measurable (δ : ℝ) : Measurable (weight L m δ) := by
  have hh := MeasurableDerivatives.hessian_measurable L.averagedTest_measurable
    (fun p => (L.averagedTest_uniform.smooth p).of_le (by simp))
  have hH := hh.comp ((historyPoint_measurable (P := P) (Ω := Ω)).prodMk
    ((oldState_measurable L m).comp measurable_fst))
  have hr := (L.cutoffRow_measurable δ).comp (historyPoint_measurable (P := P) (Ω := Ω))
  have he₁ : Continuous (fun p : (WordRecursion.State n →L[ℝ] WordRecursion.State n →L[ℝ] ℝ) × WordRecursion.State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have he₂ : Continuous (fun p : (WordRecursion.State n →L[ℝ] ℝ) × WordRecursion.State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (he₂.measurable.comp ((he₁.measurable.comp (hH.prodMk hr)).prodMk hr)).const_mul (1/2:ℝ)

theorem weight_bounded {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ q,|weight L m δ q| ≤ C := by
  obtain ⟨B,hB,hH⟩ := L.averagedTest_uniform.fderiv.fderiv.norm_bound
  let Q : ℝ := Real.sqrt n*CovarianceMatrix.heatRowBound δ
  have hQ : 0 ≤ Q := mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos hδ).le
  refine ⟨(1/2:ℝ)*B*Q^2,by positivity,fun q => ?_⟩
  let H := GaussianTaylor.hessian (L.averagedTest (historyPoint q)) (oldState L m q.1)
  let r := L.cutoffRow δ (historyPoint q)
  have hr : ‖r‖ ≤ Q := L.cutoffRow_bound hδ _
  have hb : ‖H r r‖ ≤ B*Q^2 := by
    have hh := (GaussianTaylor.bilinear_norm_le H r r).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hH _ _) (norm_nonneg r)) (norm_nonneg r))
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg r) hr 2) hB
    exact hh.trans (by nlinarith only [hs])
  change |(1/2:ℝ)*H r r| ≤ _
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq (by ring)

theorem child_difference_mass (δ ε : ℝ) (hε : 0 < ε) (q : (P × Ω) × ℝ) :
    (∫ x : HeatCircle,|HeatCutoffStep.childLeaf L δ ε m.physicalState m.physicalField
      (q.1.1,(q.2,x)) q.1.2-CutoffWordStep.childLeaf L δ m.physicalState m.physicalField
      (q.1.1,(q.2,x)) q.1.2| ∂haarAddCircle)=
      HeatFieldWeightedLimit.mass (nodeState L m) R.totalVariance (weight L m δ) ε q := by
  apply integral_congr_ae
  filter_upwards with x
  rw [HeatCutoffStep.childLeaf_sub_literal L δ ε m.physicalState m.physicalField hε]
  change abs ((1/2:ℝ)*(R.totalVariance _-R.totalVariance _)*_)=abs ((_ - _)*((1/2:ℝ)*_))
  dsimp only [historyPoint,nodeState,nodeClock,oldState,CutoffWordLevel.Level.nodeTime,
    PredictableWordState.Data.physicalState,PredictableWordState.Data.physicalField,
    PredictableScalarField.wordField,PredictableScalarField.nativeField,PredictableScalarField.unitField]
  congr 1
  ring

/-- At a fixed level and fixed time cutoff δ, the literal additional
ε heat regularization error vanishes in full history/expectation/time/
space L¹. This does not assert a uniform limit for ε-dependent levels. -/
theorem integrated_child_difference_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (μ : Measure P) [IsFiniteMeasure μ] :
    Tendsto (fun ε => ∫ q : (P × Ω) × ℝ,
      ∫ x : HeatCircle,|HeatCutoffStep.childLeaf L δ ε m.physicalState m.physicalField
        (q.1.1,(q.2,x)) q.1.2-CutoffWordStep.childLeaf L δ m.physicalState m.physicalField
        (q.1.1,(q.2,x)) q.1.2| ∂haarAddCircle
      ∂(μ.prod τ).prod (volume.restrict (Ioc R.base R.horizon))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hC,hCb⟩ := weight_bounded L m hδ
  obtain ⟨M,hM⟩ := R.totalVariance_smooth.norm_bound
  obtain ⟨B,hB⟩ := R.totalVariance_smooth.fderiv.norm_bound
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hLip (z w : ℝ) : |R.totalVariance z-R.totalVariance w| ≤ B*|z-w| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => R.totalVariance_smooth.smooth.differentiable (by simp) y)
      (fun y _ => hB y) convex_univ (mem_univ w) (mem_univ z)
  have ht := HeatFieldWeightedLimit.integrated_mass_tendsto_zero (nodeState L m) (nodeState_measurable L m)
    R.totalVariance R.totalVariance_smooth.smooth.continuous.measurable (weight L m δ) (weight_measurable L m δ)
    ((μ.prod τ).prod (volume.restrict (Ioc R.base R.horizon)))
    (fun z => by simpa only [Real.norm_eq_abs] using hM z) hC hCb hBn hLip
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  filter_upwards with q
  exact (child_difference_mass L m δ ε hε q).symm

end SHE.StateCutoffSpatialLimit
