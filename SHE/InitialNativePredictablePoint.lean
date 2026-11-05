module
public import SHE.InitialNativeKernelFields
public import SHE.PredictableClock
public import SHE.MovingNativeFields
public import SHE.ZeroDirectionProfile
public import SHE.MixedPastNativeTimeFields
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.InitialNativePredictablePoint
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance initialNativePredictablePoint_realSigma : MeasurableSpace RealL2 := borel _
local instance initialNativePredictablePoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance initialNativePredictablePoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance initialNativePredictablePoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance initialNativePredictablePoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance initialNativePredictablePoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
open PastItoInputs PastItoAlgebra PhysicalProfile


local instance initialNativePredictablePoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance initialNativePredictablePoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance initialNativePredictablePoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance initialNativePredictablePoint_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "L"=>InitialTerminalLevel.level R F hF hFm
local notation "Root"=>InitialTerminalLevel.Root R
local notation "Mean"=>InitialNativeKernelFields.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Point"=>InitialNativeKernelFields.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

/-- The moving terminal is deterministic data; the actual current state
is measurable for the original predictable sigma algebra. -/
theorem mean_predictable (k:ℕ):
    @Measurable ((ℝ×(ℝ≥0×Ω))×History Root k) _
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _
      (fun z=>Mean k z.1.1 z.1.2.1 z.1.2.2 z.2):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hmap:Measurable (fun z:(ℝ×(ℝ≥0×Ω))×History Root k=>z.1.2):=measurable_fst.snd
  have hU:=S.first_predictable.measurable.comp hmap
  have hD:=(S.second_predictable.sub S.first_predictable).measurable.comp hmap
  apply (WithLp.measurable_toLp 2 (Fin (1+k)→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT:Measurable (fun p:History Root k=>targets L k p i):=
    (carrier L k).observations.target_measurable i
  have hx:Measurable (fun p:History Root k=>centers L k p i):=
    (carrier L k).observations.center_measurable i
  have hs:Measurable (fun p:History Root k=>stops L k p i):=
    ((carrier L k).observations.stop_measurable i).min
      ((L).terminal_measurable.comp (rootParameter_measurable k))
  have hq:Measurable (fun z:(ℝ×(ℝ≥0×Ω))×History Root k=>(z.1.2.1:ℝ)):=
    NNReal.continuous_coe.measurable.comp
      ((PredictableClock.time_measurable 𝓕).comp measurable_fst.snd)
  have harg:=((hT.comp measurable_snd).sub hq).prodMk (hx.comp measurable_snd)
  have hfirst:=functional_joint_measurable.comp (hU.prodMk harg)
  have hdiff:=functional_joint_measurable.comp (hD.prodMk harg)
  have hdamp:=measurable_fst.fst.mul (((hs.comp measurable_snd).sub hq).const_mul (-Λ)).exp
  convert! hfirst.add (hdamp.mul hdiff) using 1

attribute [local irreducible] InitialNativeKernelFields.mean InitialTerminalLevel.level

/-- Initial-strip Gaussian rows are jointly measurable in the root
terminal and the ORIGINAL predictable current sigma algebra. -/
theorem point_predictable (k:ℕ)(weighted:Bool)(θ:ℝ):
    @Measurable (((ℝ≥0×Ω)×((Icc (R).base (R).horizon)×History HeatCircle k))×HeatCircle) ℝ
      ((𝓕.predictable.prod inferInstance).prod inferInstance) _
      (fun z=>Point k weighted θ z.1.1.1 z.1.2.1 z.1.2.2 z.2 z.1.1.2):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hm:=mean_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h F hF hFm k
  have hm':Measurable (fun z:(ℝ≥0×Ω)×History Root k=>Mean k θ z.1.1 z.1.2 z.2):=
    hm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hl:=InitialTerminalFields.lift_measurable R k
  have hmap:Measurable
      (fun z:((ℝ≥0×Ω)×((Icc (R).base (R).horizon)×History HeatCircle k))×HeatCircle=>
      ((z.1.1,InitialTerminalFields.lift R z.1.2.1 k z.1.2.2),z.2)):=
    (measurable_fst.fst.prodMk (hl.comp measurable_fst.snd)).prodMk measurable_snd
  have hq:Measurable (fun z:ℝ≥0×Ω=>(z.1:ℝ)):=
    NNReal.continuous_coe.measurable.comp (PredictableClock.time_measurable 𝓕)
  cases weighted
  · have hh:=(ActualMeanKernel.rowPoint_variable_measurable L k _ _ hq hq
      (fun z:ℝ≥0×Ω=>Mean k θ z.1 z.2) hm').comp hmap
    simpa only [InitialNativeKernelFields.point,Bool.false_eq_true,if_false,
      Function.comp_def,Prod.fst,Prod.snd] using hh
  · have hh:=(ActualMeanKernel.weightedPoint_variable_measurable L k Λ _ _ hq hq
      (fun z:ℝ≥0×Ω=>Mean k θ z.1 z.2) hm').comp hmap
    simpa only [InitialNativeKernelFields.point,if_true,Function.comp_def,Prod.fst,Prod.snd] using hh

end SHE.InitialNativePredictablePoint
