module
public import SHE.InitialTerminalFields
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
namespace SHE.InitialNativeKernelFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativeKernelFields_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativeKernelFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativeKernelFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativeKernelFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativeKernelFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativeKernelFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance movingNativeKernelFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativeKernelFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativeKernelFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativeKernelFields_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
abbrev referenceData:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 h bot_le (embed u₀,0)
local notation "R"=>referenceData Λ u₀ P haP h
local notation "L"=>InitialTerminalLevel.level R F hF hFm
local notation "Root"=>InitialTerminalLevel.Root R

/-- The actual current, at the variable root terminal and its original covered native stops. -/
def mean (k:ℕ)(θ:ℝ)(q:ℝ≥0)(ω:Ω)(p:History Root k):WordRecursion.State (1+k):=
  WithLp.toLp 2 (fun i=>functional (targets L k p i-(q:ℝ)) (centers L k p i) (S.first q ω)+
    θ*Real.exp (-Λ*(stops L k p i-(q:ℝ)))*
      functional (targets L k p i-(q:ℝ)) (centers L k p i) (S.second q ω-S.first q ω))
local notation "Mean"=>mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem mean_measurable (k:ℕ):Measurable (fun z:(ℝ×(ℝ≥0×Ω))×History Root k=>
    Mean k z.1.1 z.1.2.1 z.1.2.2 z.2):=by
  have hmap:Measurable (fun z:(ℝ×(ℝ≥0×Ω))×History Root k=>(z.1.2.1,z.1.2.2)):=measurable_fst.snd
  have hU:=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable.comp hmap
  have hD:=((S.second_predictable.sub S.first_predictable).mono (predictable_le_product 𝓕)).measurable.comp hmap
  apply (WithLp.measurable_toLp 2 (Fin (1+k)→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT:Measurable (fun p:History Root k=>targets L k p i):=(carrier L k).observations.target_measurable i
  have hx:Measurable (fun p:History Root k=>centers L k p i):=(carrier L k).observations.center_measurable i
  have hs:Measurable (fun p:History Root k=>stops L k p i):=
    ((carrier L k).observations.stop_measurable i).min
      ((L).terminal_measurable.comp (rootParameter_measurable k))
  have hq:Measurable (fun z:(ℝ×(ℝ≥0×Ω))×History Root k=>(z.1.2.1:ℝ)):=
    measurable_subtype_coe.comp measurable_fst.snd.fst
  have harg:=((hT.comp measurable_snd).sub hq).prodMk (hx.comp measurable_snd)
  have hfirst:=functional_joint_measurable.comp (hU.prodMk harg)
  have hdiff:=functional_joint_measurable.comp (hD.prodMk harg)
  have hdamp:=measurable_fst.fst.mul (((hs.comp measurable_snd).sub hq).const_mul (-Λ)).exp
  convert! hfirst.add (hdamp.mul hdiff) using 1

/-- A fixed deterministic initial reference is used; the root terminal moves inside its horizon. -/
def point (k:ℕ)(weighted:Bool)(θ:ℝ)(q:ℝ≥0)(T:Icc (R).base (R).horizon)
    (p:History HeatCircle k)(y:HeatCircle)(ω:Ω):ℝ:=
  let a:=InitialTerminalFields.lift R T k p
  if weighted then ActualMeanKernel.weightedPoint L k Λ q q (Mean k θ q ω) a y
  else ActualMeanKernel.rowPoint L k q q (Mean k θ q ω) a y
local notation "Point"=>point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

attribute [local irreducible] mean InitialTerminalLevel.level

theorem point_measurable (k:ℕ)(weighted:Bool)(θ:ℝ):Measurable
    (fun z:((ℝ≥0×Ω)×((Icc (R).base (R).horizon)×History HeatCircle k))×HeatCircle=>
      Point k weighted θ z.1.1.1 z.1.2.1 z.1.2.2 z.2 z.1.1.2):=by
  have hm:=mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k
  have hm':Measurable (fun z:(ℝ≥0×Ω)×History Root k=>Mean k θ z.1.1 z.1.2 z.2):=
    hm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hl:=InitialTerminalFields.lift_measurable R k
  have hmap:Measurable (fun z:((ℝ≥0×Ω)×((Icc (R).base (R).horizon)×History HeatCircle k))×HeatCircle=>
      ((z.1.1,InitialTerminalFields.lift R z.1.2.1 k z.1.2.2),z.2)):=
    (measurable_fst.fst.prodMk (hl.comp measurable_fst.snd)).prodMk measurable_snd
  have hq:Measurable (fun z:ℝ≥0×Ω=>(z.1:ℝ)):=measurable_subtype_coe.comp measurable_fst
  cases weighted
  · have hh:=(ActualMeanKernel.rowPoint_variable_measurable L k _ _ hq hq
      (fun z:ℝ≥0×Ω=>Mean k θ z.1 z.2) hm').comp hmap
    simpa only [point,Bool.false_eq_true,if_false,Function.comp_def,Prod.fst,Prod.snd] using hh
  · have hh:=(ActualMeanKernel.weightedPoint_variable_measurable L k Λ _ _ hq hq
      (fun z:ℝ≥0×Ω=>Mean k θ z.1 z.2) hm').comp hmap
    simpa only [point,if_true,Function.comp_def,Prod.fst,Prod.snd] using hh

abbrev Param (k:ℕ):Type:=((Icc (R).base (R).horizon)×ℝ≥0)×((Fin k→ℝ)×Ω)

end SHE.InitialNativeKernelFields
