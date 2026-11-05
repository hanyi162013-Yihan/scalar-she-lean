module
public import SHE.InitialOrdinaryNewestFibre
public import SHE.InitialOrdinaryNewestIntegration
public import SHE.RootSectionAverage
public import SHE.InitialOrdinaryNewestFields
public import SHE.InitialNativeKernelFibre
public import SHE.MixedNativePairInitial
public import SHE.MixedPastNewestOriginalMass
public import SHE.PhysicalWordErrorFields
public import SHE.MixedPastNewestOrdinaryError
public import SHE.InitialNativeKernelFields
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
namespace SHE.InitialOrdinaryNewestActual
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
attribute [local irreducible] GaussianConvolution.gaussianAverage ActualMeanKernel.cappedAverage
  GaussianTaylor.hessian WordRecursion.hessian UncutSmoothWords.test
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
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "L"=>InitialTerminalLevel.level R F hF hFm
local notation "Root"=>InitialTerminalLevel.Root R

local notation "Mean"=>InitialNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Error"=>MixedPastNewestOrdinaryError.errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "BT" T:max=>InitialNativeKernelFibre.terminal Λ u₀ P haP h T
local notation "NB" T:max=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "K" T:max=>(NB T) (0,(embed u₀,0))
local notation "Lift" T:max=>InitialTerminalFields.lift R T
local notation "MA"=>InitialNativeKernelFibre.actualMean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Point"=>InitialOrdinaryNewestFields.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "CA" T:max=>MixedPastNewestOriginalMass.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "PA" T:max=>MixedPastNewestOriginalMass.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

local notation "Primitive"=>InitialOrdinaryNewestFields.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

/-- The one original initial event works for every actual initial
terminal and history before the current integral is taken. -/
theorem primitive_all_parameters_ae:
    ∀ᵐω∂μ,∀T:Icc (R).base (R).horizon,∀k:ℕ,∀p:History HeatCircle k,
      (PA T) k Error (ω,p)=Primitive k ((T,ω),p):=by
  filter_upwards [InitialOrdinaryNewestFibre.current_all_parameters_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm] with ω hω
  intro T k p
  have hTh:(T:ℝ)≤(h:ℝ):=T.2.2
  unfold MixedPastNewestOriginalMass.primitive InitialOrdinaryNewestFields.primitive
  dsimp only [Prod.fst,Prod.snd]
  rw [InitialOrdinaryNewestIntegration.current_restrict (h:=(h:ℝ)) (T:=(T:ℝ)) hTh]
  simp only [NNReal.coe_zero,InitialNativeKernelFibre.terminal,NNReal.coe_mk]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
  have hqn:(q.toNNReal:ℝ)=q:=Real.coe_toNNReal q hq.1.le
  simpa only [hqn] using hω T k q.toNNReal p

/-- Original initial old-node restrictions are preserved while the
chosen Borel version uses a fixed cube and variable-terminal indicator. -/
theorem average_all_parameters_ae:
    ∀ᵐω∂μ,∀T:Icc (R).base (R).horizon,∀k:ℕ,∀x:HeatCircle,
      RootSectionAverage.average
        (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 (BT T) bot_le (0,0)) k
        ((PA T) k Error) (ω,x)=
      InitialOrdinaryNewestFields.average
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k ((T,ω),x):=by
  filter_upwards [primitive_all_parameters_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm] with ω hω
  intro T k x
  have hTh:(T:ℝ)≤(h:ℝ):=T.2.2
  unfold RootSectionAverage.average InitialOrdinaryNewestFields.average
  dsimp only [Prod.fst,Prod.snd]
  rw [InitialOrdinaryNewestIntegration.old_cube_restrict (h:=(h:ℝ)) (T:=(T:ℝ)) hTh]
  simp only [ControlledReferenceLevel.referenceData,NNReal.coe_zero,InitialNativeKernelFibre.terminal,NNReal.coe_mk]
  apply integral_congr_ae
  filter_upwards [] with t
  apply integral_congr_ae
  filter_upwards [] with w
  exact hω T k (separated k (x,t,w))

end SHE.InitialOrdinaryNewestActual
