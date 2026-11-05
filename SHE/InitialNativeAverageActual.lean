module
public import SHE.InitialNativeColumnActual
public import SHE.InitialNativeOldCube
public import SHE.InitialNativeColumnAverages
public import SHE.MixedPastNativeCompleteColumns
public import SHE.InitialNativeColumns
public import SHE.MixedPastNativeKernelSemigroup
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedEndpointFields
public import SHE.NativeKernelCongruence
public import SHE.MixedNativePairInitial
public import SHE.ControlledScalarReference
public import SHE.WordRootState
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
namespace SHE.InitialNativeAverageActual
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
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "BT" T:max=>InitialNativeKernelFibre.terminal Λ u₀ P haP h T
local notation "ZZ" T:max=>ControlledScalarReference.observations (BT T)
local notation "LeftA" T:max=>MixedPastNativeCompleteColumns.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "RightA" T:max=>MixedPastNativeCompleteColumns.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Left"=>InitialNativeColumnAverages.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Right"=>InitialNativeColumnAverages.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

/-- The whole initial-strip channel field is a jointly Borel version of the actual original averages, on one sample event. -/
theorem average_initial_ae (hΛ:0≤Λ):
    ∀ᵐω∂μ,∀T:Icc (R).base (R).horizon,∀k:ℕ,∀q:ℝ≥0,
      ∀mass ρ:ℝ,∀hmass:1≤mass,∀hρ:0≤ρ,
      (LeftA T) k q hmass hρ ω=Left hΛ k hmass hρ ((T,q),ω) ∧
      (RightA T) k q hmass hρ ω=Right hΛ k hmass hρ ((T,q),ω):=by
  filter_upwards [InitialNativeColumnActual.columns_initial_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ] with ω hω
  intro T k q mass ρ hmass hρ
  have heA:=InitialNativeOldCube.additive_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm T k q ω hmass hρ
  have heB:=InitialNativeOldCube.base_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm T k q ω hmass hρ
  have heS:=InitialNativeOldCube.signed_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm T k q ω hmass hρ
  let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))
  have hhA:=integral_congr_ae (μ:=old) (ae_of_all _ (fun t=>(hω T k q t mass ρ hmass hρ).1))
  have hhB:=integral_congr_ae (μ:=old) (ae_of_all _ (fun t=>(hω T k q t mass ρ hmass hρ).2.1))
  have hhS:=integral_congr_ae (μ:=old) (ae_of_all _ (fun t=>(hω T k q t mass ρ hmass hρ).2.2))
  constructor
  · unfold MixedPastNativeCompleteColumns.left InitialNativeColumnAverages.left
    convert! heA.trans hhA using 1
  · unfold MixedPastNativeCompleteColumns.right InitialNativeColumnAverages.right
    convert! congrArg₂ (fun a b:NativeKernelHaarColumns.Space=>a+b) (heB.trans hhB) (heS.trans hhS) using 1

end SHE.InitialNativeAverageActual
