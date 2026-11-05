module
public import SHE.InitialNativePointActual
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
namespace SHE.InitialNativeColumnActual
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
local notation "Field"=>InitialNativeSpatialKernel.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Common"=>InitialNativeColumns.common 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Endpoint"=>InitialNativeColumns.endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "SpatialA" T:max=>MixedPastNativeKernelAverage.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "EndpointA" T:max=>MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "EndZeroA" T:max=>MixedPastNativeKernelSemigroup.endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

private theorem rowPoint_zero {R0:ReferenceData}{X:Type}[MeasurableSpace X]{n:ℕ}
    (L0:Level R0 X n)(k:ℕ)(q r:ℝ)(m:History X k→WordRecursion.State (n+k))(p:History X k)(y:HeatCircle):
    ActualMeanKernel.rowPoint L0 k q r m p y=ActualMeanKernel.weightedPoint L0 k 0 q r m p y:=by
  classical
  unfold ActualMeanKernel.rowPoint ActualMeanKernel.weightedPoint
  split_ifs
  · congr 1
    apply PiLp.ext
    intro i
    simp only [StopWeightedRows.weightedHeatRow,StopWeightedRows.diagonal_apply,
      StopWeightedRows.weights,neg_zero,zero_mul,Real.exp_zero,one_mul]
  · rfl

/-- A single initial sample event identifies both complete kernels for every root terminal and old time. -/
theorem fields_initial_ae:
    ∀ᵐω∂μ,∀T:Icc (R).base (R).horizon,∀k:ℕ,∀q:ℝ≥0,∀t:Fin k→ℝ,∀y x:HeatCircle,
      (SpatialA T) k q q t (ω,(y,x))=Common k (((T,q),(t,ω)),(y,x)) ∧
      (EndpointA T) k 1 q q t (ω,(y,x))=Endpoint k (((T,q),(t,ω)),(y,x)):=by
  filter_upwards [InitialNativePointActual.point_initial_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm] with ω hω
  intro T k q t y x
  have he(θ:ℝ):(EndZeroA T) θ k q q t (ω,(y,x))=Field k false θ (((T,q),(t,ω)),(y,x)):=by
    unfold MixedPastNativeKernelSemigroup.endpoint ActualMeanKernel.weightedSpatial InitialNativeSpatialKernel.field
    congr 1
    apply integral_congr_ae
    filter_upwards [] with w
    have hp:=hω T k false θ q (separated k (x,t,w)) y
    simp only [InitialNativePointActual.originalPoint,Bool.false_eq_true,if_false,
      MixedPastNativeConsistentPoint.point] at hp
    rw [rowPoint_zero] at hp
    exact hp
  constructor
  · rw [MixedPastNativeKernelSemigroup.spatial_eq_endpoint_sub,he 1,he 0]
    rfl
  · unfold MixedPastKernelFields.spatial ActualMeanKernel.weightedSpatial InitialNativeColumns.endpoint InitialNativeSpatialKernel.field
    congr 1
    apply integral_congr_ae
    filter_upwards [] with w
    have hp:=hω T k true 1 q (separated k (x,t,w)) y
    simpa only [InitialNativePointActual.originalPoint,if_true,MixedPastLiteralPoint.point] using hp

local notation "AddA" T:max=>MixedPastNativeOldTimeEnergy.additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "BaseA" T:max=>MixedPastNativeOldTimeEnergy.base 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "SignedA" T:max=>MixedPastSignedEndpointFields.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Add"=>InitialNativeColumns.additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "BaseCols"=>InitialNativeColumns.base 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Signed"=>InitialNativeColumns.signed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem columns_initial_ae (hΛ:0≤Λ):
    ∀ᵐω∂μ,∀T:Icc (R).base (R).horizon,∀k:ℕ,∀q:ℝ≥0,∀t:Fin k→ℝ,
      ∀mass ρ:ℝ,∀hmass:1≤mass,∀hρ:0≤ρ,
      (AddA T) k q hmass hρ (t,ω)=Add hΛ k hmass hρ ((T,q),(t,ω)) ∧
      (BaseA T) k q hmass hρ (t,ω)=BaseCols hΛ k hmass hρ ((T,q),(t,ω)) ∧
      (SignedA T) k q hmass hρ (t,ω)=Signed k hmass hρ ((T,q),(t,ω)):=by
  filter_upwards [fields_initial_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm] with ω hω
  intro T k q t mass ρ hmass hρ
  have he:=NativeKernelCongruence.operator_congr ((SpatialA T) k q q t) (Common k) ω ((T,q),(t,ω))
    (fun y x=>(hω T k q t y x).1)
  have hf:=NativeKernelCongruence.operator_congr ((EndpointA T) k 1 q q t) (Endpoint k) ω ((T,q),(t,ω))
    (fun y x=>(hω T k q t y x).2)
  refine ⟨?_,?_,?_⟩
  · apply lp.ext
    funext j
    simp only [MixedPastNativeOldTimeEnergy.additive,MixedPastNativeHaarFields.columns_apply,
      InitialNativeColumns.additive,NativeKernelHaarColumns.columns_apply,NativeKernelHaarColumns.column,he]
  · apply lp.ext
    funext j
    simp only [MixedPastNativeOldTimeEnergy.base,MixedPastNativeHaarFields.columns_apply,
      InitialNativeColumns.base,NativeKernelHaarColumns.columns_apply,NativeKernelHaarColumns.column,
      InitialNativeColumns.coefficientU,he]
  · rw [MixedPastSignedEndpointFields.raw_section]
    apply lp.ext
    funext j
    simp only [InitialNativeColumns.signed,SignedKernelColumns.rawColumns_apply,
      InitialNativeColumns.coefficientU,InitialNativeColumns.coefficientV,hf]

end SHE.InitialNativeColumnActual
