module
public import SHE.MovingNativeColumnTranslation
public import SHE.MovingNativeColumnAverages
public import SHE.MixedPastNativeCompleteColumns
public import SHE.ShiftedOldTimeMeasure
public import SHE.MovingNativeColumns
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedEndpointFields
public import SHE.NativeKernelCongruence
public import SHE.ShiftedPhysicalArrays
public import SHE.NativeRowTimeShift
public import SHE.MovingNativeSpatialKernel
public import SHE.ControlledMeanSpatialShift
public import SHE.MixedPastNativeKernelSemigroup

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingNativeAverageTranslation
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativePointTranslation_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativePointTranslation_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativePointTranslation_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativePointTranslation_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativePointTranslation_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativePointTranslation_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance movingNativePointTranslation_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativePointTranslation_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativePointTranslation_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativePointTranslation_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Past" v:max ω:max=>(embed (S.first v ω),embed (S.second v ω-S.first v ω))

local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v:max=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v:max=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v:max=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "Mean"=>MovingNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

local notation "LeftA" v:max=>MixedPastNativeCompleteColumns.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "RightA" v:max=>MixedPastNativeCompleteColumns.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "Left"=>MovingNativeColumnAverages.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Right"=>MovingNativeColumnAverages.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

/-- Exact original old-time averaging becomes a fixed relative-cube average, before any norm. -/
theorem left_translation (hΛ:0≤Λ)(k:ℕ)(v s:ℝ≥0)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    (LeftA v) k (v+s) hmass hρ ω=Left hΛ k hmass hρ ((v,s),ω):=by
  unfold MixedPastNativeCompleteColumns.left MovingNativeColumnAverages.left
  simp only [NNReal.coe_add]
  rw [←ShiftedOldTimeMeasure.integral_translation (v:ℝ) (h:ℝ) k]
  apply integral_congr_ae
  filter_upwards [] with t
  exact MovingNativeColumnTranslation.additive_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm hΛ k v s t ω hmass hρ

/-- Both common and signed channels retain their separate original old-time integrals. -/
theorem right_translation (hΛ:0≤Λ)(k:ℕ)(v s:ℝ≥0)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    (RightA v) k (v+s) hmass hρ ω=Right hΛ k hmass hρ ((v,s),ω):=by
  unfold MixedPastNativeCompleteColumns.right MovingNativeColumnAverages.right
  simp only [NNReal.coe_add]
  rw [←ShiftedOldTimeMeasure.integral_translation (v:ℝ) (h:ℝ) k]
  rw [←ShiftedOldTimeMeasure.integral_translation (v:ℝ) (h:ℝ) k]
  congr 1
  · apply integral_congr_ae
    filter_upwards [] with t
    exact MovingNativeColumnTranslation.base_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm hΛ k v s t ω hmass hρ
  · apply integral_congr_ae
    filter_upwards [] with t
    exact MovingNativeColumnTranslation.signed_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm k v s t ω hmass hρ

end SHE.MovingNativeAverageTranslation
