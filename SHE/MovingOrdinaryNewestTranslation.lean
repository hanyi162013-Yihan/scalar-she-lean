module
public import SHE.NativeHessianTimeShift
public import SHE.MovingOrdinaryNewestFields
public import SHE.MovingNativePointTranslation
public import SHE.ShiftedOldTimeMeasure
public import SHE.MixedPastNewestOriginalMass
public import SHE.MixedPastNewestOrdinaryError
public import SHE.ControlledThetaBackwardFields
public import SHE.PhysicalWordErrorFields
public import SHE.MovingNativeKernelFields
public import SHE.MovingNativeFields
public import SHE.MixedPastNativeTimeFields
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingOrdinaryNewestTranslation
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
variable (h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Past" v:max ω:max=>(embed (S.first v ω),embed (S.second v ω-S.first v ω))

local notation "Mean"=>MovingNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Error"=>MixedPastNewestOrdinaryError.errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v:max=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v:max=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v:max=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "MA"=>MovingNativePointTranslation.absoluteMean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Point"=>MovingOrdinaryNewestFields.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Primitive"=>MovingOrdinaryNewestFields.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "CA" v:max=>MixedPastNewestOriginalMass.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add
    (ZT v) (HT v) (HS v) F hF hFm
local notation "PA" v:max=>MixedPastNewestOriginalMass.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add
    (ZT v) (HT v) (HS v) F hF hFm

theorem second_translation(k:ℕ)(v s:ℝ≥0)(ω:Ω)(p:History HeatCircle k)(y:HeatCircle):
    WordRecursion.directionalSecond
      (gaussianAverage (WordRecursion.covariance (ControlledReferenceLevel.referenceData
        P P.coefficient haP Λ 0 v (v+h) le_self_add (Past v ω)).reference
        ((carrier (Abs v (0,Past v ω)) k).observations.observations (ShiftedWordGeometry.shift (v:ℝ) k p))
        (v+s) ((carrier (Abs v (0,Past v ω)) k).terminal (ShiftedWordGeometry.shift (v:ℝ) k p)))
        (UncutSmoothWords.test (Abs v (0,Past v ω)) k (ShiftedWordGeometry.shift (v:ℝ) k p)))
      (MA k 0 v s ω (ShiftedWordGeometry.shift (v:ℝ) k p))
      (heatRow ((carrier (Abs v (0,Past v ω)) k).observations.observations
        (ShiftedWordGeometry.shift (v:ℝ) k p)) (v+s) y)=
    WordRecursion.directionalSecond
      (gaussianAverage (WordRecursion.covariance
        (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 h bot_le (Past v ω)).reference
        ((carrier (Base (0,Past v ω)) k).observations.observations p)
        s ((carrier (Base (0,Past v ω)) k).terminal p))
        (UncutSmoothWords.test (Base (0,Past v ω)) k p)) (Mean k 0 v s ω p)
      (heatRow ((carrier Zero k).observations.observations p) s y):=by
  have hh:=ShiftedWordCalculus.directionalSecond_shift (Base (0,Past v ω)) (Abs v (0,Past v ω)) (v:ℝ)
    (ControlledWordTimeShift.base_shift P P.coefficient haP Λ h v (0,Past v ω))
    (ControlledWordTimeShift.terminal_shift P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,Past v ω))
    (ControlledWordTimeShift.observations_shift P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,Past v ω))
    (ControlledWordTimeShift.reference_shift P P.coefficient haP Λ h v (0,Past v ω)) rfl (fun _=>rfl)
    k (s:ℝ) p (MA k 0 v s ω (ShiftedWordGeometry.shift (v:ℝ) k p)) y
  rw [MovingNativePointTranslation.mean_translation
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm] at hh
  have ho:=ControlledReferenceThetaGeometry.carrier_observations_eq
    P P.coefficient haP Λ 0 h bot_le Z htarget hstop F hF hFm (0,Past v ω) (0,(0,0)) k p
  rw [←ho,MovingNativePointTranslation.mean_translation
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm]
  convert! hh using 1 <;> simp only [NNReal.coe_add,add_comm]

end SHE.MovingOrdinaryNewestTranslation
