module
public import SHE.MovingOrdinaryNewestTranslation
public import SHE.MovingClockEnergy
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
namespace SHE.MovingOrdinaryNewestCurrent
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

/-- Literal original current-error insertion equals the moving
relative Hessian field before any current/history averaging. -/
theorem current_translation(k:ℕ)(v s:ℝ≥0)(ω:Ω)(p:History HeatCircle k):
    (CA v) k Error ((v+s:ℝ≥0),(ω,ShiftedWordGeometry.shift (v:ℝ) k p))=
      ∫y,Point k v s p y ω ∂haarAddCircle:=by
  have hterm:=ShiftedWordGeometry.terminal_shift Zero (Abs v (0,(0,0))) (v:ℝ)
    (ControlledWordTimeShift.base_shift P P.coefficient haP Λ h v (0,(0,0)))
    (ControlledWordTimeShift.terminal_shift P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,(0,0))) k p
  have hguard:((v+s:ℝ≥0):ℝ)<(carrier (Abs v (0,(0,0))) k).terminal
      (ShiftedWordGeometry.shift (v:ℝ) k p)↔(s:ℝ)<(carrier Zero k).terminal p:=by
    rw [hterm,NNReal.coe_add]
    constructor <;> intro hh <;> linarith
  unfold MixedPastNewestOriginalMass.current MixedPastNewestTimeFields.active
  simp only [Real.toNNReal_coe]
  by_cases hs:(s:ℝ)<(carrier Zero k).terminal p
  · simp only [if_pos (hguard.mpr hs),MovingOrdinaryNewestFields.point,if_pos hs]
    unfold MixedPastNewestError.value
    dsimp only
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    have hh:=MovingOrdinaryNewestTranslation.second_translation
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k v s ω p y
    have hrt:=ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient haP Λ 0 h bot_le Z htarget hstop F hF hFm (0,Past v ω) (0,(0,0)) k p
    have hqs:(s:ℝ)≤(carrier (Base (0,Past v ω)) k).terminal p:=by rw [hrt];exact hs.le
    simp only [ActualMeanKernel.cappedAverage,min_eq_left hqs]
    convert! congrArg (fun a:ℝ=>Error ((v+s,ω),y)*a) hh using 1 <;>
      simp only [MixedPastJointData.pastU,MixedPastJointData.pastD,NNReal.coe_add,
        WordRecursion.directionalSecond,WordRecursion.hessian,GaussianTaylor.hessian]
  · have hnot:¬((v+s:ℝ≥0):ℝ)<(carrier (Abs v (0,(0,0))) k).terminal
        (ShiftedWordGeometry.shift (v:ℝ) k p):=fun hh=>hs (hguard.mp hh)
    simp only [if_neg hnot,MovingOrdinaryNewestFields.point,if_neg hs,integral_zero]

/-- The original physical [v,v+h] current integral becomes the fixed
relative [0,h] integral, without a probability normalization factor. -/
theorem primitive_translation(k:ℕ)(v:ℝ≥0)(ω:Ω)(p:History HeatCircle k):
    (PA v) k Error (ω,ShiftedWordGeometry.shift (v:ℝ) k p)=Primitive k ((v,ω),p):=by
  unfold MixedPastNewestOriginalMass.primitive MovingOrdinaryNewestFields.primitive
  have hp:=MovingClockEnergy.translation (v:ℝ) (h:ℝ)
  have he:=hp.integral_comp (Homeomorph.addRight (v:ℝ)).isClosedEmbedding.measurableEmbedding
    (fun q:ℝ=>(CA v) k Error (q,(ω,ShiftedWordGeometry.shift (v:ℝ) k p)))
  simp only [NNReal.coe_add] at he ⊢
  rw [←he]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hs0:(s.toNNReal:ℝ)=s:=Real.coe_toNNReal s hs.1.le
  simpa only [NNReal.coe_add,hs0,add_comm,MeasurableEquiv.coe_addRight] using
    current_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      k v s.toNNReal ω p

/-- The genuine original retained-root error average is exactly the
Borel relative-cube average, with every old measure retained. -/
theorem average_translation(k:ℕ)(v:ℝ≥0)(ω:Ω)(x:HeatCircle):
    RootSectionAverage.average
      (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v (v+h) le_self_add (0,0)) k
      ((PA v) k Error) (ω,x)=
      MovingOrdinaryNewestFields.average
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k ((v,ω),x):=by
  unfold RootSectionAverage.average MovingOrdinaryNewestFields.average
  simp only [ControlledReferenceLevel.referenceData,NNReal.coe_add]
  rw [←ShiftedOldTimeMeasure.integral_translation (v:ℝ) (h:ℝ) k]
  apply integral_congr_ae
  filter_upwards [] with t
  apply integral_congr_ae
  filter_upwards [] with w
  rw [←ControlledMeanSpatialShift.shift_separated]
  exact primitive_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k v ω
    (separated k (x,t,w))

end SHE.MovingOrdinaryNewestCurrent
