module
public import SHE.MovingNativeKernelFields
public import SHE.ShiftedPhysicalArrays
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingNativePointTranslation
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

abbrev absoluteMean (k:ℕ)(θ:ℝ)(v s:ℝ≥0)(ω:Ω):History HeatCircle k→WordRecursion.State (1+k):=
  MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm k θ (v+s) ω
local notation "MA"=>absoluteMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

/-- The true covered stops, full targets, and literal original current
are translated together; no active-domain mean replacement is needed. -/
theorem mean_translation (k:ℕ)(θ:ℝ)(v s:ℝ≥0)(ω:Ω)(p:History HeatCircle k):
    MA k θ v s ω (ShiftedWordGeometry.shift (v:ℝ) k p)=Mean k θ v s ω p:=by
  have hb:=ControlledWordTimeShift.base_shift P P.coefficient haP Λ h v (0,(0,0))
  have hT:=ControlledWordTimeShift.terminal_shift P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,(0,0))
  have hZ:=ControlledWordTimeShift.observations_shift P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,(0,0))
  have hs:=ShiftedPhysicalArrays.stops_shift Zero (Abs v (0,(0,0))) (v:ℝ) hb hT hZ k p
  have ht:=ShiftedPhysicalArrays.targets_shift Zero (Abs v (0,(0,0))) (v:ℝ) hb hT hZ k p
  have hc:=ShiftedPhysicalArrays.centers_shift Zero (Abs v (0,(0,0))) (v:ℝ) hb hT hZ k p
  unfold absoluteMean MixedPastLiteralPoint.meanField MixedPastJointData.mean MixedNativePastThetaCentering.current
    MovingNativeKernelFields.mean
  apply PiLp.ext
  intro i
  simp only [WithLp.ofLp_toLp,sub_add_cancel]
  rw [hs,ht,hc]
  simp only [NNReal.coe_add]
  congr 2 <;> ring


/-- Literal original-clock point field before the physical moving-window guard. -/
def absolutePoint (k:ℕ)(weighted:Bool)(θ:ℝ)(v s:ℝ≥0)(p:History HeatCircle k)(y:HeatCircle)(ω:Ω):ℝ:=
  if weighted then ActualMeanKernel.weightedPoint (Abs v (θ,Past v ω)) k Λ (v+s) (v+s) (MA k θ v s ω) p y
  else ActualMeanKernel.rowPoint (Abs v (θ,Past v ω)) k (v+s) (v+s) (MA k θ v s ω) p y
local notation "PA"=>absolutePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem point_translation (k:ℕ)(weighted:Bool)(θ:ℝ)(v s:ℝ≥0)(ω:Ω)(p:History HeatCircle k)(y:HeatCircle):
    PA k weighted θ v s (ShiftedWordGeometry.shift (v:ℝ) k p) y ω=
      MovingNativeKernelFields.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm k weighted θ v s p y ω:=by
  have hq:((v+s:ℝ≥0):ℝ)=(s:ℝ)+(v:ℝ):=by rw [NNReal.coe_add,add_comm]
  have hcomm:(v:ℝ)+(s:ℝ)=(s:ℝ)+(v:ℝ):=add_comm _ _
  cases weighted
  · have hh:=ShiftedWordCalculus.rowPoint_shift (Base (θ,Past v ω)) (Abs v (θ,Past v ω)) (v:ℝ)
      (ControlledWordTimeShift.base_shift P P.coefficient haP Λ h v (θ,Past v ω))
      (ControlledWordTimeShift.terminal_shift P P.coefficient haP Λ h Z htarget hstop F hF hFm v (θ,Past v ω))
      (ControlledWordTimeShift.observations_shift P P.coefficient haP Λ h Z htarget hstop F hF hFm v (θ,Past v ω))
      (ControlledWordTimeShift.reference_shift P P.coefficient haP Λ h v (θ,Past v ω)) rfl (fun _=>rfl)
      k (s:ℝ) (s:ℝ) (MA k θ v s ω) p y
    simpa only [absolutePoint,MovingNativeKernelFields.point,Bool.false_eq_true,if_false,hq,NNReal.coe_add,hcomm,
      mean_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm] using hh
  · have hh:=ControlledWordTimeShift.weightedPoint_translation P P.coefficient haP Λ h Z htarget hstop F hF hFm
      v (θ,Past v ω) k (s:ℝ) (s:ℝ) (MA k θ v s ω) p y
    simpa only [absolutePoint,MovingNativeKernelFields.point,if_true,hq,NNReal.coe_add,hcomm,
      mean_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm] using hh

end SHE.MovingNativePointTranslation
