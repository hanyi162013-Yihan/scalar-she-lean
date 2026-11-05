module
public import SHE.MovingNativePointTranslation
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
namespace SHE.MovingNativeSpatialTranslation
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

local notation "MA"=>MovingNativePointTranslation.absoluteMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "PointA"=>MovingNativePointTranslation.absolutePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Field"=>MovingNativeSpatialKernel.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

/-- The original-clock old-space average, retaining both native spatial coordinates. -/
def absoluteField (k:ℕ)(weighted:Bool)(θ:ℝ)(v s:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)(y x:HeatCircle):ℂ:=
  ((∫w:Fin k→HeatCircle,PointA k weighted θ v s (separated k (x,t,w)) y ω
    ∂Measure.pi (fun _=>haarAddCircle)):ℝ)
local notation "FieldA"=>absoluteField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

/-- Translating old times leaves their actual Haar spatial average unchanged. -/
theorem field_translation (k:ℕ)(weighted:Bool)(θ:ℝ)(v s:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)(y x:HeatCircle):
    FieldA k weighted θ v s (fun i=>t i+(v:ℝ)) ω y x=
      Field k weighted ((θ,((v,s),(t,ω))),(y,x)):=by
  unfold absoluteField MovingNativeSpatialKernel.field
  congr 1
  apply integral_congr_ae
  filter_upwards [] with w
  rw [←ControlledMeanSpatialShift.shift_separated]
  exact MovingNativePointTranslation.point_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm k weighted θ v s ω (separated k (x,t,w)) y

private theorem rowPoint_zero {R:ReferenceData}{X:Type}[MeasurableSpace X]{n:ℕ}
    (L:Level R X n)(k:ℕ)(q r:ℝ)(m:History X k→WordRecursion.State (n+k))(p:History X k)(y:HeatCircle):
    ActualMeanKernel.rowPoint L k q r m p y=ActualMeanKernel.weightedPoint L k 0 q r m p y:=by
  classical
  unfold ActualMeanKernel.rowPoint ActualMeanKernel.weightedPoint
  split_ifs
  · congr 1
    apply PiLp.ext
    intro i
    simp only [StopWeightedRows.weightedHeatRow,StopWeightedRows.diagonal_apply,
      StopWeightedRows.weights,neg_zero,zero_mul,Real.exp_zero,one_mul]
  · rfl

/-- Exact identification with the signed endpoint kernel used in the actual column energy theorem. -/
theorem endpoint_absolute (k:ℕ)(θ:ℝ)(v s:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)(y x:HeatCircle):
    MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP
      v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm k θ (v+s) (v+s) t (ω,(y,x))=
      FieldA k true θ v s t ω y x:=by
  rfl

/-- The complete original kernel is the difference of its true unweighted endpoints. -/
theorem common_absolute (k:ℕ)(v s:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)(y x:HeatCircle):
    MixedPastNativeKernelAverage.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
      v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm k (v+s) (v+s) t (ω,(y,x))=
      FieldA k false 1 v s t ω y x-FieldA k false 0 v s t ω y x:=by
  rw [MixedPastNativeKernelSemigroup.spatial_eq_endpoint_sub]
  have he(θ:ℝ):MixedPastNativeKernelSemigroup.endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
      v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm θ k (v+s) (v+s) t (ω,(y,x))=
      FieldA k false θ v s t ω y x:=by
    unfold MixedPastNativeKernelSemigroup.endpoint absoluteField ActualMeanKernel.weightedSpatial
    congr 1
    apply integral_congr_ae
    filter_upwards [] with w
    unfold MovingNativePointTranslation.absolutePoint
    simp only [Bool.false_eq_true,if_false]
    exact (rowPoint_zero _ _ _ _ _ _ _).symm
  rw [he 1,he 0]

end SHE.MovingNativeSpatialTranslation

