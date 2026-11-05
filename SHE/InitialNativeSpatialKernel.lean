module
public import SHE.InitialNativeKernelFibre
public import SHE.InitialNativeKernelFields
public import SHE.SeparatedMeanBounds
public import SHE.WeightedMeanBounds
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
namespace SHE.InitialNativeSpatialKernel
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
local notation "Point"=>InitialNativeKernelFields.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
abbrev Param (k:ℕ):Type:=((Icc (R).base (R).horizon)×ℝ≥0)×((Fin k→ℝ)×Ω)

def field (k:ℕ)(weighted:Bool)(θ:ℝ)(z:Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=
  ((∫w:Fin k→HeatCircle,Point k weighted θ z.1.1.2 z.1.1.1
      (separated k (z.2.2,z.1.2.1,w)) z.2.1 z.1.2.2
    ∂Measure.pi (fun _=>haarAddCircle)):ℝ)
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem field_measurable (k:ℕ)(weighted:Bool)(θ:ℝ):Measurable (Field k weighted θ):=by
  let Y:=(Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle))×(Fin k→HeatCircle)
  have hh:Measurable (fun z:Y=>separated k (z.1.2.2,z.1.1.2.1,z.2)):=
    (separated_measurable k).comp (measurable_fst.snd.snd.prodMk
      (measurable_fst.fst.snd.fst.prodMk measurable_snd))
  have hm:=InitialNativeKernelFields.point_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k weighted θ
  have hmap:=((measurable_fst.fst.fst.snd.prodMk measurable_fst.fst.snd.snd).prodMk
    (measurable_fst.fst.fst.fst.prodMk hh)).prodMk measurable_fst.snd.fst
  have hi:=(hm.comp hmap).stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi)))
  convert! Complex.continuous_ofReal.measurable.comp hi.measurable using 1

local notation "BT" T:max=>InitialNativeKernelFibre.terminal Λ u₀ P haP h T
local notation "NB" T:max=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "MA"=>InitialNativeKernelFibre.actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem field_bound (hΛ:0≤Λ)(k:ℕ)(weighted:Bool)(θ:ℝ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):
    ∃B:ℝ,0≤B∧∀y x,‖Field k weighted θ (z,(y,x))‖≤B:=by
  let T:=z.1.1
  let q:=z.1.2
  let K:=(NB T) (θ,(embed u₀,0))
  cases weighted
  · obtain ⟨B,hB,hb⟩:=ActualMeanKernel.rowSpatial_uniform_bound K (X:=Unit) (T:ℝ) (fun _=>rfl) k q q z.2.1
    refine ⟨B,hB,fun y x=>?_⟩
    have heq:Field k false θ (z,(y,x))=ActualMeanKernel.rowSpatial K k q q
        (fun _:Unit=>MA k θ q T z.2.2) z.2.1 () y x:=by
      unfold field ActualMeanKernel.rowSpatial
      congr 1
      apply integral_congr_ae
      filter_upwards [] with w
      exact (InitialNativeKernelFibre.point_fibre 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
        k false θ q T (separated k (x,z.2.1,w)) y z.2.2).symm
    rw [heq]
    exact hb (fun _:Unit=>MA k θ q T z.2.2) () y x
  · obtain ⟨B,hB,hb⟩:=ActualMeanKernel.weightedSpatial_uniform_bound K (X:=Unit) (T:ℝ) (fun _=>rfl) k hΛ q q z.2.1
    refine ⟨B,hB,fun y x=>?_⟩
    have heq:Field k true θ (z,(y,x))=ActualMeanKernel.weightedSpatial K k Λ q q
        (fun _:Unit=>MA k θ q T z.2.2) z.2.1 () y x:=by
      unfold field ActualMeanKernel.weightedSpatial
      congr 1
      apply integral_congr_ae
      filter_upwards [] with w
      exact (InitialNativeKernelFibre.point_fibre 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
        k true θ q T (separated k (x,z.2.1,w)) y z.2.2).symm
    rw [heq]
    exact hb (fun _:Unit=>MA k θ q T z.2.2) () y x

end SHE.InitialNativeSpatialKernel
