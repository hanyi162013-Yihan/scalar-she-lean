module
public import SHE.MovingNativeKernelFields
public import SHE.SeparatedMeanBounds
public import SHE.WeightedMeanBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
namespace SHE.MovingNativeSpatialKernel
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativeSpatialKernel_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativeSpatialKernel_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativeSpatialKernel_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativeSpatialKernel_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativeSpatialKernel_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativeSpatialKernel_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance movingNativeSpatialKernel_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativeSpatialKernel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativeSpatialKernel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativeSpatialKernel_nativeSecond:SecondCountableTopology CircleL2:=
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
local notation "Point"=>MovingNativeKernelFields.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
abbrev Param (k:ℕ):Type:=ℝ×((ℝ≥0×ℝ≥0)×((Fin k→ℝ)×Ω))

/-- Literal old-space kernel with a moving physical past, relative
current time, reference inputs, old times, and retained native output. -/
def field (k:ℕ)(weighted:Bool)(z:Param (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=
  ((∫w:Fin k→HeatCircle,Point k weighted z.1.1 z.1.2.1.1 z.1.2.1.2
      (separated k (z.2.2,z.1.2.2.1,w)) z.2.1 z.1.2.2.2
    ∂Measure.pi (fun _=>haarAddCircle)):ℝ)
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem field_measurable (k:ℕ)(weighted:Bool):Measurable (Field k weighted):=by
  let Y:=(Param (Ω:=Ω) k×(HeatCircle×HeatCircle))×(Fin k→HeatCircle)
  have hh:Measurable (fun z:Y=>separated k (z.1.2.2,z.1.1.2.2.1,z.2)):=
    (separated_measurable k).comp (measurable_fst.snd.snd.prodMk
      (measurable_fst.fst.snd.snd.fst.prodMk measurable_snd))
  have hp:Measurable (fun z:Y=>(z.1.1.1,(z.1.1.2.1,z.1.1.2.2.2))):=
    measurable_fst.fst.fst.prodMk
      (measurable_fst.fst.snd.fst.prodMk measurable_fst.fst.snd.snd.snd)
  have hmap:= (hp.prodMk hh).prodMk measurable_fst.snd.fst
  have he:=(MovingNativeKernelFields.point_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k weighted).comp hmap
  have hi:=he.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi)))
  convert! Complex.continuous_ofReal.measurable.comp hi.measurable using 1

theorem field_bound (hΛ:0≤Λ)(k:ℕ)(weighted:Bool)(z:Param (Ω:=Ω) k):
    ∃B:ℝ,0≤B ∧ ∀y x,‖Field k weighted (z,(y,x))‖≤B:=by
  let L:=Base (z.1,Past z.2.1.1 z.2.2.2)
  let m:=Mean k z.1 z.2.1.1 z.2.1.2 z.2.2.2
  cases weighted
  · obtain ⟨B,hB,hb⟩:=ActualMeanKernel.rowSpatial_uniform_bound L (X:=Unit) (h:ℝ) (fun _=>rfl)
      k (z.2.1.2:ℝ) (z.2.1.2:ℝ) z.2.2.1
    refine ⟨B,hB,fun y x=>?_⟩
    have he:=hb (fun _:Unit=>m) () y x
    simpa only [L,m,field,MovingNativeKernelFields.point,Bool.false_eq_true,if_false,
      ActualMeanKernel.rowSpatial] using he
  · obtain ⟨B,hB,hb⟩:=ActualMeanKernel.weightedSpatial_uniform_bound L (X:=Unit) (h:ℝ) (fun _=>rfl)
      k hΛ (z.2.1.2:ℝ) (z.2.1.2:ℝ) z.2.2.1
    refine ⟨B,hB,fun y x=>?_⟩
    have he:=hb (fun _:Unit=>m) () y x
    simpa only [L,m,field,MovingNativeKernelFields.point,if_true,ActualMeanKernel.weightedSpatial] using he

end SHE.MovingNativeSpatialKernel
