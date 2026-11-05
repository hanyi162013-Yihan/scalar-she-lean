module
public import SHE.InitialNativePredictablePoint
public import SHE.InitialNativeColumns
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
namespace SHE.InitialNativePredictableKernel
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance initialNativePredictableKernel_realSigma : MeasurableSpace RealL2 := borel _
local instance initialNativePredictableKernel_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance initialNativePredictableKernel_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance initialNativePredictableKernel_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance initialNativePredictableKernel_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance initialNativePredictableKernel_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance initialNativePredictableKernel_circleSigma : MeasurableSpace CircleL2 := borel _
local instance initialNativePredictableKernel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance initialNativePredictableKernel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance initialNativePredictableKernel_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "Point"=>InitialNativeKernelFields.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
abbrev Param(k:ℕ):Type:=(Fin k→ℝ)×((Icc (R).base (R).horizon)×(ℝ≥0×Ω))

def field(k:ℕ)(weighted:Bool)(θ:ℝ)
    (z:Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=
  InitialNativeSpatialKernel.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h F hF hFm k weighted θ (((z.1.2.1,z.1.2.2.1),(z.1.1,z.1.2.2.2)),z.2)
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem field_predictable(k:ℕ)(weighted:Bool)(θ:ℝ):
    @Measurable (Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle)) ℂ
      ((((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace (Icc (R).base (R).horizon)).prod 𝓕.predictable))).prod inferInstance) _
      (Field k weighted θ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  let W:=(Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle))×(Fin k→HeatCircle)
  have hh:Measurable (fun z:W=>separated k (z.1.2.2,z.1.1.1,z.2)):=
    (separated_measurable k).comp
      (measurable_fst.snd.snd.prodMk (measurable_fst.fst.fst.prodMk measurable_snd))
  have hmap:Measurable (fun z:W=>
      ((z.1.1.2.2,(z.1.1.2.1,separated k (z.1.2.2,z.1.1.1,z.2))),z.1.2.1)):=
    (measurable_fst.fst.snd.snd.prodMk
      (measurable_fst.fst.snd.fst.prodMk hh)).prodMk measurable_fst.snd.fst
  have hp:=(InitialNativePredictablePoint.point_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k weighted θ).comp hmap
  have hi:=hp.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi)))
  convert! Complex.continuous_ofReal.measurable.comp hi.measurable using 1

def common(k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=
  Field k false 1 z-Field k false 0 z
def endpoint(k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=Field k true 1 z
local notation "Common"=>common 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Endpoint"=>endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "OldCommon"=>InitialNativeColumns.common 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "OldEndpoint"=>InitialNativeColumns.endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem common_predictable(k:ℕ):
    @Measurable (Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle)) ℂ
      ((((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace (Icc (R).base (R).horizon)).prod 𝓕.predictable))).prod inferInstance) _
      (Common k):=
  (field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k false 1).sub
    (field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k false 0)

theorem endpoint_predictable(k:ℕ):
    @Measurable (Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle)) ℂ
      ((((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace (Icc (R).base (R).horizon)).prod 𝓕.predictable))).prod inferInstance) _
      (Endpoint k):=
  field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k true 1

theorem common_eq(k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k)(y x:HeatCircle):
    Common k (z,(y,x))=OldCommon k (((z.2.1,z.2.2.1),(z.1,z.2.2.2)),(y,x)):=rfl
theorem endpoint_eq(k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k)(y x:HeatCircle):
    Endpoint k (z,(y,x))=OldEndpoint k (((z.2.1,z.2.2.1),(z.1,z.2.2.2)),(y,x)):=rfl

theorem common_bound(hΛ:0≤Λ)(k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):
    ∃B:ℝ,0≤B∧∀y x,‖Common k (z,(y,x))‖≤B:=
  InitialNativeColumns.common_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h F hF hFm hΛ k ((z.2.1,z.2.2.1),(z.1,z.2.2.2))

theorem endpoint_bound(hΛ:0≤Λ)(k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):
    ∃B:ℝ,0≤B∧∀y x,‖Endpoint k (z,(y,x))‖≤B:=
  InitialNativeColumns.endpoint_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h F hF hFm hΛ k ((z.2.1,z.2.2.1),(z.1,z.2.2.2))

end SHE.InitialNativePredictableKernel
