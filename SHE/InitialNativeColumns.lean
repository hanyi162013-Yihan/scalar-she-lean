module
public import SHE.InitialNativeSpatialKernel
public import SHE.NativeKernelHaarColumns
public import SHE.RawKernelColumns
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
namespace SHE.InitialNativeColumns
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
abbrev Param (k:ℕ):Type:=InitialNativeSpatialKernel.Param Λ u₀ P haP h (Ω:=Ω) k
local notation "Field"=>InitialNativeSpatialKernel.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

/-- Complete unweighted kernel difference at the true moving current. -/
def common (k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=
  Field k false 1 z-Field k false 0 z
/-- Stop-weighted endpoint kernel, with law and row both at the true current. -/
def endpoint (k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=
  Field k true 1 z
local notation "Common"=>common 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Endpoint"=>endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem common_measurable (k:ℕ):Measurable (Common k):=
  (InitialNativeSpatialKernel.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k false 1).sub
    (InitialNativeSpatialKernel.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k false 0)

theorem endpoint_measurable (k:ℕ):Measurable (Endpoint k):=
  InitialNativeSpatialKernel.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k true 1

theorem common_bound (hΛ:0≤Λ)(k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):
    ∃B:ℝ,0≤B∧∀y x,‖Common k (z,(y,x))‖≤B:=by
  obtain ⟨B1,h1,hb1⟩:=InitialNativeSpatialKernel.field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k false 1 z
  obtain ⟨B0,h0,hb0⟩:=InitialNativeSpatialKernel.field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k false 0 z
  exact ⟨B1+B0,add_nonneg h1 h0,fun y x=>(norm_sub_le _ _).trans (add_le_add (hb1 y x) (hb0 y x))⟩

theorem endpoint_bound (hΛ:0≤Λ)(k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):
    ∃B:ℝ,0≤B∧∀y x,‖Endpoint k (z,(y,x))‖≤B:=
  InitialNativeSpatialKernel.field_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h F hF hFm hΛ k true 1 z

local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

def coefficientU (k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):EllipticField ell M:=CU (z.1.2,z.2.2)
def coefficientV (k:ℕ)(z:Param Λ u₀ P haP h (Ω:=Ω) k):EllipticField ell M:=CV (z.1.2,z.2.2)
local notation "CoefU"=>coefficientU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
local notation "CoefV"=>coefficientV 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h

theorem coefficientU_measurable (k:ℕ):Measurable (CoefU k):=
  (S.first_coefficient.mono (predictable_le_product 𝓕)).measurable.comp
    (measurable_fst.snd.prodMk measurable_snd.snd)
theorem coefficientV_measurable (k:ℕ):Measurable (CoefV k):=
  (S.second_coefficient.mono (predictable_le_product 𝓕)).measurable.comp
    (measurable_fst.snd.prodMk measurable_snd.snd)

local instance movingNativeColumns_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance movingNativeColumns_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩

def additive (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Param Λ u₀ P haP h (Ω:=Ω) k→NativeKernelHaarColumns.Space:=
  NativeKernelHaarColumns.columns hmass hρ hκ
    (common_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k)
    (fun z=>by
      obtain ⟨B,_,hb⟩:=common_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h F hF hFm hΛ k z
      exact ⟨B,hb⟩)
    (fun _=>AdditiveHaarForcing.constantField κ hκ)

def base (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Param Λ u₀ P haP h (Ω:=Ω) k→NativeKernelHaarColumns.Space:=
  NativeKernelHaarColumns.columns hmass hρ hell
    (common_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k)
    (fun z=>by
      obtain ⟨B,_,hb⟩:=common_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h F hF hFm hΛ k z
      exact ⟨B,hb⟩)
    (CoefU k)

def signed (k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Param Λ u₀ P haP h (Ω:=Ω) k→NativeKernelHaarColumns.Space:=
  SignedKernelColumns.rawColumns (Endpoint k) mass ρ hmass hρ ell M hell (CoefU k) (CoefV k)

local notation "Add"=>additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "BaseCols"=>base 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Signed"=>signed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem additive_measurable (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Measurable (Add hΛ k hmass hρ):=by
  unfold additive
  exact NativeKernelHaarColumns.columns_measurable _ _ _ _ _ _ measurable_const

theorem base_measurable (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Measurable (BaseCols hΛ k hmass hρ):=by
  unfold base
  exact NativeKernelHaarColumns.columns_measurable _ _ _ _ _ _
    (coefficientU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h k)

theorem signed_measurable (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Measurable (Signed k hmass hρ):=by
  unfold signed
  exact SignedKernelColumns.rawColumns_measurable
    (endpoint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k)
    (endpoint_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k)
    hmass hρ hell _ _
    (coefficientU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h k)
    (coefficientV_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h k)

end SHE.InitialNativeColumns
