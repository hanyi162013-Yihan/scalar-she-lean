module
public import SHE.MovingNativeColumns
public import SHE.NativeKernelHaarColumns
public import SHE.RawKernelColumns
public import SHE.SeparatedMeanBounds
public import SHE.WeightedMeanBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
namespace SHE.MovingNativeColumnAverages
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
abbrev Param:Type:=(ℝ≥0×ℝ≥0)×Ω
local notation "Add"=>MovingNativeColumns.additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "BaseCols"=>MovingNativeColumns.base 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Signed"=>MovingNativeColumns.signed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local instance movingNativeColumnAverages_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance movingNativeColumnAverages_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩

/-- Actual original old times are translated to this fixed relative cube before squaring. -/
def left (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param (Ω:=Ω)):
    NativeKernelHaarColumns.Space:=
  ∫t,Add hΛ k hmass hρ (z.1,(t,z.2)) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))

def right (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param (Ω:=Ω)):
    NativeKernelHaarColumns.Space:=
  (∫t,BaseCols hΛ k hmass hρ (z.1,(t,z.2)) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ))))+
  (∫t,Signed k hmass hρ (z.1,(t,z.2)) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ))))
local notation "Left"=>left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Right"=>right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

private theorem average_measurable (k:ℕ)(G:MovingNativeColumns.Param (Ω:=Ω) k→NativeKernelHaarColumns.Space)
    (hG:Measurable G):Measurable (fun z:Param (Ω:=Ω)=>
      ∫t,G (z.1,(t,z.2)) ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))):=by
  have hh:=hG.comp ((measurable_fst.fst).prodMk (measurable_snd.prodMk measurable_fst.snd))
  exact hh.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))) |>.measurable

theorem left_measurable (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Measurable (Left hΛ k hmass hρ):=
  average_measurable h k _ (MovingNativeColumns.additive_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ)

theorem right_measurable (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Measurable (Right hΛ k hmass hρ):=by
  exact (average_measurable h k _ (MovingNativeColumns.base_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ)).add
    (average_measurable h k _ (MovingNativeColumns.signed_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ))

/-- The actual post-past stochastic support is imposed explicitly. -/
def guardedLeft (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param (Ω:=Ω)):
    NativeKernelHaarColumns.Space:=if 0<z.1.2∧z.1.2<h then Left hΛ k hmass hρ z else 0

def guardedRight (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param (Ω:=Ω)):
    NativeKernelHaarColumns.Space:=if 0<z.1.2∧z.1.2<h then Right hΛ k hmass hρ z else 0

theorem guardedLeft_measurable (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (guardedLeft 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ):=
  (left_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ).ite
    ((measurable_fst.snd) measurableSet_Ioo) measurable_const

theorem guardedRight_measurable (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (guardedRight 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ):=
  (right_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k hmass hρ).ite
    ((measurable_fst.snd) measurableSet_Ioo) measurable_const

end SHE.MovingNativeColumnAverages
