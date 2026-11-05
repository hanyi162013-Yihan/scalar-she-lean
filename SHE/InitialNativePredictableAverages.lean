module
public import SHE.InitialNativePredictableColumns
public import SHE.InitialNativeAverageActual
public import SHE.MixedNativeOriginalFourierRows
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.InitialNativePredictableAverages
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  Set WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories HistoryProductMeasure AddCircle
open scoped NNReal ENNReal
local instance initialNativePredictableAverages_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance initialNativePredictableAverages_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance initialNativePredictableAverages_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance initialNativePredictableAverages_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance initialNativePredictableAverages_realSigma:MeasurableSpace RealL2:=borel _
local instance initialNativePredictableAverages_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance initialNativePredictableAverages_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance initialNativePredictableAverages_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩
local instance initialNativePredictableAverages_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance initialNativePredictableAverages_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance initialNativePredictableAverages_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance initialNativePredictableAverages_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Add"=>InitialNativePredictableColumns.additive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Base"=>InitialNativePredictableColumns.base
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Signed"=>InitialNativePredictableColumns.signed
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "OldLeft"=>InitialNativeColumnAverages.left
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "OldRight"=>InitialNativeColumnAverages.right
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
abbrev Terminal:Type:=Icc (R).base (R).horizon
abbrev Param:Type:=Terminal Λ u₀ P haP h×(ℝ≥0×Ω)

def left(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param Λ u₀ P haP h (Ω:=Ω)):NativeKernelHaarColumns.Space:=
  if 0<(z.2.1:ℝ)∧(z.2.1:ℝ)<(z.1:ℝ) then
    ∫t:Fin k→ℝ,Add hΛ k hmass hρ (t,z) ∂Measure.pi (fun _=>volume.restrict (Ioc 0 (h:ℝ))) else 0
def right(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param Λ u₀ P haP h (Ω:=Ω)):NativeKernelHaarColumns.Space:=
  if 0<(z.2.1:ℝ)∧(z.2.1:ℝ)<(z.1:ℝ) then
    (∫t:Fin k→ℝ,Base hΛ k hmass hρ (t,z) ∂Measure.pi (fun _=>volume.restrict (Ioc 0 (h:ℝ))))+
    (∫t:Fin k→ℝ,Signed k hmass hρ (t,z) ∂Measure.pi (fun _=>volume.restrict (Ioc 0 (h:ℝ)))) else 0
local notation "Left"=>left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Right"=>right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
private theorem active_measurable:
    @MeasurableSet (Param Λ u₀ P haP h (Ω:=Ω))
      ((inferInstance:MeasurableSpace (Terminal Λ u₀ P haP h)).prod 𝓕.predictable)
      {z|0<(z.2.1:ℝ)∧(z.2.1:ℝ)<(z.1:ℝ)}:=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hq:Measurable (fun z:Param Λ u₀ P haP h (Ω:=Ω)=>(z.2.1:ℝ)):=NNReal.continuous_coe.measurable.comp ((PredictableClock.time_measurable 𝓕).comp measurable_snd)
  exact (measurableSet_lt measurable_const hq).inter
    (measurableSet_lt hq (measurable_subtype_coe.comp measurable_fst))

theorem left_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (Param Λ u₀ P haP h (Ω:=Ω)) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace (Terminal Λ u₀ P haP h)).prod 𝓕.predictable) _ (Left hΛ k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hm:=(InitialNativePredictableColumns.additive_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k hmass hρ).comp measurable_swap
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))) |>.measurable).ite
    (active_measurable 𝓕 Λ u₀ P haP h) measurable_const

theorem right_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    @Measurable (Param Λ u₀ P haP h (Ω:=Ω)) NativeKernelHaarColumns.Space
      ((inferInstance:MeasurableSpace (Terminal Λ u₀ P haP h)).prod 𝓕.predictable) _ (Right hΛ k hmass hρ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hb:=(InitialNativePredictableColumns.base_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k hmass hρ).comp measurable_swap
  have hs:=(InitialNativePredictableColumns.signed_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k hmass hρ).comp measurable_swap
  exact (hb.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))) |>.measurable).add
    (hs.stronglyMeasurable.integral_prod_right'
      (ν:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 (h:ℝ)))) |>.measurable) |>.ite
    (active_measurable 𝓕 Λ u₀ P haP h) measurable_const

theorem left_eq(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param Λ u₀ P haP h (Ω:=Ω)):
    Left hΛ k hmass hρ z=InitialNativeColumnAverages.guardedLeft
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k hmass hρ ((z.1,z.2.1),z.2.2):=rfl

theorem right_eq(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:Param Λ u₀ P haP h (Ω:=Ω)):
    Right hΛ k hmass hρ z=InitialNativeColumnAverages.guardedRight
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k hmass hρ ((z.1,z.2.1),z.2.2):=rfl

def row(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)
    (z:Param Λ u₀ P haP h (Ω:=Ω)):Both RealHaarInput:=
  WithLp.toLp 2
    (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Left hΛ k hmass hρ z),
     HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Right hΛ k hmass hρ z))

theorem row_original(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)
    (T:Terminal Λ u₀ P haP h)(q:ℝ≥0)(ω:Ω):
    row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
      hΛ k hmass hρ a l (T,(q,ω))=WithLp.toLp 2
        (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l))
          (InitialNativeColumnAverages.guardedLeft 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k hmass hρ ((T,q),ω)),
         HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l))
          (InitialNativeColumnAverages.guardedRight 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k hmass hρ ((T,q),ω))):=rfl

/-- Both real and imaginary complete native Fourier inputs are genuinely
jointly predictable in the initial terminal parameter and the ORIGINAL noise clock. -/
theorem row_predictable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(a:ℂ→L[ℝ]ℝ)(l:ℤ):
    StronglyMeasurable[((inferInstance:MeasurableSpace (Terminal Λ u₀ P haP h)).prod 𝓕.predictable)]
      (row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
        hΛ k hmass hρ a l):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have h0:=(HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l))).continuous.measurable.comp
    (left_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k hmass hρ)
  have h1:=(HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l))).continuous.measurable.comp
    (right_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ k hmass hρ)
  exact ((WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput).measurable.comp
    (h0.prodMk h1)).stronglyMeasurable
end SHE.InitialNativePredictableAverages
