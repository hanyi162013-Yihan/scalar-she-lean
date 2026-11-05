module
public import SHE.AdditiveSmoothCommonLaw
public import SHE.NativeSmoothFirstConstruction
public import SHE.NativePathLawClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.NativeSmoothCommonLaw
open MeasureTheory PredictableL2 LowBands
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable{Ω Ω' D:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable[NormedAddCommGroup D][InnerProductSpace ℝ D][CompleteSpace D]
variable[MeasurableSpace D][BorelSpace D][SecondCountableTopology D]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(h:ℝ≥0)(hh:(h:ℝ)≤1)(κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a)
variable{ell M K β:ℝ}(hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hK:0≤K)
variable(hholder:∀z w,|a z-a w|≤K*|z-w|^β)
variable(I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ h)
variable(J:Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ h)
variable(B:Bool→ℝ≥0)(hBDG:∀b,StandardTerminalBDG16 (I b) (B b))
variable(hpos:0<h)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable(hIJ:∀b,NativeObservationNaturality.StandardScalarNaturality (I b) (J b))
variable(hlocal:∀b,StandardTerminalPastLocality (J b))
local notation "rate"=>NativeClock.rate
local notation "rp"=>NativeClock.rate_pos
include hBDG hpos hnull hIJ hlocal in
/-- The actual full-horizon smooth native models have one path law,
with the original native clock and state realization retained. -/
theorem paths{Lip:ℝ≥0}(hLip:LipschitzWith Lip (fun x=>(a x:ℂ)))(u₀:StateL2)
    (A:NativeSmoothFirstConstruction.Model 𝓕 μ h hh κ hκ ha hell hb hβ hK hholder I u₀)
    (𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (I':Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν h)
    (J':Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν h)
    (hBDG':∀b,StandardTerminalBDG16 (I' b) (B b))
    (hnull':NullCompleteFiltration.ContainsNullSets 𝓖 ν)
    (hIJ':∀b,NativeObservationNaturality.StandardScalarNaturality (I' b) (J' b))
    (hlocal':∀b,StandardTerminalPastLocality (J' b))
    (A':NativeSmoothFirstConstruction.Model 𝓖 ν h hh κ hκ ha hell hb hβ hK hholder I' u₀)
    (stateMap:StateL2→L[ℝ]D)
    (hDriver:μ.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓕 μ h J b i t ω)=
      ν.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓖 ν h J' b i t ω)):
    NativePathLawComparison.law (rate*h) μ
        (fun t ω=>stateMap (NativePairClock.path A.model.value t ω))
        (fun ω=>stateMap.continuous.comp (NativePairClock.path_continuous A.model.value A.model.continuous ω))=
      NativePathLawComparison.law (rate*h) ν
        (fun t ω=>stateMap (NativePairClock.path A'.model.value t ω))
        (fun ω=>stateMap.continuous.comp (NativePairClock.path_continuous A'.model.value A'.model.continuous ω)):=by
  have he:=AdditiveSmoothCommonLaw.paths
    (a:=fun z=>(rate:ℝ)*a z) (ell:=(rate:ℝ)*ell) (M:=(rate:ℝ)*M) (K:=(rate:ℝ)*K) (β:=β)
    𝓕 μ h hh ((rate:ℝ)*κ) (mul_pos rp hκ) (ha.const_mul (rate:ℝ)) (mul_pos rp hell)
    (HaarFieldScaling.scaled_bounds rp hb) hβ (mul_nonneg rate.2 hK)
    (NativeAdditiveResidualPair.scaled_holder hholder) I J B hBDG hpos hnull hIJ hlocal
    (NativeAdditiveResidualPair.scaled_lipschitz hLip) u₀ A
    𝓖 ν I' J' hBDG' hnull' hIJ' hlocal' A' hDriver
  exact NativePathLawClock.native h μ ν A.model.value A'.model.value
    A.model.continuous A'.model.continuous A.model.measurable A'.model.measurable stateMap he
end SHE.NativeSmoothCommonLaw
