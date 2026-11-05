module
public import SHE.AdditiveSmoothMild
import all SHE.AdditiveSmoothMild
public import SHE.SmoothPicardCommonLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
namespace SHE.AdditiveSmoothCommonLaw
open MeasureTheory PredictableL2 LowBands
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable{Ω Ω':Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(H:ℝ≥0)(hH:(H:ℝ)≤1)(κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a)
variable{ell M K β:ℝ}(hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hK:0≤K)
variable(hholder:∀z w,|a z-a w|≤K*|z-w|^β)
variable(I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
variable(J:Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable(B:Bool→ℝ≥0)(hBDG:∀b,StandardTerminalBDG16 (I b) (B b))
variable(hpos:0<H)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable(hIJ:∀b,NativeObservationNaturality.StandardScalarNaturality (I b) (J b))
variable(hlocal:∀b,StandardTerminalPastLocality (J b))
include hBDG hpos hnull hIJ hlocal in
/-- The actual smooth additive/residual models constructed on the two
spaces have the same path law. This retains their exact model fields. -/
theorem paths{Lip:ℝ≥0}(hLip:LipschitzWith Lip (fun x=>(a x:ℂ)))(u₀:StateL2)
    (A:AdditiveSmoothMild.Solution 𝓕 μ H hH κ hκ ha hell hb hβ hK hholder I u₀)
    (𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (I':Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν H)
    (J':Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (hBDG':∀b,StandardTerminalBDG16 (I' b) (B b))
    (hnull':NullCompleteFiltration.ContainsNullSets 𝓖 ν)
    (hIJ':∀b,NativeObservationNaturality.StandardScalarNaturality (I' b) (J' b))
    (hlocal':∀b,StandardTerminalPastLocality (J' b))
    (A':AdditiveSmoothMild.Solution 𝓖 ν H hH κ hκ ha hell hb hβ hK hholder I' u₀)
    (hDriver:μ.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓕 μ H J b i t ω)=
      ν.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓖 ν H J' b i t ω)):
    NativePathLawComparison.law H μ A.model.value A.model.continuous=
      NativePathLawComparison.law H ν A'.model.value A'.model.continuous:=by
  let Lips:Bool→ℝ≥0:=Bool.rec Lip 0
  have hl:∀b,LipschitzWith (Lips b) (fun x=>(AdditiveSmoothMild.coefficient κ a b x:ℂ)):=by
    intro b
    cases b
    · exact hLip
    · exact LipschitzWith.const (κ:ℂ)
  have hp:Continuous (fun t:ℝ≥0=>((t:ℝ),u₀)):=continuous_subtype_val.prodMk continuous_const
  have hz:=RealHeat.continuous_realHeat_action.comp hp
  change Continuous (fun t:ℝ≥0=>RealHeat.realHeat (t:ℝ) u₀) at hz
  exact SmoothPicardCommonLaw.paths 𝓕 μ H hH
    (AdditiveSmoothMild.coefficient κ a) (AdditiveSmoothMild.measurable κ ha)
    (AdditiveSmoothMild.lower κ ell) (AdditiveSmoothMild.upper κ M) (AdditiveSmoothMild.holder K)
    (AdditiveSmoothMild.positive hκ hell) (AdditiveSmoothMild.bounds κ hb)
    β hβ (AdditiveSmoothMild.holder_nonneg hK) (AdditiveSmoothMild.holder_bound κ hholder)
    Lips hl I J B hBDG hpos hnull (fun t=>RealHeat.realHeat (t:ℝ) u₀) hz hIJ hlocal A.model
    𝓖 ν I' J' hBDG' hnull' hIJ' hlocal' A'.model hDriver
end SHE.AdditiveSmoothCommonLaw
