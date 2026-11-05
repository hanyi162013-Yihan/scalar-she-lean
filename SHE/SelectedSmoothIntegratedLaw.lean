module
public import SHE.SelectedSmoothCommonLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.SelectedSmoothCommonLaw
open MeasureTheory PredictableL2 LowBands OrthogonalItoChannels PredictableTimeDilation
open scoped NNReal ENNReal
local instance : SecondCountableTopology CircleHeat.CircleL2:=(_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance : MeasurableSpace FiniteHaar.RealHaarInput:=borel _
local instance : BorelSpace FiniteHaar.RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both FiniteHaar.RealHaarInput):=borel _
local instance : BorelSpace (Both FiniteHaar.RealHaarInput):=⟨rfl⟩
variable{Ω Ω':Type}[MeasurableSpace Ω][MeasurableSpace Ω']
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(Q:Measure Ω)[IsProbabilityMeasure Q]
variable(H:ℝ≥0)(hH:(H:ℝ)≤1)
variable(κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a)
variable{ell M L β:ℝ}(hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hL:0≤L)
variable(hholder:∀z w,|a z-a w|≤L*|z-w|^β)
variable(K:StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 Q H)
variable(A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 Q H)
variable(u₀:StateL2)
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : MeasurableSpace (Lp StateL2 2 (SHE.timeMeasure (H:ℝ))):=borel _
local instance : BorelSpace (Lp StateL2 2 (SHE.timeMeasure (H:ℝ))):=⟨rfl⟩

/-- The exact integrated-path laws of the selected actual smooth
solutions agree, ready for the final bounded-test comparison. -/
theorem integrated{Lip:ℝ≥0}(hLip:LipschitzWith Lip (fun z=>(a z:ℂ)))(hpos:0<H)
    (D:SelectedGirsanovSmoothModel.Data 𝓕 Q H hH κ hκ ha hell hb hβ hL hholder K A0 A1 u₀)
    (𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (K':StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (A0' A1':StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν H)
    (D':SelectedGirsanovSmoothModel.Data 𝓖 ν H hH κ hκ ha hell hb hβ hL hholder K' A0' A1' u₀):
    let W:=SelectedGirsanovSmoothModel.Data.solution 𝓕 Q H hH κ hκ ha hell hb hβ hL hholder K A0 A1 u₀ D
    let W':=SelectedGirsanovSmoothModel.Data.solution 𝓖 ν H hH κ hκ ha hell hb hβ hL hholder K' A0' A1' u₀ D'
    Q.map (NativeContinuousPath.integrated H W.value W.continuous)=
      ν.map (NativeContinuousPath.integrated H W'.value W'.continuous):=by
  let W:=SelectedGirsanovSmoothModel.Data.solution 𝓕 Q H hH κ hκ ha hell hb hβ hL hholder K A0 A1 u₀ D
  let W':=SelectedGirsanovSmoothModel.Data.solution 𝓖 ν H hH κ hκ ha hell hb hβ hL hholder K' A0' A1' u₀ D'
  have hm:Measurable (Function.uncurry W.value):=
    (W.predictable.mono (predictable_le_product 𝓕)).measurable
  have hm':Measurable (Function.uncurry W'.value):=
    (W'.predictable.mono (predictable_le_product 𝓖)).measurable
  have he:=paths Q 𝓕 H hH κ hκ ha hell hb hβ hL hholder K A0 A1 u₀ hLip hpos D 𝓖 ν K' A0' A1' D'
  change NativePathLawComparison.law H Q W.value W.continuous=
    NativePathLawComparison.law H ν W'.value W'.continuous at he
  have hi:=congrArg (fun m:ProbabilityMeasure C(Set.Icc (0:ℝ) (H:ℝ),StateL2)=>
    ProbabilityMeasure.map m (ContinuousMap.toLp (E:=StateL2) 2 (SHE.timeMeasure (H:ℝ)) ℝ)) he
  rw [NativePathLawComparison.integrated_law H Q W.value W.continuous hm,
    NativePathLawComparison.integrated_law H ν W'.value W'.continuous hm'] at hi
  exact congrArg Subtype.val hi
end SHE.SelectedSmoothCommonLaw
