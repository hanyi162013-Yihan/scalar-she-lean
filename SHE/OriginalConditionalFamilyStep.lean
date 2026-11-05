module
public import SHE.OriginalNativeConditionalKernels
public import SHE.ConditionalCanonicalModelFamily
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.OriginalConditionalFamilyStep
open MeasureTheory ProbabilityTheory Set PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels
open scoped NNReal ENNReal
local instance familyStep_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance familyStep_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance familyStep_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance familyStep_realSigma:MeasurableSpace RealL2:=borel _
local instance familyStep_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance familyStep_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance familyStep_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance familyStep_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance familyStep_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
variable {ι:Type} [Fintype ι] [Nonempty ι] (Ω:ι→Type) [∀i,MeasurableSpace (Ω i)]
variable (𝓕:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
variable (μ:∀i,Measure (Ω i)) [∀i,IsProbabilityMeasure (μ i)]
variable (H:ℝ≥0) (D:SmoothApproximation.ScalarData)
variable (B:∀i,StandardTerminalIto (C:=Both RealL2) (E:=ℝ) (𝓕 i) (μ i) H) (u₀:RealL2)
variable (S:∀i,OriginalNativeHeatEquation.Data (𝓕 i) (μ i) H D (B i) u₀)
variable (v h:ℝ≥0) (hpos:0<H)

def kernel (i:ι) := OriginalShiftedSingleModels.kernel (𝓕 i) (μ i) H D (B i) u₀ (S i) v h hpos
instance kernel_markov (i:ι) : IsMarkovKernel (kernel Ω 𝓕 μ H D B u₀ S v h hpos i) := by
  unfold kernel OriginalShiftedSingleModels.kernel
  infer_instance

def pastLaw (i:ι) := (μ i).map (NativeContinuousPath.path v (S i).value (S i).continuous)
def futureKernel (i:ι) := OriginalNativeConditionalKernels.stateKernel (𝓕 i) (μ i) H D (B i) u₀ (S i) v h

/-- Only ordinary stochastic inputs on the actual selected conditional
integrals and product/rotated maps; no conditional future-law or
uniqueness conclusion is included in this selector. -/
abbrev OrdinaryInputs := ∀i,∀ᵐp∂pastLaw Ω 𝓕 μ H D B u₀ S v i,
  ∀(A:∀i,ConditionalCanonicalModelFamily.Packet h D
    (kernel Ω 𝓕 μ H D B u₀ S v h hpos i p) (OriginalShiftedSingleModels.known v p)),
  Nonempty (ConditionalCanonicalModelFamily.OrdinaryInputs h D
    (kernel Ω 𝓕 μ H D B u₀ S v h hpos) (OriginalShiftedSingleModels.known v) p A)

/-- Actual conditional future STATE kernels agree whenever the already
constructed state prefixes have the same laws. All conditional weak
models and the local comparison are instantiated internally. -/
theorem future_eq (hvh:v+h≤H) (hh:0<h) (hsmall:(h:ℝ)≤1)
    (C:ι→ℝ≥0) (hBDG:∀i,StandardTerminalBDG16 (B i) (C i))
    (hnull:∀i,NullCompleteFiltration.ContainsNullSets (𝓕 i) (μ i))
    (hLevy:∀i,StandardTerminalLevy (B i)) (hlocal:∀i,StandardTerminalPastLocality (B i))
    (hConstruct:∀i p,StandardBrownianItoConstruction (ConditionalCanonicalModelFamily.filtration h)
      (kernel Ω 𝓕 μ H D B u₀ S v h hpos i p) h NativeSingleNoiseBasis.basis
        (CanonicalStateDriverFiltration.coordinate h))
    (hprefix:∀i j,pastLaw Ω 𝓕 μ H D B u₀ S v i=pastLaw Ω 𝓕 μ H D B u₀ S v j)
    (hInputs:OrdinaryInputs Ω 𝓕 μ H D B u₀ S v h hpos) :
    ∀i j:ι,futureKernel Ω 𝓕 μ H D B u₀ S v h i=ᵐ[pastLaw Ω 𝓕 μ H D B u₀ S v i]
      futureKernel Ω 𝓕 μ H D B u₀ S v h j := by
  let i₀:ι := Classical.choice (inferInstance:Nonempty ι)
  let ρ := pastLaw Ω 𝓕 μ H D B u₀ S v i₀
  have hpacks (i:ι) : ∀ᵐp∂ρ,Nonempty (ConditionalCanonicalModelFamily.Packet h D
      (kernel Ω 𝓕 μ H D B u₀ S v h hpos i p) (OriginalShiftedSingleModels.known v p)) := by
    change ∀ᵐp∂pastLaw Ω 𝓕 μ H D B u₀ S v i₀,_
    rw [←hprefix i i₀]
    filter_upwards [OriginalShiftedSingleModels.exists_models (𝓕 i) (μ i) H D (B i) u₀ (S i)
      v h hvh hpos (C i) (hBDG i) (hnull i) (hLevy i) (hlocal i) (hConstruct i)] with p hp
    obtain ⟨K,hK,hLift,hBasis,M,hM⟩ := hp
    exact ⟨⟨K,hK,hLift,hBasis,M,hM⟩⟩
  have hstates := ConditionalCanonicalModelFamily.state_laws_eq_ae h D
    (kernel Ω 𝓕 μ H D B u₀ S v h hpos) ρ (OriginalShiftedSingleModels.known v)
    hh hsmall hpacks (hInputs i₀)
  intro i j
  have hs : ∀ᵐp∂pastLaw Ω 𝓕 μ H D B u₀ S v i,
      (kernel Ω 𝓕 μ H D B u₀ S v h hpos i p).map Prod.fst=
      (kernel Ω 𝓕 μ H D B u₀ S v h hpos j p).map Prod.fst := by
    rw [hprefix i i₀]
    exact hstates.mono (fun p hp=>hp i j)
  have hi := OriginalNativeConditionalKernels.state_projection (𝓕 i) (μ i) H D (B i) u₀ (S i)
    v h hpos (C i) (hBDG i) (hnull i)
  have hj := OriginalNativeConditionalKernels.state_projection (𝓕 j) (μ j) H D (B j) u₀ (S j)
    v h hpos (C j) (hBDG j) (hnull j)
  have hj' : futureKernel Ω 𝓕 μ H D B u₀ S v h j=ᵐ[pastLaw Ω 𝓕 μ H D B u₀ S v i]
      (kernel Ω 𝓕 μ H D B u₀ S v h hpos j).map Prod.fst := by
    rw [hprefix i j]
    exact hj
  filter_upwards [hi,hs,hj'] with p hi hs hj
  rw [Kernel.map_apply _ measurable_fst p] at hi hj
  exact hi.trans (hs.trans hj.symm)
end SHE.OriginalConditionalFamilyStep
