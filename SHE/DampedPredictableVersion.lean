module

public import SHE.DampedContinuousVersion
public import SHE.NullCompleteFiltration
public import SHE.DampedVersionIdentification

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The constructed continuous Haar convolution is adapted and
predictable in an ambient-null-complete filtration. The completeness
condition is stated explicitly; continuity itself was proved by chaining. -/
noncomputable section
namespace SHE.DampedPredictableVersion
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar DampedContinuousVersion
open scoped NNReal ENNReal
local instance haarPredictableVersion_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarPredictableVersion_stateSigma : MeasurableSpace LowBands.StateL2 := borel LowBands.StateL2
local instance haarPredictableVersion_stateBorel : BorelSpace LowBands.StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)
variable (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
include hBDG

theorem adapted_versions (hh0 : 0 < h) (t : ℝ≥0) :
    ∃ Z : Ω → LowBands.StateL2,StronglyMeasurable[𝓕 t] Z ∧
      version 𝓕 μ h hh hΛ hell hM f hf I t =ᵐ[μ] Z := by
  obtain ⟨Z,hZ,he⟩ := DampedFixedIntegral.adapted_version 𝓕 μ h hh hΛ hell hM f hf I
    (min t h) (min_le_right t h)
  exact ⟨Z,hZ.mono (𝓕.mono (min_le_left t h)),
    (version_ae 𝓕 μ h hh hΛ hell hM f hf I B hBDG hh0 t).trans he⟩

theorem stronglyAdapted_version (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hh0 : 0 < h) : StronglyAdapted 𝓕 (version 𝓕 μ h hh hΛ hell hM f hf I) :=
  NullCompleteFiltration.stronglyAdapted_of_versions 𝓕 μ hnull _
    (adapted_versions 𝓕 μ h hh hΛ hell hM f hf I B hBDG hh0)

theorem predictable_version (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hh0 : 0 < h) :
    StronglyMeasurable[𝓕.predictable]
      (fun p : ℝ≥0 × Ω => version 𝓕 μ h hh hΛ hell hM f hf I p.1 p.2) :=
  NullCompleteFiltration.predictable_of_continuous_versions 𝓕 μ hnull _
    (adapted_versions 𝓕 μ h hh hΛ hell hM f hf I B hBDG hh0)
    (continuous_version 𝓕 μ h hh hΛ hell hM f hf I hh0)

/-- The simultaneously continuous version represents the actual
complete predictable L² stochastic convolution already constructed. -/
theorem convolution_ae_version (hh0 : 0 < h) :
    DampedStochasticConvolution.convolution 𝓕 μ h hh hΛ hell hM I f hf =ᵐ[energyMeasure μ h]
      (fun p : ℝ≥0 × Ω => version 𝓕 μ h hh hΛ hell hM f hf I p.1 p.2) :=
  DampedVersionIdentification.convolution_ae_version 𝓕 μ h hh hΛ hell hM f hf I _
    (version_joint_measurable 𝓕 μ h hh hΛ hell hM f hf I B hBDG hh0).stronglyMeasurable
    (version_ae_of_le 𝓕 μ h hh hΛ hell hM f hf I B hBDG hh0)

end SHE.DampedPredictableVersion
