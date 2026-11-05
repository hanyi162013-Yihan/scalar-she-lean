module

public import SHE.DampedFixedApproximation
public import SHE.DampedStochasticConvolution
public import SHE.ProductLpIdentification

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.DampedVersionIdentification
open MeasureTheory Set Filter PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal Topology
local instance haarVersionIdentification_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarVersionIdentification_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance haarVersionIdentification_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance haarVersionIdentification_stateSigma : MeasurableSpace LowBands.StateL2 := borel LowBands.StateL2
local instance haarVersionIdentification_stateBorel : BorelSpace LowBands.StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)

def approximation (n : ℕ) : Process (E := LowBands.StateL2) 𝓕 μ h :=
  KernelItoLimit.output (DampedKernelModel.model 𝓕 μ h hh hΛ hell hM) I ⟨f,hf⟩ n

theorem approximation_tendsto : Filter.Tendsto (approximation 𝓕 μ h hh hΛ hell hM f hf I)
    Filter.atTop (𝓝 (DampedStochasticConvolution.convolution 𝓕 μ h hh hΛ hell hM I f hf)) :=
  KernelItoLimit.approximation_tendsto (DampedKernelModel.model 𝓕 μ h hh hΛ hell hM) I ⟨f,hf⟩

/-- A jointly measurable fixed-time version of the terminal heat
integrals is the previously constructed complete predictable L²
convolution. No parameterized stochastic integration identity is assumed. -/
theorem convolution_ae_version (Y : ℝ≥0 × Ω → LowBands.StateL2)
    (hY : StronglyMeasurable Y)
    (hversion : ∀ (t : ℝ≥0) (ht : t ≤ h), (fun ω => Y (t,ω)) =ᵐ[μ]
      DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t ht) :
    DampedStochasticConvolution.convolution 𝓕 μ h hh hΛ hell hM I f hf =ᵐ[energyMeasure μ h] Y := by
  let A := ambientIsometry (E := LowBands.StateL2) (energyMeasure μ h) (predictable_le_product 𝓕)
  let v : ℕ → Lp LowBands.StateL2 2 (energyMeasure μ h) :=
    fun n => A (approximation 𝓕 μ h hh hΛ hell hM f hf I n)
  let V : Lp LowBands.StateL2 2 (energyMeasure μ h) :=
    A (DampedStochasticConvolution.convolution 𝓕 μ h hh hΛ hell hM I f hf)
  have hv : Tendsto v atTop (𝓝 V) :=
    A.continuous.continuousAt.tendsto.comp
      (approximation_tendsto 𝓕 μ h hh hΛ hell hM f hf I)
  have hslices : ∀ᵐ t ∂timeMeasure h, ∀ n,
      (fun ω => v n (t,ω)) =ᵐ[μ]
        I.integral (DampedCellIntegrands.input 𝓕 μ h hΛ hell hM f hf n (ApproximationCells.index n t)) := by
    apply ae_all_iff.mpr
    intro n
    have ha : ∀ᵐ t ∂timeMeasure h, (fun ω => v n (t,ω)) =ᵐ[μ]
        (fun ω => approximation 𝓕 μ h hh hΛ hell hM f hf I n (t,ω)) :=
      Measure.ae_ae_of_ae_prod (ambient_ae (energyMeasure μ h) (predictable_le_product 𝓕)
        (approximation 𝓕 μ h hh hΛ hell hM f hf I n))
    have hb := PredictableItoCells.output_slice_ae I n
      (DampedCellIntegrands.input 𝓕 μ h hΛ hell hM f hf n)
      (DampedCellIntegrands.input_stopped 𝓕 μ h hΛ hell hM f hf n)
    filter_upwards [ha,hb] with t ht ht'
    exact ht.trans ht'
  have hs : ∀ᵐ t ∂timeMeasure h,
      TendstoInMeasure μ (fun n ω => v n (t,ω)) atTop (fun ω => Y (t,ω)) := by
    filter_upwards [timeMeasure_ae_mem h,hslices] with t ht hs
    have hI := tendstoInMeasure_of_tendsto_Lp
      (DampedFixedApproximation.integral_tendsto 𝓕 μ h hh hΛ hell hM f hf I t ht.1 ht.2)
    exact TendstoInMeasure.congr_right (hversion t ht.2).symm
      (TendstoInMeasure.congr_left (fun n => (hs n).symm) hI)
  have hEq : V =ᵐ[energyMeasure μ h] Y :=
    ProductLpIdentification.ae_eq_of_slice_limits (timeMeasure h) μ v V hv Y hY hs
  exact (ambient_ae (energyMeasure μ h) (predictable_le_product 𝓕)
    (DampedStochasticConvolution.convolution 𝓕 μ h hh hΛ hell hM I f hf)).symm.trans hEq

end SHE.DampedVersionIdentification
