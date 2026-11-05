module

public import SHE.HaarItoEnergy
public import SHE.HaarKernelPairConvergence

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarStochasticConvolution
open MeasureTheory Set Filter PredictableL2 HaarKernelApproximation HaarKernelL2Approximation
open scoped NNReal ENNReal Topology
local instance haarStochasticConvolution_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarStochasticConvolution_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance haarStochasticConvolution_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance haarStochasticConvolution_columnsSigma : MeasurableSpace Columns := borel Columns
local instance haarStochasticConvolution_columnsBorel : BorelSpace Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (I : StandardTerminalIto (C := Columns) (E := LowBands.StateL2) 𝓕 μ h)

/-- The actual predictable Hilbert-valued stochastic convolution of a
bounded elliptic coefficient field. It is constructed as the complete-L²
limit of finite adapted Itô cells, rather than supplied as a premise. -/
def convolution (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) : Process (E := LowBands.StateL2) 𝓕 μ h :=
  limUnder atTop (HaarItoApproximation.output 𝓕 μ h hell hM f hf I)

theorem approximation_tendsto (hh : (h:ℝ) ≤ 1)
    (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) :
    Tendsto (HaarItoApproximation.output 𝓕 μ h hell hM f hf I) atTop
      (𝓝 (convolution 𝓕 μ h hell hM I f hf)) :=
  (HaarItoApproximation.output_cauchy 𝓕 μ h hell hM I f hf hh).tendsto_limUnder

/-- Exact common-Haar difference isometry for the constructed convolution.
Only ordinary terminal Hilbert Itô integration was standard input; all
time-parameter, predictability and limiting work is proved above. -/
theorem difference_isometry (hh : (h:ℝ) ≤ 1)
    (f g : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) (hg : StronglyMeasurable[𝓕.predictable] g) :
    ENNReal.ofReal (‖convolution 𝓕 μ h hell hM I f hf-convolution 𝓕 μ h hell hM I g hg‖^2)=
      ∫⁻ p,ENNReal.ofReal (‖raw hell f p-raw hell g p‖^2) ∂measure μ h := by
  have hsub := (approximation_tendsto 𝓕 μ h hell hM I hh f hf).sub
    (approximation_tendsto 𝓕 μ h hell hM I hh g hg)
  have hout := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hsub.norm.pow 2)
  change Tendsto (fun n => ENNReal.ofReal
    (‖HaarItoApproximation.output 𝓕 μ h hell hM f hf I n-
      HaarItoApproximation.output 𝓕 μ h hell hM g hg I n‖^2)) atTop
    (𝓝 (ENNReal.ofReal (‖convolution 𝓕 μ h hell hM I f hf-convolution 𝓕 μ h hell hM I g hg‖^2))) at hout
  have hkernel := pair_energy_tendsto hell hM μ h hh
    (hf.mono (predictable_le_product 𝓕)).measurable (hg.mono (predictable_le_product 𝓕)).measurable
  have heq : (fun n => ENNReal.ofReal
      (‖HaarItoApproximation.output 𝓕 μ h hell hM f hf I n-
        HaarItoApproximation.output 𝓕 μ h hell hM g hg I n‖^2))=
      (fun n => ∫⁻ p,ENNReal.ofReal (‖approx hell f n p-approx hell g n p‖^2) ∂measure μ h) := by
    funext n
    exact HaarItoApproximation.output_pair_energy 𝓕 μ h hell hM I f g hf hg n n
  rw [← heq] at hkernel
  exact tendsto_nhds_unique hout hkernel

end SHE.HaarStochasticConvolution
