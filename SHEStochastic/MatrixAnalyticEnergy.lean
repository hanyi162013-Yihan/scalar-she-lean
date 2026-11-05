module

public import SHEStochastic.MatrixSquareAnalyticConvolution
public import SHEStochastic.CausalKernelInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixAnalyticEnergy
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (hH : (H : ℝ)≤1) {cap : ℝ} (hcap : 0≤cap)
    (Q : ℝ≥0×Ω → Profile d) (hUpper : ∀ p,(Q p).upper≤cap)
    (hQ : @Measurable ((ℝ≥0×Ω)×AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

/-- A uniform second-moment bound for any compatible vector Itô
integral of the actual physical-clock heat kernel. -/
theorem bound (J : StandardTerminalIto (C := MatrixHaarKernel.Columns (d := d))
    (E := Physical (d := d)) F μ H) (t : ℝ≥0) (ht : t≤H) :
    ENNReal.ofReal (‖J.integral
      (MatrixAnalyticConvolution.input F μ H hH cap hcap Q hUpper hQ t ht)‖^2)≤
      ENNReal.ofReal (MatrixAnalyticKernel.constant d cap*(2*(t : ℝ)^(1/2 : ℝ))) := by
  rw [J.isometry_energy]
  have he : (∫⁻ s,∫⁻ ω, ENNReal.ofReal
      (‖MatrixAnalyticConvolution.input F μ H hH cap hcap Q hUpper hQ t ht (s,ω)‖^2)
        ∂μ ∂timeMeasure H)=
      ∫⁻ s,∫⁻ ω, ENNReal.ofReal (‖MatrixAnalyticKernel.kernel ((t : ℝ)-(s : ℝ)) (Q (s,ω))‖^2)
        ∂μ ∂timeMeasure H := by
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod
      (MatrixAnalyticConvolution.input_ae F μ H hH cap hcap Q hUpper hQ t ht)] with s hs
    exact lintegral_congr_ae (hs.mono (fun _ h => congrArg (fun v => ENNReal.ofReal (‖v‖^2)) h))
  rw [he]
  apply CausalKernelInput.fixed_energy (fun τ p => MatrixAnalyticKernel.kernel τ (Q p))
    (fun τ hτ p => MatrixAnalyticKernel.zero hτ (Q p))
    (MatrixAnalyticKernel.constant d cap) (MatrixAnalyticKernel.constant_nonneg hcap) _ μ hH ht
  intro τ hτ hτ1 p
  exact (MatrixAnalyticKernel.small_bound hτ hτ1 (Q p)).trans
    (mul_le_mul_of_nonneg_right (MatrixAnalyticKernel.constant_mono (hUpper p))
      (Real.rpow_nonneg hτ.le _))

end SHEStochastic.MatrixAnalyticEnergy
