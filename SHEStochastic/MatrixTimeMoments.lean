module

public import SHEStochastic.MatrixKernelTimeIncrement
public import SHEStochastic.CausalHeatIncrementEnergy
public import SHEStochastic.MatrixKernelVersion
public import SHEStochastic.DirectHilbertBDG

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixTimeMoments
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixHeatKernelModel
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩

def incrementConstant (d : Type*) [Fintype d] (U : ℝ) : ℝ :=
  4*MatrixKernelTimeIncrement.constant d U+2*MatrixAnalyticKernel.constant d U

theorem incrementConstant_nonneg {U : ℝ} (hU : 0 ≤ U) : 0 ≤ incrementConstant d U :=
  add_nonneg (mul_nonneg (by norm_num) (MatrixKernelTimeIncrement.constant_nonneg hU))
    (mul_nonneg (by norm_num) (MatrixAnalyticKernel.constant_nonneg hU))

def momentConstant (d : Type*) [Fintype d] (U : ℝ) : ℝ :=
  (NativeScalarBDG.constant 3 : ℝ)*(incrementConstant d U)^8

theorem momentConstant_nonneg (U : ℝ) : 0 ≤ momentConstant d U := by
  unfold momentConstant
  positivity

variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (hH : (H : ℝ) ≤ 1) {U : ℝ} (hU : 0 ≤ U) (a : Fields (d := d) F U)

include hH hU

/-- Uniform pathwise increment energy for the literal analytic matrix
Haar convolution, with the old and new time intervals both included. -/
theorem path_energy (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) (ω : Ω) :
    (∫⁻ r, ENNReal.ofReal (‖MatrixAnalyticKernel.kernel ((t : ℝ)-(r : ℝ)) (a.value (r,ω))-
      MatrixAnalyticKernel.kernel ((s : ℝ)-(r : ℝ)) (a.value (r,ω))‖^2) ∂timeMeasure H) ≤
      ENNReal.ofReal (incrementConstant d U*((t : ℝ)-(s : ℝ))^(1/4 : ℝ)) := by
  apply CausalHeatIncrementEnergy.bound
    (fun τ r => MatrixAnalyticKernel.kernel τ (a.value (r,ω)))
    (fun τ hτ r => MatrixAnalyticKernel.zero hτ (a.value (r,ω)))
    (MatrixAnalyticKernel.constant d U) (MatrixKernelTimeIncrement.constant d U)
    (MatrixAnalyticKernel.constant_nonneg hU) (MatrixKernelTimeIncrement.constant_nonneg hU)
    _ _ hH hst htH (fun r => r)
  · intro τ hτ hτ1 r
    exact (MatrixAnalyticKernel.small_bound hτ hτ1 (a.value (r,ω))).trans
      (mul_le_mul_of_nonneg_right (MatrixAnalyticKernel.constant_mono (a.upper (r,ω)))
        (Real.rpow_nonneg hτ.le _))
  · intro τ hτ hτ1 δ hδ r
    exact MatrixKernelTimeIncrement.rate hτ hτ1 hδ (a.value (r,ω)) (a.upper (r,ω))

theorem bracket_bound (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) : ∀ᵐ ω ∂μ,
    (∫⁻ r, ENNReal.ofReal (‖(MatrixAnalyticConvolution.input F μ H hH U hU a.value a.upper a.measurable t htH-
      MatrixAnalyticConvolution.input F μ H hH U hU a.value a.upper a.measurable s (hst.trans htH)) (r,ω)‖^2)
        ∂timeMeasure H) ≤ ENNReal.ofReal (incrementConstant d U*((t : ℝ)-(s : ℝ))^(1/4 : ℝ)) := by
  let v := MatrixAnalyticConvolution.input F μ H hH U hU a.value a.upper a.measurable t htH
  let w := MatrixAnalyticConvolution.input F μ H hH U hU a.value a.upper a.measurable s (hst.trans htH)
  have he : (v-w) =ᵐ[energyMeasure μ H] fun p =>
      MatrixAnalyticKernel.kernel ((t : ℝ)-(p.1 : ℝ)) (a.value p)-
        MatrixAnalyticKernel.kernel ((s : ℝ)-(p.1 : ℝ)) (a.value p) := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub v w),
      MatrixAnalyticConvolution.input_ae F μ H hH U hU a.value a.upper a.measurable t htH,
      MatrixAnalyticConvolution.input_ae F μ H hH U hU a.value a.upper a.measurable s (hst.trans htH)]
      with p hs hv hw
    rw [hs,Pi.sub_apply]
    exact congrArg₂ HSub.hSub hv hw
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  exact (lintegral_congr_ae (hω.mono fun r hr => congrArg (fun z => ENNReal.ofReal (‖z‖^2)) hr)).trans_le
    (path_energy hH hU a s t hst htH ω)

variable (N : FiniteScalarIto.Family F μ H (d × HaarNode))

/-- The sixteen-moment time-increment estimate is derived from the
proved native Hilbert BDG theorem, without an external moment premise. -/
theorem increment_moment16 (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) :
    (∫⁻ ω, ENNReal.ofReal
      (‖MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N t htH ω-
        MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N s (hst.trans htH) ω‖^16) ∂μ) ≤
      ENNReal.ofReal (momentConstant d U*((t : ℝ)-(s : ℝ))^2) := by
  let I := NativeMatrixConvolution.terminalIto N
  let v := MatrixAnalyticConvolution.input F μ H hH U hU a.value a.upper a.measurable t htH
  let w := MatrixAnalyticConvolution.input F μ H hH U hU a.value a.upper a.measurable s (hst.trans htH)
  have hδ : 0 ≤ (t : ℝ)-(s : ℝ) := sub_nonneg.mpr (by exact_mod_cast hst)
  have hb := StandardTerminalBDGPower.moment_of_bracket_bound I
    (DirectHilbertBDG.power_two N MatrixPredictableHaarRotation.basis VectorWhiteCoordinates.basis 3)
    (v-w) (mul_nonneg (incrementConstant_nonneg hU) (Real.rpow_nonneg hδ _))
    (bracket_bound hH hU a s t hst htH)
  have he : (fun ω => I.integral (v-w) ω) =ᵐ[μ]
      fun ω => I.integral v ω-I.integral w ω := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (‖I.integral (v-w) ω‖^16) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]
      rfl
    _ ≤ ENNReal.ofReal ((NativeScalarBDG.constant 3 : ℝ)*
        (incrementConstant d U*((t : ℝ)-(s : ℝ))^(1/4 : ℝ))^8) := hb
    _ = _ := by
      congr 1
      rw [mul_pow,← Real.rpow_mul_natCast hδ]
      norm_num only [Nat.cast_ofNat,show (1/4 : ℝ)*8=2 by norm_num,Real.rpow_two]
      unfold momentConstant
      ring

theorem symmetric_increment_moment16 (s t : ℝ≥0) (hsH : s ≤ H) (htH : t ≤ H) :
    (∫⁻ ω, ENNReal.ofReal
      (‖MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N s hsH ω-
        MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N t htH ω‖^16) ∂μ) ≤
      ENNReal.ofReal (momentConstant d U*((s : ℝ)-(t : ℝ))^2) := by
  rcases le_total s t with hst | hts
  · simpa only [norm_sub_rev,sub_sq_comm] using increment_moment16 hH hU a N s t hst htH
  · exact increment_moment16 hH hU a N t s hts hsH

end SHEStochastic.MatrixTimeMoments
