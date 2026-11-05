module

public import SHEStochastic.NativeMatrixConvolution
public import SHEStochastic.DirectHilbertBDG

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixConvolutionMoments
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixHaarKernel MatrixFixedHaarInput
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
variable (N : FiniteScalarIto.Family F μ H (d × FiniteHaar.HaarNode))
  (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ U)
  (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun p => (Q p.1).value p.2))

def cap (t : ℝ≥0) : ℝ := horizonConstant d H U*(2*(t : ℝ)^(1/2 : ℝ))

include hU in
theorem cap_nonneg (t : ℝ≥0) : 0 ≤ cap (H := H) (d := d) U t :=
  mul_nonneg (horizonConstant_nonneg H hU) (mul_nonneg (by norm_num) (Real.rpow_nonneg t.coe_nonneg _))

include hU hUpper in
theorem path_energy (t : ℝ≥0) (ht : t ≤ H) (ω : Ω) :
    (∫⁻ s, ENNReal.ofReal (‖kernel ((t : ℝ)-(s : ℝ)) (Q (s,ω))‖^2) ∂timeMeasure H) ≤
      ENNReal.ofReal (cap (H := H) (d := d) U t) := by
  have hb := MatrixFixedHaarInput.horizon_energy (Measure.dirac ()) H U hU
    (fun p : ℝ≥0 × Unit => Q (p.1,ω)) (fun p => hUpper (p.1,ω)) t ht
  simpa only [lintegral_dirac,cap] using hb

theorem bracket_bound (t : ℝ≥0) (ht : t ≤ H) : ∀ᵐ ω ∂μ,
    (∫⁻ s, ENNReal.ofReal (‖MatrixFixedHaarInput.input F μ H U hU Q hUpper hQ t ht (s,ω)‖^2)
      ∂timeMeasure H) ≤ ENNReal.ofReal (cap (H := H) (d := d) U t) := by
  have he := MatrixFixedHaarInput.input_ae F μ H U hU Q hUpper hQ t ht
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  exact (lintegral_congr_ae (hω.mono fun s hh => congrArg (fun v => ENNReal.ofReal (‖v‖^2)) hh)).trans_le
    (path_energy U hU Q hUpper t ht ω)

/-- Arbitrarily high dyadic moments for the actual vector convolution
with a random predictable matrix coefficient, without Gaussianity. -/
theorem moment (t : ℝ≥0) (ht : t ≤ H) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (‖NativeMatrixConvolution.value N U hU Q hUpper hQ t ht ω‖^(2*2^k)) ∂μ) ≤
      ENNReal.ofReal ((NativeScalarBDG.constant k : ℝ)*(cap (H := H) (d := d) U t)^(2^k)) :=
  StandardTerminalBDGPower.moment_of_bracket_bound (NativeMatrixConvolution.terminalIto N)
    (DirectHilbertBDG.power_two N MatrixPredictableHaarRotation.basis VectorWhiteCoordinates.basis k)
    (MatrixFixedHaarInput.input F μ H U hU Q hUpper hQ t ht)
    (cap_nonneg U hU t) (bracket_bound U hU Q hUpper hQ t ht)

theorem integrable_moment (t : ℝ≥0) (ht : t ≤ H) (k : ℕ) :
    Integrable (fun ω => ‖NativeMatrixConvolution.value N U hU Q hUpper hQ t ht ω‖^(2*2^k)) μ := by
  refine ⟨((Lp.stronglyMeasurable _).norm.pow _).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => pow_nonneg (norm_nonneg _) _)]
  exact (moment N U hU Q hUpper hQ t ht k).trans_lt ENNReal.ofReal_lt_top

theorem memLp (t : ℝ≥0) (ht : t ≤ H) (k : ℕ) :
    MemLp (NativeMatrixConvolution.value N U hU Q hUpper hQ t ht : Ω → Physical (d := d))
      ((2*2^k : ℕ) : ENNReal) μ := by
  apply (integrable_norm_rpow_iff (Lp.aestronglyMeasurable _)
    (by positivity : ((2*2^k : ℕ) : ENNReal) ≠ 0) (by finiteness)).mp
  simpa only [ENNReal.toReal_natCast,Real.rpow_natCast] using integrable_moment N U hU Q hUpper hQ t ht k

end SHEStochastic.MatrixConvolutionMoments
