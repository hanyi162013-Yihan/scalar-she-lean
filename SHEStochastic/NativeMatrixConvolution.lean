module

public import SHEStochastic.MatrixFixedHaarInput
public import SHEStochastic.FiniteCylindricalTerminalIto
public import SHEStochastic.HilbertTerminalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.NativeMatrixConvolution
open MeasureTheory SHE SHE.FiniteHaar SHE.PredictableL2 MatrixInfiniteHaar MatrixHaarKernel
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- The native terminal vector integral is reused directly from the
proved cylindrical construction and the actual complete vector basis. -/
def terminalIto (N : FiniteScalarIto.Family F μ H (d × HaarNode)) :
    StandardTerminalIto (C := Columns (d := d)) (E := Physical (d := d)) F μ H :=
  HilbertTerminalIto.terminalIto F μ H VectorWhiteCoordinates.basis
    (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis)

variable (N : FiniteScalarIto.Family F μ H (d × HaarNode))
  (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ U)
  (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

/-- The actual covariance-adapted vector stochastic convolution exists
at every deterministic terminal time as a native `L²` random variable. -/
def value (t : ℝ≥0) (ht : t ≤ H) : Lp (Physical (d := d)) 2 μ :=
  (terminalIto N).integral (MatrixFixedHaarInput.input F μ H U hU Q hUpper hQ t ht)

theorem adapted (t : ℝ≥0) (ht : t ≤ H) :
    ∃ Z : Ω → Physical (d := d), StronglyMeasurable[F t] Z ∧ value N U hU Q hUpper hQ t ht =ᵐ[μ] Z :=
  (terminalIto N).adapted t _ (MatrixFixedHaarInput.input_stopped F μ H U hU Q hUpper hQ t ht)

theorem centered (t : ℝ≥0) (ht : t ≤ H) :
    (∫ ω, value N U hU Q hUpper hQ t ht ω ∂μ) = 0 := (terminalIto N).centered _

theorem energy (t : ℝ≥0) (ht : t ≤ H) :
    ENNReal.ofReal (‖value N U hU Q hUpper hQ t ht‖ ^ 2) =
      ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖kernel ((t : ℝ)-(s : ℝ)) (Q (s,ω))‖ ^ 2) ∂μ ∂timeMeasure H := by
  rw [value, (terminalIto N).isometry_energy]
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod (MatrixFixedHaarInput.input_ae F μ H U hU Q hUpper hQ t ht)] with s hs
  apply lintegral_congr_ae
  filter_upwards [hs] with ω hω
  rw [hω]

theorem energy_bound (hH : (H : ℝ) ≤ 1) (t : ℝ≥0) (ht : t ≤ H) :
    ENNReal.ofReal (‖value N U hU Q hUpper hQ t ht‖ ^ 2) ≤
      ENNReal.ofReal (MatrixFixedHaarInput.constant d U * (2 * (t : ℝ) ^ (1/2 : ℝ))) := by
  rw [energy]
  exact MatrixFixedHaarInput.energy μ H hH U hU Q hUpper t ht

theorem horizon_energy_bound (t : ℝ≥0) (ht : t ≤ H) :
    ENNReal.ofReal (‖value N U hU Q hUpper hQ t ht‖ ^ 2) ≤
      ENNReal.ofReal (MatrixFixedHaarInput.horizonConstant d H U *
        (2 * (t : ℝ) ^ (1/2 : ℝ))) := by
  rw [energy]
  exact MatrixFixedHaarInput.horizon_energy μ H U hU Q hUpper t ht

/-- The exact common-noise difference isometry uses the same actual
infinite Haar family at both terminal times. -/
theorem difference_energy (t s : ℝ≥0) (ht : t ≤ H) (hs : s ≤ H) :
    ENNReal.ofReal (‖value N U hU Q hUpper hQ t ht - value N U hU Q hUpper hQ s hs‖ ^ 2) =
      ∫⁻ r, ∫⁻ ω, ENNReal.ofReal
        (‖kernel ((t : ℝ)-(r : ℝ)) (Q (r,ω)) - kernel ((s : ℝ)-(r : ℝ)) (Q (r,ω))‖ ^ 2)
        ∂μ ∂timeMeasure H := by
  rw [value, value, (terminalIto N).difference_energy]
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod (MatrixFixedHaarInput.input_ae F μ H U hU Q hUpper hQ t ht),
    Measure.ae_ae_of_ae_prod (MatrixFixedHaarInput.input_ae F μ H U hU Q hUpper hQ s hs)] with r hr hr'
  apply lintegral_congr_ae
  filter_upwards [hr, hr'] with ω hω hω'
  rw [hω, hω']

end SHEStochastic.NativeMatrixConvolution
