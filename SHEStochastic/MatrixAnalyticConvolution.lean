module

public import SHEStochastic.MatrixAnalyticKernel
public import SHEStochastic.NativeMatrixConvolution
public import SHEStochastic.MatrixPointHeatRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixAnalyticConvolution
open MeasureTheory SHE SHE.FiniteHaar SHE.StoppedFourier SHE.PredictableL2 MatrixInfiniteHaar MatrixAnalyticKernel
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩

/-- Bounded heat observations of the actual physical-clock kernel are
the literal point rows at the original, unchanged terminal target. -/
theorem observed {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (P : Profile d) (x : HeatCircle) (i : d) :
    HilbertColumns.mapCLM (innerSL ℝ (VectorPointHeatTest.test ε x i)) (kernel t P)=
      MatrixPointHeatRows.row (ε+t) P x i := by
  rw [kernel,MatrixCausalHeatRows.mapped_kernel,MatrixCausalHeatRows.row,
    if_pos (div_pos ht NativeHeatObservation.timeScale_pos),MatrixHaarHeatRows.row]
  change (factor P).adjoint ((VectorAnalyticHeat.heat t).adjoint (VectorPointHeatTest.test ε x i))=_
  rw [VectorAnalyticHeat.test hε ht.le,MatrixPointHeatRows.row,if_pos (by linarith : 0 < ε+t)]

theorem stopped_observed {T t : ℝ} (ht : t < T) (r : ℝ) (P : Profile d) (x : HeatCircle) (i : d) :
    HilbertColumns.mapCLM (innerSL ℝ (VectorPointHeatTest.test (T-t) x i)) (kernel (t-r) P)=
      if r < t then MatrixPointHeatRows.row (T-r) P x i else 0 := by
  by_cases hr : r < t
  · rw [if_pos hr,observed (sub_pos.mpr ht) (sub_pos.mpr hr)]
    rw [show T-t+(t-r)=T-r by ring]
  · rw [if_neg hr,MatrixAnalyticKernel.zero (sub_nonpos.mpr (not_lt.mp hr)),map_zero]

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (U : ℝ) (hU : 0 ≤ U)
    (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ U)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

include hH hU hUpper hQ in
theorem memLp (t : ℝ≥0) (ht : t ≤ H) :
    @MemLp _ _ F.predictable _ _ (fun p : ℝ≥0 × Ω => kernel ((t : ℝ)-(p.1 : ℝ)) (Q p)) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  apply CausalKernelInput.memLp F μ H hH (fun τ p => kernel τ (Q p))
    (fun τ hτ p => MatrixAnalyticKernel.zero hτ (Q p)) (constant d U) (constant_nonneg hU) _ t ht
    (MatrixAnalyticKernel.predictable F Q hQ t)
  intro τ hτ hτ1 p
  exact (small_bound hτ hτ1 (Q p)).trans
    (mul_le_mul_of_nonneg_right (constant_mono (hUpper p)) (Real.rpow_nonneg hτ.le _))

def input (t : ℝ≥0) (ht : t ≤ H) : Process (E := MatrixHaarKernel.Columns (d := d)) F μ H :=
  (memLp F μ H hH U hU Q hUpper hQ t ht).toLp _

theorem input_ae (t : ℝ≥0) (ht : t ≤ H) :
    input F μ H hH U hU Q hUpper hQ t ht =ᵐ[energyMeasure μ H]
      fun p : ℝ≥0 × Ω => kernel ((t : ℝ)-(p.1 : ℝ)) (Q p) :=
  ae_eq_of_ae_eq_trim (memLp F μ H hH U hU Q hUpper hQ t ht).coeFn_toLp

/-- Actual vector stochastic convolution with the paper's analytic
heat generator, built with the same native Hilbert Itô isometry. -/
def value (N : FiniteScalarIto.Family F μ H (d × HaarNode)) (t : ℝ≥0) (ht : t ≤ H) :
    Lp (Physical (d := d)) 2 μ :=
  (NativeMatrixConvolution.terminalIto N).integral (input F μ H hH U hU Q hUpper hQ t ht)

theorem centered (N : FiniteScalarIto.Family F μ H (d × HaarNode)) (t : ℝ≥0) (ht : t ≤ H) :
    (∫ ω, value F μ H hH U hU Q hUpper hQ N t ht ω ∂μ)=0 :=
  (NativeMatrixConvolution.terminalIto N).centered _

end SHEStochastic.MatrixAnalyticConvolution
