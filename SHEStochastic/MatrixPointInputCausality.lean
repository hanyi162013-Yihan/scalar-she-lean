module

public import SHEStochastic.MatrixPointTargetContinuity
public import SHEStochastic.NativeInputPairing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.MatrixPointInputCausality
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {Ω d : Type*} [mΩ : MeasurableSpace Ω] [Fintype d] [DecidableEq d]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩

/-- Causality makes stopping at the point target redundant. The value
at zero heat age is zero in the original native input space. -/
theorem process_self (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (cap : ℝ) (hcap : 0 ≤ cap)
    (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ cap)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
    (s : ℝ≥0) (hs : s ≤ H) (x : HeatCircle) (i : d) :
    @Eq (Process (E := Input (d := d)) F μ H)
      (show Process (E := Input (d := d)) F μ H from
        MatrixPointTargetContinuity.process F μ H hH cap hcap Q hUpper hQ s s hs x i)
      (show Process (E := Input (d := d)) F μ H from
        MatrixPointHeatInput.input F μ H hH cap hcap Q hUpper hQ s hs x i) := by
  apply NativeInputPairing.process_ext
  filter_upwards [MatrixPointTargetContinuity.process_ae F μ H hH cap hcap Q hUpper hQ s s hs x i,
    MatrixPointHeatInput.input_ae F μ H hH cap hcap Q hUpper hQ s hs x i] with p hp hi
  rw [hp,hi]
  split_ifs with h
  · rfl
  · exact (MatrixPointHeatInput.row_zero (by linarith [not_lt.mp h]) (Q p) x i).symm

end SHEStochastic.MatrixPointInputCausality
