module

public import SHE.DampedTerminalMoments

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.DampedUnitTimeMoments
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal
local instance haarUnitTimeMoments_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarUnitTimeMoments_stateSigma : MeasurableSpace LowBands.StateL2 := borel LowBands.StateL2
local instance haarUnitTimeMoments_stateBorel : BorelSpace LowBands.StateL2 := ⟨rfl⟩

def clock (h : ℝ≥0) (r : ℝ) : ℝ≥0 := min h (h*r.toNNReal)

theorem clock_bound (h : ℝ≥0) (r : ℝ) : clock h r ≤ h := min_le_left _ _

theorem clock_coe (h : ℝ≥0) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    (clock h r:ℝ)=(h:ℝ)*r := by
  have hc : ((h*r.toNNReal : ℝ≥0):ℝ) ≤ (h:ℝ) := by
    rw [NNReal.coe_mul,Real.coe_toNNReal _ hr.1]
    nlinarith [hr.2, h.2]
  have hc' : h*r.toNNReal ≤ h := by exact_mod_cast hc
  rw [clock,min_eq_right hc',NNReal.coe_mul,Real.coe_toNNReal _ hr.1]

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)

/-- A genuine real-time family whose restriction to [0,1] is the actual
fixed-terminal stochastic convolution at physical time h*r. -/
def process (r : ℝ) (ω : Ω) : LowBands.StateL2 :=
  DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I (clock h r) (clock_bound h r) ω

theorem process_measurable (r : ℝ) : Measurable (process 𝓕 μ h hh hΛ hell hM f hf I r) :=
  (Lp.stronglyMeasurable (DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I
    (clock h r) (clock_bound h r))).measurable

/-- The actual real-unit-interval moment condition, ready for a proved
Kolmogorov continuous-modification theorem. No heat or stopping premise
remains in this condition. -/
theorem increment_moment16 (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    (∫⁻ ω,ENNReal.ofReal (‖process 𝓕 μ h hh hΛ hell hM f hf I s ω-
      process 𝓕 μ h hh hΛ hell hM f hf I t ω‖^16) ∂μ) ≤
      ENNReal.ofReal (DampedTerminalMoments.momentConstant B Λ M*|s-t|^2) := by
  have hb := DampedTerminalMoments.symmetric_increment_moment16 𝓕 μ h hh hΛ hell hM f hf I B hBDG
    (clock h s) (clock h t) (clock_bound h s) (clock_bound h t)
  have hc : ((clock h s:ℝ)-(clock h t:ℝ))^2 ≤ |s-t|^2 := by
    rw [clock_coe h hs,clock_coe h ht,← mul_sub,mul_pow,sq_abs]
    have hh2 : (h:ℝ)^2 ≤ 1 := by nlinarith [h.2]
    exact (mul_le_mul_of_nonneg_right hh2 (sq_nonneg (s-t))).trans_eq (one_mul _)
  exact hb.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hc (DampedTerminalMoments.momentConstant_nonneg B Λ M)))

end SHE.DampedUnitTimeMoments
