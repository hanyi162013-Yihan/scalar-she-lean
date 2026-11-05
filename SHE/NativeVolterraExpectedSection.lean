module
public import SHE.NativeWeightedVolterraEnergy
public import SHE.NativeVolterraFields
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeVolterraExpectedSection
open MeasureTheory Set PredictableL2 LowBands
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual fixed-target weighted native drift energy is bounded by
full-horizon input energy. This form needs no target-process version. -/
theorem bound (μ : Measure Ω) [SFinite μ] (H : ℝ≥0) {Λ γ : ℝ}
    (hΛ : 0 ≤ Λ) (hγ : 0 < γ)
    (U : ℝ≥0 → Ω → StateL2) (hU : Measurable (Function.uncurry U))
    (hmem : ∀ω, MemLp (fun s : ℝ≥0 => Real.exp (-γ*(s:ℝ)) • U s ω) 2 (timeMeasure H))
    (t : ℝ≥0) (ht : t ≤ H) :
    (∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ)) *
      ‖NativeClock.volterra Λ (fun s => U s ω) t‖^2) ∂μ) ≤
    ENNReal.ofReal (1/(2*(Λ+γ))) *
      (∫⁻s, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) ∂μ ∂timeMeasure H) := by
  let c : ℝ := 1/(2*(Λ+γ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hm : Measurable (fun p : ℝ≥0 × Ω => ENNReal.ofReal
      (Real.exp (-2*γ*(p.1:ℝ))*‖U p.1 p.2‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((((measurable_coe_nnreal_real.comp measurable_fst).const_mul (-2*γ)).exp).mul
        (hU.norm.pow_const 2))
  have htm : timeMeasure t ≤ timeMeasure H := by
    rw [← timeMeasure_restrict ht]
    exact Measure.restrict_le_self
  have hb (ω : Ω) :
      ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖NativeClock.volterra Λ (fun s => U s ω) t‖^2) ≤
        ENNReal.ofReal c *
          (∫⁻s, ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) ∂timeMeasure H) := by
    have hft : MemLp (fun s : ℝ≥0 => Real.exp (-γ*(s:ℝ)) • U s ω) 2 (timeMeasure t) :=
      (hmem ω).mono_measure htm
    have hi : Integrable (fun s : ℝ≥0 => Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) (timeMeasure t) := by
      simpa only [NativeWeightedVolterra.norm_weight_sq] using hft.norm.integrable_sq
    have hh := ENNReal.ofReal_le_ofReal
      (NativeWeightedVolterra.section_energy hΛ hγ t (fun s => U s ω) hft)
    rw [ENNReal.ofReal_mul hc, ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ (fun s => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))] at hh
    exact hh.trans (mul_le_mul_right (lintegral_mono' htm le_rfl) (ENNReal.ofReal c))
  calc
    _ ≤ ∫⁻ω, ENNReal.ofReal c *
        (∫⁻s, ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) ∂timeMeasure H) ∂μ := lintegral_mono hb
    _ = ENNReal.ofReal c *
        (∫⁻ω, ∫⁻s, ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) ∂timeMeasure H ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal c * z)
      (lintegral_lintegral_swap hm.aemeasurable).symm
end SHE.NativeVolterraExpectedSection
