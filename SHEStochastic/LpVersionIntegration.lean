module

public import SHE.LpIntegralFubini

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.LpVersionIntegration
open MeasureTheory Filter
open scoped ENNReal

/-- A jointly measurable version of an integrable L2-valued family is
jointly L1-integrable on a finite measure space. This discharges the version
integrability premise of the existing Lp/stochastic Fubini theorem. -/
theorem integrable {A Ω E : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure A) [SFinite ν]
    (Z : A → Lp E 2 μ) (hZ : Integrable Z ν)
    (raw : A × Ω → E) (hm : AEStronglyMeasurable raw (ν.prod μ))
    (he : ∀ᵐ a ∂ν, Z a =ᵐ[μ] fun ω ↦ raw (a, ω)) : Integrable raw (ν.prod μ) := by
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [he] with a ha
    exact ((Lp.memLp (Z a)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).congr ha
  · apply (hZ.norm.const_mul (Real.sqrt (μ.real Set.univ))).mono' hm.norm.integral_prod_right'
    filter_upwards [he] with a ha
    calc
      ‖∫ ω, ‖raw (a, ω)‖ ∂μ‖ = ∫ ω, ‖raw (a, ω)‖ ∂μ :=
        Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
      _ = ∫ ω, ‖Z a ω‖ ∂μ := integral_congr_ae (ha.mono fun _ h ↦ congrArg norm h.symm)
      _ ≤ Real.sqrt (μ.real Set.univ) * ‖Z a‖ := SHE.LpIntegralFubini.integral_norm_le_norm μ (Z a)

end SHEStochastic.LpVersionIntegration
