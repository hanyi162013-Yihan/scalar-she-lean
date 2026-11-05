module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.KernelUniformMoment
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω Y E : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Kernel Ω Y) [IsMarkovKernel κ]

/-- A Borel observable with a uniform conditional moment has the same
moment on the actual kernel product. This is ordinary Tonelli, with no
conditional choice of versions or random evaluation assumption. -/
theorem memLp {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ⊤)
    (X : Ω × Y → E) (hX : Measurable X) (C : ℝ≥0∞) (hC : C < ⊤)
    (hbound : ∀ᵐ ω ∂μ, (∫⁻ y, ‖X (ω,y)‖ₑ ^ p.toReal ∂κ ω) ≤ C) :
    MemLp X p (μ ⊗ₘ κ) := by
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpTop hX.aestronglyMeasurable).mpr
  rw [Measure.lintegral_compProd (hX.enorm.pow_const _)]
  calc
    _ ≤ ∫⁻ _ : Ω, C ∂μ := lintegral_mono_ae hbound
    _ = C := by simp
    _ < ⊤ := hC

theorem memLp_nonneg_nat (p : ℕ) (hp : p ≠ 0) (X : Ω × Y → ℝ)
    (hX : Measurable X) (h0 : ∀ z, 0 ≤ X z) (C : ℝ≥0∞) (hC : C < ⊤)
    (hbound : ∀ᵐ ω ∂μ, (∫⁻ y, ENNReal.ofReal (X (ω,y)^p) ∂κ ω) ≤ C) :
    MemLp X p (μ ⊗ₘ κ) := by
  have he (z : Ω × Y) : ‖X z‖ₑ ^ (p : ℝ≥0∞).toReal = ENNReal.ofReal (X z^p) := by
    rw [ENNReal.toReal_natCast, ENNReal.rpow_natCast, ← ofReal_norm,
      Real.norm_of_nonneg (h0 z), ← ENNReal.ofReal_pow (h0 z)]
  apply memLp μ κ (by exact_mod_cast hp) (by simp) X hX C hC
  exact hbound.mono fun ω hω ↦ by simpa only [he] using hω

end SHEStochastic.KernelUniformMoment
