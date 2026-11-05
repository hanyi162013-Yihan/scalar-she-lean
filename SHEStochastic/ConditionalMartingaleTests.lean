module

public import SHEStochastic.BCFL1PastTesting
public import SHEStochastic.ContinuousStoppedMartingaleTests
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.ConditionalMartingaleTests
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Every fixed bounded past test retains its martingale identity under
almost every conditional initial-state law. Countable generators can
then assemble one event supporting the full conditional martingale. -/
theorem weighted_increment_integrable {Ω E : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (Z : Ω → E) (hZ₀ : Measurable[F 0] Z)
    (s t : ℝ≥0) (hst : s ≤ t) (test : Ω → ℝ) (htest : StronglyMeasurable[F s] test)
    (K : ℝ≥0) (hbound : ∀ sample, ‖test sample‖ ≤ K) :
    ∀ᵐ z ∂μ.map Z, (∫ sample, test sample*(M t sample-M s sample) ∂condDistrib id Z μ z) = 0 := by
  have hZ : Measurable Z := hZ₀.mono (F.le 0) le_rfl
  have hZs : Measurable[F s] Z := hZ₀.mono (F.mono zero_le) le_rfl
  let Y (sample : Ω) := test sample*(M t sample-M s sample)
  have hYm : StronglyMeasurable Y := (htest.mono (F.le s)).mul
    (((hM.stronglyAdapted t).mono (F.le t)).sub ((hM.stronglyAdapted s).mono (F.le s)))
  have hY : Integrable Y μ :=
    ((hM.integrable t).sub (hM.integrable s)).bdd_mul
      (htest.mono (F.le s)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun sample => hbound sample))
  have hc : μ[Y | MeasurableSpace.comap Z inferInstance] =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    apply BCFL1PastTesting.condExp_zero μ Z hZ Y hY
    intro f
    have hm : StronglyMeasurable[F s] (fun sample ↦ f (Z sample)*test sample) :=
      (f.continuous.measurable.comp hZs).stronglyMeasurable.mul htest
    have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F M hM s t hst
      (fun sample ↦ f (Z sample)*test sample) hm (‖f‖*K) (fun sample ↦ by
        rw [norm_mul]
        exact mul_le_mul (f.norm_coe_le_norm _) (hbound sample) (norm_nonneg _) (norm_nonneg _))
    calc
      _ = ∫ sample, (f (Z sample)*test sample)*(M t sample-M s sample) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ ↦ (mul_assoc _ _ _).symm
      _ = 0 := hh
  have hi := condExp_ae_eq_integral_condDistrib_id hZ hY
  have hm : Measurable (fun z ↦ ∫ sample, Y sample ∂condDistrib id Z μ z) :=
    (hYm.comp_measurable measurable_snd).integral_kernel_prod_right'.measurable
  exact (ae_map_iff hZ.aemeasurable (measurableSet_eq_fun hm measurable_const)).mpr (hi.symm.trans hc)

/-- Backward-compatible L2 interface; the proof only uses integrability. -/
theorem weighted_increment {Ω E : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ) (_hM2 : ∀ t, MemLp (M t) 2 μ)
    (Z : Ω → E) (hZ₀ : Measurable[F 0] Z)
    (s t : ℝ≥0) (hst : s ≤ t) (test : Ω → ℝ) (htest : StronglyMeasurable[F s] test)
    (K : ℝ≥0) (hbound : ∀ sample, ‖test sample‖ ≤ K) :
    ∀ᵐ z ∂μ.map Z, (∫ sample, test sample*(M t sample-M s sample) ∂condDistrib id Z μ z) = 0 :=
  weighted_increment_integrable μ F M hM Z hZ₀ s t hst test htest K hbound

end SHEStochastic.ConditionalMartingaleTests
