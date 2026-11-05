module

public import SHEStochastic.HilbertSimpleInputs

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.SimplePrimitivePairing
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Integration against a primitive on one time cell. -/
theorem primitive_sub (ν : Measure ℝ≥0) [NullSingletonClass ν] (q : ℝ≥0 → ℝ)
    (hq : Integrable q ν) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ r, (Set.Iio t).indicator q r ∂ν) - (∫ r, (Set.Iio s).indicator q r ∂ν) =
      ∫ r, (Set.Ioc s t).indicator q r ∂ν := by
  rw [← integral_sub (hq.indicator measurableSet_Iio) (hq.indicator measurableSet_Iio)]
  calc
    _ = ∫ r, (Set.Ico s t).indicator q r ∂ν := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro r
      by_cases hs : r < s
      · have ht : r < t := lt_of_lt_of_le hs hst
        simp [Set.indicator_apply, hs, ht, not_le_of_gt hs]
      · by_cases ht : r < t
        · simp [Set.indicator_apply, hs, ht, le_of_not_gt hs]
        · simp [Set.indicator_apply, hs, ht]
    _ = _ := by rw [integral_indicator measurableSet_Ico,
      integral_indicator measurableSet_Ioc, integral_Ico_eq_integral_Ioc]

/-- The finite increment sum of a bounded predictable simple coefficient
against an ordinary primitive equals its time integral. The time-zero
atom of a simple process contributes nothing. -/
theorem simple_pairing {Ω : Type*} [MeasurableSpace Ω]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (ν : Measure ℝ≥0) [NullSingletonClass ν]
    (V : SimpleProcess ℝ F) (q : ℝ≥0 → ℝ) (hq : Integrable q ν) (ω : Ω) :
    (∫ r, V r ω * q r ∂ν) =
      ∑ p ∈ V.value.support, V.value p ω *
        ((∫ r, (Set.Iio p.2).indicator q r ∂ν) -
          (∫ r, (Set.Iio p.1).indicator q r ∂ν)) := by
  have he : (fun r ↦ V r ω * q r) =ᵐ[ν]
      (fun r ↦ ∑ p ∈ V.value.support,
        (Set.Ioc p.1 p.2).indicator (fun r ↦ V.value p ω * q r) r) := by
    filter_upwards [ν.ae_ne 0] with r hr
    rw [SimpleProcess.apply_eq, Set.indicator_of_notMem (by simpa using hr), zero_add,
      Finsupp.sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : r ∈ Set.Ioc p.1 p.2 <;> simp [Set.indicator_apply, h]
  rw [integral_congr_ae he, integral_finsetSum _
    (fun p hp ↦ (hq.const_mul (V.value p ω)).indicator measurableSet_Ioc)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [primitive_sub ν q hq p.1 p.2 (V.le_of_mem_support_value p hp)]
  rw [integral_indicator measurableSet_Ioc, integral_const_mul,
    integral_indicator measurableSet_Ioc]

end SHEStochastic.SimplePrimitivePairing
