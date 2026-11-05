module

public import SHEStochastic.ContinuousBracket
public import SHEStochastic.HilbertSimplePartition
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.TimeEnergyCap
open MeasureTheory
open scoped NNReal ENNReal

variable {H : ℝ≥0}
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

def primitive (q : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ∫ r, (Set.Iio t).indicator q r ∂νt

theorem monotone_primitive {q : ℝ≥0 → ℝ} (hq : Integrable q νt) (hq0 : ∀ r, 0 ≤ q r) :
    Monotone (primitive (H := H) q) := by
  intro a b hab
  exact integral_mono (hq.indicator measurableSet_Iio) (hq.indicator measurableSet_Iio)
    (Set.indicator_le_indicator_of_subset (Set.Iio_subset_Iio hab) hq0)

theorem continuous_primitive {q : ℝ≥0 → ℝ} (hq : Integrable q νt) :
    Continuous (primitive (H := H) q) := by
  letI : NullSingletonClass MathFin.ItoIntegralL2.timeMeasure :=
    ⟨MathFin.ItoIntegralL2.timeMeasure_singleton⟩
  haveI : NullSingletonClass νt := by dsimp [MathFin.ItoIntegralCLM.timeMeasure_T]; infer_instance
  exact PredictableBracket.continuous_primitive hq

theorem primitive_zero (q : ℝ≥0 → ℝ) : primitive (H := H) q 0 = 0 := by
  simp [primitive]

theorem primitive_terminal (q : ℝ≥0 → ℝ) :
    primitive (H := H) q (H + 1) = ∫ r, q r ∂νt := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := 0) (b := H))] with r hr
  exact Set.indicator_of_mem (show r ∈ Set.Iio (H + 1) from
    hr.2.trans_lt (lt_add_one H)) q

/-- Stopping an integrable nonnegative time density before its running
energy reaches `K` leaves at most `K` energy. Only continuity of the
Lebesgue primitive is used, not continuity of the density. -/
theorem capped_integral_le {q : ℝ≥0 → ℝ} (hq : Integrable q νt) (hq0 : ∀ r, 0 ≤ q r)
    (K : ℝ) (hK : 0 ≤ K) :
    (∫ r, {r | primitive (H := H) q r < K}.indicator q r ∂νt) ≤
      min (∫ r, q r ∂νt) K := by
  let A := primitive (H := H) q
  have hc : Continuous A := continuous_primitive hq
  have hm : Monotone A := monotone_primitive hq hq0
  have hi : Integrable ({r | A r < K}.indicator q) νt :=
    hq.indicator (measurableSet_lt hc.measurable measurable_const)
  have htotal : (∫ r, {r | A r < K}.indicator q r ∂νt) ≤ ∫ r, q r ∂νt :=
    integral_mono hi hq (fun r ↦ by
      by_cases hr : A r < K <;> simp [Set.indicator, hr, hq0 r])
  apply le_min htotal
  by_cases hE : (∫ r, q r ∂νt) ≤ K
  · exact htotal.trans hE
  · have hKmem : K ∈ Set.Icc (A 0) (A (H + 1)) := by
      change K ∈ Set.Icc (primitive q 0) (primitive q (H + 1))
      rw [primitive_zero, primitive_terminal]
      exact ⟨hK, (lt_of_not_ge hE).le⟩
    obtain ⟨τ, hτ, hAτ⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ H + 1 from zero_le)
      hc.continuousOn hKmem
    have hsub : {r | A r < K} ⊆ Set.Iio τ := by
      intro r hr
      by_contra hn
      have hτr : τ ≤ r := le_of_not_gt hn
      exact (not_lt.mpr ((hm hτr).trans_eq' hAτ)) hr
    calc
      _ ≤ ∫ r, (Set.Iio τ).indicator q r ∂νt :=
        integral_mono hi (hq.indicator measurableSet_Iio)
          (Set.indicator_le_indicator_of_subset hsub hq0)
      _ = K := hAτ

end SHEStochastic.TimeEnergyCap
