module

public import SHEStochastic.PredictableBracket
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.PredictableBracket
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

/-- An integrable density on an atomless time measure has a continuous
primitive. This reuses dominated convergence at each time endpoint. -/
theorem continuous_primitive {ν : Measure ℝ≥0} [NullSingletonClass ν]
    {q : ℝ≥0 → ℝ} (hq : Integrable q ν) :
    Continuous (fun t : ℝ≥0 ↦ ∫ s, (Set.Iio t).indicator q s ∂ν) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_of_dominated
    (Filter.Eventually.of_forall fun r ↦ (hq.indicator measurableSet_Iio).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun r ↦ Filter.Eventually.of_forall fun s ↦
      norm_indicator_le_norm_self q s) hq.norm
  filter_upwards [ν.ae_ne t] with s hne
  by_cases hst : s < t
  · have he : (fun r : ℝ≥0 ↦ (Set.Iio r).indicator q s) =ᶠ[𝓝 t] (fun _ ↦ q s) := by
      filter_upwards [eventually_gt_nhds hst] with r hr
      exact Set.indicator_of_mem (show s ∈ Set.Iio r from hr) q
    exact continuousAt_const.congr_of_eventuallyEq he
  · have hts : t < s := lt_of_le_of_ne (le_of_not_gt hst) hne.symm
    have he : (fun r : ℝ≥0 ↦ (Set.Iio r).indicator q s) =ᶠ[𝓝 t] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hts] with r hr
      exact Set.indicator_of_notMem (show s ∉ Set.Iio r from not_lt.mpr hr.le) q
    exact continuousAt_const.congr_of_eventuallyEq he

variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- The energy has continuous increasing paths on a single full-measure
event; this is pathwise energy, not merely continuity at each fixed time. -/
theorem continuous_monotone (u : Process (E := C) F μ H) :
    ∀ᵐ ω ∂μ, Continuous (fun t ↦ energy u t ω) ∧ Monotone (fun t ↦ energy u t ω) := by
  have hi : Integrable (fun p : ℝ≥0 × Ω ↦ ‖u p‖ ^ 2) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  filter_upwards [hi.prod_left_ae] with ω hω
  refine ⟨continuous_primitive hω, fun a b hab ↦ ?_⟩
  apply integral_mono (hω.indicator measurableSet_Iio) (hω.indicator measurableSet_Iio)
  intro s
  exact Set.indicator_le_indicator_of_subset (Set.Iio_subset_Iio hab) (fun s ↦ sq_nonneg _) s

end SHEStochastic.PredictableBracket
