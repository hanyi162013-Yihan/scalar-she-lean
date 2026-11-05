module

public import SHEStochastic.ConditionalBracket

/-! Pathwise bracket bookkeeping for the original predictable L2 input.
Adaptedness reuses Mathlib's predictable inclusion map; no second trace
sigma-algebra construction or stochastic theorem is needed. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.PredictableBracket
open MeasureTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [mΩ : MeasurableSpace Ω] [NormedAddCommGroup C]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- A representative-level time integral, rather than the arbitrary L2
representative of a stopped input. It is measurable in the actual past. -/
def energy (u : Process (E := C) F μ H) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s, (Set.Iio t).indicator (fun s ↦ ‖u (s, ω)‖ ^ 2) s ∂timeMeasure H

/-- Integrating any predictable Banach-valued field before a deterministic
time gives a strongly measurable variable in that time's sigma algebra. -/
theorem stronglyMeasurable_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure ℝ≥0) [SFinite ν] (q : ℝ≥0 × Ω → E)
    (hq : StronglyMeasurable[F.predictable] q) (t : ℝ≥0) :
    StronglyMeasurable[F t]
      (fun ω ↦ ∫ s, (Set.Iio t).indicator (fun s ↦ q (s, ω)) s ∂ν) := by
  letI : MeasurableSpace Ω := F t
  have hclip : @Measurable (ℝ≥0 × Ω) (Set.Iic t × Ω) _
      (Subtype.instMeasurableSpace.prod (F t))
      (fun p ↦ (⟨min p.1 t, min_le_right _ _⟩, p.2)) :=
    ((measurable_fst.min measurable_const).subtype_mk).prodMk
      measurable_snd
  have hmap : @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) _ F.predictable
      (fun p ↦ (min p.1 t, p.2)) := measurable_inclusion_predictable.comp hclip
  have hi := (hq.comp_measurable hmap).indicator
    ((measurableSet_Iio (a := t)).preimage measurable_fst)
  have hm := hi.integral_prod_left' (μ := ν)
  convert hm using 1
  funext ω
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s ↦ by
    by_cases hs : s < t
    · simp [hs, min_eq_left hs.le]
    · simp [hs]

theorem measurable (u : Process (E := C) F μ H) (t : ℝ≥0) :
    Measurable[F t] (energy u t) :=
  (stronglyMeasurable_primitive (F := F) (timeMeasure H) (fun p ↦ ‖u p‖ ^ 2)
    ((Lp.stronglyMeasurable u).norm.pow 2) t).measurable

theorem stopped_eq (u : Process (E := C) F μ H) (t : ℝ≥0) :
    StochasticExponential.bracket F μ H (stop F μ H t u) =ᵐ[μ] energy u t := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (stop_ae F μ H t u)
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  apply integral_congr_ae
  filter_upwards [hω] with s hs
  dsimp only [Prod.swap] at hs
  rw [hs]
  by_cases ht : s < t <;>
    simp [before, Set.indicator, NNReal.coe_lt_coe, ht]

variable [InnerProductSpace ℝ C]

theorem integrable (u : Process (E := C) F μ H) (t : ℝ≥0) :
    Integrable (energy u t) μ :=
  (StochasticExponential.bracket_integrable F μ H _).congr (stopped_eq u t)

/-- The localized bracket really is the increment of the adapted energy
process; deterministic endpoints have zero time measure. -/
theorem band_eq_sub (u : Process (E := C) F μ H) {a b : ℝ≥0} (hab : a ≤ b) :
    StochasticExponential.bracket F μ H (post F μ H a (stop F μ H b u)) =ᵐ[μ]
      fun ω ↦ energy u b ω - energy u a ω := by
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (post_ae F μ H a (stop F μ H b u))
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (stop_ae F μ H b u)
  have hi : Integrable (fun p : ℝ≥0 × Ω ↦ ‖u p‖ ^ 2) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  filter_upwards [Measure.ae_ae_of_ae_prod hp, Measure.ae_ae_of_ae_prod hs,
    hi.prod_left_ae] with ω hp hs hi
  change (∫ s, ‖post F μ H a (stop F μ H b u) (s, ω)‖ ^ 2 ∂timeMeasure H) = _
  rw [energy, energy, ← integral_sub (hi.indicator measurableSet_Iio) (hi.indicator measurableSet_Iio)]
  apply integral_congr_ae
  filter_upwards [hp, hs, (timeMeasure H).ae_ne a] with s hp hs hne
  dsimp only [Prod.swap] at hp hs
  rw [hp]
  by_cases hsa : s < a <;> by_cases hsb : s < b <;> by_cases has : a < s <;>
    simp_all [before, Set.indicator, NNReal.coe_lt_coe] <;>
    (try split_ifs) <;> first | order | simp_all

end SHEStochastic.PredictableBracket
