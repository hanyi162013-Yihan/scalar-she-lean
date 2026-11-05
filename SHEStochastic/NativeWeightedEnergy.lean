module

public import SHEStochastic.WeightedPrimitiveSums
public import SHEStochastic.ContinuousBracket
public import SHEStochastic.L2EnergyContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.NativeWeightedEnergy
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- The ordinary weighted predictable energy, using the original row. -/
def integral (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ r, w r ω * ‖u (r, ω)‖ ^ 2 ∂timeMeasure H

/-- Left weights paired with actual increments of the energy primitive. -/
def sum (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin n, w (unifPart H n i) ω *
    (PredictableBracket.energy u (unifPart H n (i + 1)) ω -
      PredictableBracket.energy u (unifPart H n i) ω)

theorem stronglyMeasurable_sum (u : Process (E := C) F μ H)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w) (n : ℕ) :
    StronglyMeasurable (sum u w n) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  exact ((hw _).mono (F.le _)).mul
    (((PredictableBracket.measurable u _).mono (F.le _) le_rfl).stronglyMeasurable.sub
      ((PredictableBracket.measurable u _).mono (F.le _) le_rfl).stronglyMeasurable)

/-- Continuous bounded adapted weights converge pathwise against the
energy of any predictable L² row. No bound on that row is assumed. -/
theorem tendsto_ae (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ sum u w n ω) Filter.atTop (𝓝 (integral u w ω)) := by
  have hi : Integrable (fun p : ℝ≥0 × Ω ↦ ‖u p‖ ^ 2) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  filter_upwards [hi.prod_left_ae, hc] with ω hiω hcω
  have hi' : Integrable (fun r ↦ ‖u (r, ω)‖ ^ 2) (MathFin.ItoIntegralCLM.timeMeasure_T H) := by
    simpa only [timeMeasure_eq] using hiω
  have ht := WeightedPrimitiveSums.tendsto H (fun r ↦ ‖u (r, ω)‖ ^ 2)
    (fun r ↦ w r ω) hi' hcω B hB (fun t ↦ hwb t ω)
  have hs (n : ℕ) : sum u w n ω = ∑ k ∈ Finset.range n, w (unifPart H n k) ω *
      (PredictableBracket.energy u (unifPart H n (k + 1)) ω -
        PredictableBracket.energy u (unifPart H n k) ω) :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ w (unifPart H n k) ω *
      (PredictableBracket.energy u (unifPart H n (k + 1)) ω -
        PredictableBracket.energy u (unifPart H n k) ω)) n
  simp_rw [hs]
  simpa only [PredictableBracket.energy, WeightedPrimitiveSums.primitive, integral,
    timeMeasure_eq] using ht

theorem tendstoInMeasure (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (hw : StronglyAdapted F w)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    TendstoInMeasure μ (sum u w) Filter.atTop (integral u w) :=
  tendstoInMeasure_of_tendsto_ae (fun n ↦ (stronglyMeasurable_sum u w hw n).aestronglyMeasurable)
    (tendsto_ae u w hc B hB hwb)

theorem integrable (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (hw : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (B : ℝ) (hwb : ∀ t ω, |w t ω| ≤ B) : Integrable (integral u w) μ := by
  have hu := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  have hm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ w p.1 p.2) := by
    simpa only [Function.uncurry_def] using hw.mono (predictable_le_product F)
  exact (hu.bdd_mul hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ by simpa only [Real.norm_eq_abs] using hwb p.1 p.2)).integral_prod_right

/-- Weighted energies are L¹-continuous in the original predictable L²
row, with the same dimension-independent bound as quadratic sums. -/
theorem integral_sub_le (u v : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (hw : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    (∫ ω, |integral u w ω - integral v w ω| ∂μ) ≤
      B * (‖u - v‖ * (‖u‖ + ‖v‖)) := by
  have hu := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  have hv := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)).norm.integrable_sq
  have hm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ w p.1 p.2) := by
    simpa only [Function.uncurry_def] using hw.mono (predictable_le_product F)
  have hwu := hu.bdd_mul hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ by simpa only [Real.norm_eq_abs] using hwb p.1 p.2)
  have hwv := hv.bdd_mul hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ by simpa only [Real.norm_eq_abs] using hwb p.1 p.2)
  have hd : Integrable (fun p : ℝ≥0 × Ω ↦ |‖u p‖ ^ 2 - ‖v p‖ ^ 2|) (energyMeasure μ H) :=
    (hu.sub hv).abs
  calc
    _ ≤ ∫ ω, B * (∫ r, |‖u (r, ω)‖ ^ 2 - ‖v (r, ω)‖ ^ 2| ∂timeMeasure H) ∂μ := by
      apply integral_mono_ae ((integrable u w hw B hwb).sub (integrable v w hw B hwb)).abs
        (hd.integral_prod_right.const_mul B)
      filter_upwards [hwu.prod_left_ae, hwv.prod_left_ae, hd.prod_left_ae] with ω huω hvω hdω
      change |(∫ r, w r ω * ‖u (r, ω)‖ ^ 2 ∂timeMeasure H) -
        (∫ r, w r ω * ‖v (r, ω)‖ ^ 2 ∂timeMeasure H)| ≤ _
      rw [← integral_sub huω hvω, ← integral_const_mul]
      refine abs_integral_le_integral_abs.trans ?_
      apply integral_mono (huω.sub hvω).abs (hdω.const_mul B)
      intro r
      change |w r ω * ‖u (r, ω)‖ ^ 2 - w r ω * ‖v (r, ω)‖ ^ 2| ≤ _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_right (hwb r ω) (abs_nonneg _)
    _ = B * ∫ p, |‖u p‖ ^ 2 - ‖v p‖ ^ 2| ∂energyMeasure μ H := by
      rw [integral_const_mul, ← integral_prod_symm _ hd]
      rfl
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      rw [integral_trim (predictable_le_product F)
        (by simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.pow_apply] using
          (((Lp.stronglyMeasurable u).norm.pow 2).sub
            ((Lp.stronglyMeasurable v).norm.pow 2)).norm)]
      exact L2EnergyContinuity.integral_sub_le u v

/-- One integrable bound controls every left-weighted energy sum. -/
theorem sum_bound (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    ∀ᵐ ω ∂μ, ∀ n, |sum u w n ω| ≤ B * StochasticExponential.bracket F μ H u ω := by
  have hi : Integrable (fun p : ℝ≥0 × Ω ↦ ‖u p‖ ^ 2) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  filter_upwards [hi.prod_left_ae, PredictableBracket.continuous_monotone u] with ω hiω hmω
  intro n
  have hτ := MathFin.ItoIntegralBrownian.unifPart_mono H n
  have hpos (i : Fin n) : 0 ≤ PredictableBracket.energy u (unifPart H n (i + 1)) ω -
      PredictableBracket.energy u (unifPart H n i) ω := sub_nonneg.mpr (hmω.2 (hτ (Nat.le_succ _)))
  have hs : (∑ i : Fin n, (PredictableBracket.energy u (unifPart H n (i + 1)) ω -
      PredictableBracket.energy u (unifPart H n i) ω)) = PredictableBracket.energy u (unifPart H n n) ω := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ PredictableBracket.energy u (unifPart H n (i + 1)) ω -
      PredictableBracket.energy u (unifPart H n i) ω),
      Finset.sum_range_sub (fun i ↦ PredictableBracket.energy u (unifPart H n i) ω)]
    simp [unifPart, PredictableBracket.energy]
  have he : PredictableBracket.energy u (unifPart H n n) ω ≤ StochasticExponential.bracket F μ H u ω := by
    exact integral_mono (hiω.indicator measurableSet_Iio) hiω
      (fun r ↦ Set.indicator_le_self' (fun _ _ ↦ sq_nonneg _) r)
  calc
    _ ≤ ∑ i : Fin n, |w (unifPart H n i) ω *
        (PredictableBracket.energy u (unifPart H n (i + 1)) ω -
          PredictableBracket.energy u (unifPart H n i) ω)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, B * (PredictableBracket.energy u (unifPart H n (i + 1)) ω -
        PredictableBracket.energy u (unifPart H n i) ω) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hpos i)]
      exact mul_le_mul_of_nonneg_right (hwb _ ω) (hpos i)
    _ = B * PredictableBracket.energy u (unifPart H n n) ω := by rw [← Finset.mul_sum, hs]
    _ ≤ _ := mul_le_mul_of_nonneg_left he hB

theorem integrable_sum (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (hw : StronglyAdapted F w) (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) (n : ℕ) :
    Integrable (sum u w n) μ := by
  apply ((StochasticExponential.bracket_integrable F μ H u).const_mul B).mono'
    (stronglyMeasurable_sum u w hw n).aestronglyMeasurable
  filter_upwards [sum_bound u w B hB hwb] with ω hω
  simpa only [Real.norm_eq_abs] using hω n

/-- The energy Riemann sums converge in L¹, even for unbounded L² rows.
The only dominating variable is the original integrable total energy. -/
theorem tendsto_integral_abs_sub (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (hw : StronglyAdapted F w)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    Filter.Tendsto (fun n ↦ ∫ ω, |sum u w n ω - integral u w ω| ∂μ) Filter.atTop (𝓝 0) := by
  have ht := tendsto_ae u w hc B hB hwb
  have hb := sum_bound u w B hB hwb
  have hmeas := aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun n ↦ (stronglyMeasurable_sum u w hw n).aestronglyMeasurable) ht
  have hlimb : ∀ᵐ ω ∂μ, |integral u w ω| ≤ B * StochasticExponential.bracket F μ H u ω := by
    filter_upwards [ht, hb] with ω htω hbω
    exact le_of_tendsto htω.abs (Filter.Eventually.of_forall hbω)
  have hdom (n : ℕ) : ∀ᵐ ω ∂μ, ‖|sum u w n ω - integral u w ω|‖ ≤
      (2 * B) * StochasticExponential.bracket F μ H u ω := by
    filter_upwards [hb, hlimb] with ω hbω hlω
    rw [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (by nlinarith [hbω n])
  have hpt : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ |sum u w n ω - integral u w ω|)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ht] with ω htω
    simpa only [sub_self, abs_zero] using (htω.sub_const (integral u w ω)).abs
  simpa only [integral_zero, Real.norm_eq_abs, Pi.sub_apply] using tendsto_integral_of_dominated_convergence
    (fun ω ↦ (2 * B) * StochasticExponential.bracket F μ H u ω)
    (fun n ↦ ((stronglyMeasurable_sum u w hw n).aestronglyMeasurable.sub hmeas).norm)
    ((StochasticExponential.bracket_integrable F μ H u).const_mul (2 * B)) hdom hpt

end SHEStochastic.NativeWeightedEnergy
