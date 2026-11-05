module

public import SHEStochastic.KolmogorovFieldControl
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.KolmogorovFieldMaximum
open MeasureTheory ProbabilityTheory Set Metric KolmogorovFieldControl
open scoped NNReal ENNReal
variable {T V : Type*} [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [NormedAddCommGroup V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The quantitative Chentsov control gives this explicit supremum
bound for a continuous field anchored at zero. -/
def amplitude (p : ℝ) (α R : ℝ≥0) : ℝ :=
  (((R : ℝ≥0∞)^p⁻¹).toNNReal : ℝ)*(max 1 (Metric.diam (Set.univ : Set T)))^(α : ℝ)

theorem norm_le (D : Set T) (hD : Dense D) {c : ℝ≥0∞} {d p : ℝ} {α : ℝ≥0}
    (hT : HasCoveringExponent (Set.univ : Set T) c d) (hp : 0<p) (hα : 0<α)
    (f : C(T,V)) (t₀ : T) (hz : f t₀=0) (R : ℝ≥0) (hcontrol : control D p α f≤R) :
    ‖f‖≤amplitude (T := T) p α R := by
  apply (ContinuousMap.norm_le f (by dsimp [amplitude];positivity)).mpr
  intro t
  have hb := KolmogorovFieldControl.distance_bound_of_le D p α hD hT hp hα f R hcontrol t t₀
  rw [hz,dist_zero_right] at hb
  have hd : dist t t₀≤max 1 (Metric.diam (Set.univ : Set T)) :=
    (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ t) (mem_univ t₀)).trans (le_max_right _ _)
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hd α.coe_nonneg) (NNReal.coe_nonneg _))

/-- An explicit supremum tail estimate follows directly from the
existing quantitative Chentsov theorem and Markov inequality. No
supremum moment or compactness premise is added. -/
theorem tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → C(T,V)) (hY : Measurable Y) (t₀ : T) (hzero : ∀ᵐ ω ∂μ,Y ω t₀=0)
    (D : Set T) (hDcount : D.Countable) (hDdense : Dense D)
    {c : ℝ≥0∞} {d p q : ℝ} {M α : ℝ≥0}
    (hT : HasCoveringExponent (Set.univ : Set T) c d) (hd : 0<d) (hp : 0<p) (hdq : d<q) (hα : 0<α)
    (hX : IsKolmogorovProcess (fun t ω => Y ω t) μ p q M) (R : ℝ≥0) (hR : 0<R) :
    μ {ω | amplitude (T := T) p α R<‖Y ω‖}≤
      ((M : ℝ≥0∞)*constL c d p q α)/(R : ℝ≥0∞) := by
  letI : Countable (D∩Set.univ : Set T) := hDcount.mono inter_subset_left
  have hm := (KolmogorovFieldControl.measurable_control (V := V) D p α hDcount).comp hY
  have hi : (∫⁻ ω,control D p α (Y ω) ∂μ)≤(M : ℝ≥0∞)*constL c d p q α :=
    countable_kolmogorov_chentsov hT hX.IsAEKolmogorovProcess hd hdq
      (show (0 : ℝ)<α from hα) (D∩Set.univ) (subset_univ _)
  calc
    _ ≤ μ {ω | (R : ℝ≥0∞)≤control D p α (Y ω)} := by
      apply measure_mono_ae
      filter_upwards [hzero] with ω hz hbad
      exact (lt_of_not_ge (fun hc => not_le_of_gt hbad (norm_le D hDdense hT hp hα (Y ω) t₀ hz R hc))).le
    _ ≤ (∫⁻ ω,control D p α (Y ω) ∂μ)/(R : ℝ≥0∞) :=
      meas_ge_le_lintegral_div hm.aemeasurable (by exact_mod_cast hR.ne') ENNReal.coe_ne_top
    _ ≤ _ := ENNReal.div_le_div_right hi _

end SHEStochastic.KolmogorovFieldMaximum
