module

public import SHEStochastic.FiniteItoIntervalEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.FiniteItoIntervalTime
open MeasureTheory Set SHE SHE.PredictableL2 SHE.GaussianItoTest
open scoped NNReal Topology

variable {Ω : Type*} {n : ℕ}

/-- The time derivative of the clipped test, evaluated on the stopped
path, is exactly the original time derivative inside the interval. -/
theorem derivative_eq (a b : ℝ≥0) (dG : ℝ → State n → ℝ)
    (Y : ℝ≥0 × Ω → State n) (ω : Ω) (r : ℝ≥0) :
    FiniteItoTestExtension.derivative a b dG r (FiniteItoStoppedVersions.stopped Y b (r, ω)) =
      (Ioo a b).indicator (fun r ↦ dG r (Y (r, ω))) r := by
  by_cases hr : r ∈ Ioo a b
  · have hr' : (r : ℝ) ∈ Ioo (a : ℝ) (b : ℝ) := by exact_mod_cast hr
    simp only [FiniteItoTestExtension.derivative, Set.indicator_of_mem hr', Set.indicator_of_mem hr,
      FiniteItoStoppedVersions.stopped, min_eq_left hr.2.le]
  · have hr' : (r : ℝ) ∉ Ioo (a : ℝ) (b : ℝ) := by exact_mod_cast hr
    simp only [FiniteItoTestExtension.derivative, Set.indicator_of_notMem hr', Set.indicator_of_notMem hr]

theorem integral_eq (H a b : ℝ≥0) (dG : ℝ → State n → ℝ)
    (Y : ℝ≥0 × Ω → State n) (ω : Ω) :
    (∫ r, FiniteItoTestExtension.derivative a b dG r
      (FiniteItoStoppedVersions.stopped Y b (r, ω)) ∂timeMeasure H) =
      ∫ r, (Ioc a b).indicator (fun r ↦ dG r (Y (r, ω))) r ∂timeMeasure H := by
  simp_rw [derivative_eq]
  rw [integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioc,
    Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo a b =ᵐ[timeMeasure H] Ioc a b)]

/-- The original time derivative restricted to the requested interval
is genuinely integrable along every continuous state path. -/
theorem integrable_derivative (H a b : ℝ≥0) (G dG : ℝ → State n → ℝ)
    (hG : RegularTest (a : ℝ) (b : ℝ) G dG) (x : ℝ≥0 → State n) (hx : Continuous x) :
    Integrable ((Ioc a b).indicator (fun r ↦ dG r (x r))) (timeMeasure H) := by
  obtain ⟨v, hv, hve⟩ := hG.derivative_envelope
  let q : ℝ → ℝ := fun r ↦ dG r (x r.toNNReal)
  have hq : Measurable q := hG.derivative_measurable.comp
    (measurable_id.prodMk (hx.measurable.comp measurable_real_toNNReal))
  have hi : IntegrableOn q (Ioc (a : ℝ) (b : ℝ)) (volume : Measure ℝ) := by
    apply hv.1.mono' hq.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := (a : ℝ)) (b := (b : ℝ))),
      (volume.restrict (Ioc (a : ℝ) (b : ℝ))).ae_ne (b : ℝ)] with r hr hne
    exact hve r ⟨hr.1, lt_of_le_of_ne hr.2 hne⟩ _
  have hfull := (integrable_indicator_iff measurableSet_Ioc).mpr hi
  have ht := (timeMeasurePreserving H).integrable_comp_of_integrable
    (hfull.mono_measure (Measure.restrict_le_self (s := Ioc (0 : ℝ) (H : ℝ))))
  convert ht using 1
  funext r
  simp only [Set.indicator_apply, Set.mem_Ioc, NNReal.coe_lt_coe, NNReal.coe_le_coe,
    Function.comp_apply, Real.toNNReal_coe, q]

end SHEStochastic.FiniteItoIntervalTime
