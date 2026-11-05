module

public import SHEStochastic.RightFrozenTimeSums
public import SHE.PredictableTime
public import SHE.GaussianItoTest
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.FiniteItoTimeCalculus
open MeasureTheory Set SHE.PredictableL2
open scoped NNReal Topology

/-- The native time cell is exactly its physical real-time interval,
including both endpoint conventions. No regularity of the integrand is
needed for this measure identity. -/
theorem clock_cell (H s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) (q : ℝ → ℝ) :
    (∫ r, (Ioc s t).indicator (fun r : ℝ≥0 ↦ q (r : ℝ)) r
      ∂MathFin.ItoIntegralCLM.timeMeasure_T H) = ∫ r in (s : ℝ)..(t : ℝ), q r := by
  rw [← timeMeasure_eq, timeMeasure_integral]
  have he : (fun r : ℝ ↦ (Ioc s t).indicator (fun r : ℝ≥0 ↦ q (r : ℝ)) r.toNNReal) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (H : ℝ))] (Ioc (s : ℝ) (t : ℝ)).indicator q := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := (0 : ℝ)) (b := (H : ℝ)))] with r hr
    have hc := Real.coe_toNNReal r hr.1.le
    have hiff : r.toNNReal ∈ Ioc s t ↔ r ∈ Ioc (s : ℝ) (t : ℝ) := by
      simp only [Set.mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, hc]
    simp only [Set.indicator_apply, hiff, hc]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.mpr (Set.Ioc_subset_Ioc s.coe_nonneg (show (t : ℝ) ≤ H by exact_mod_cast htH)),
    intervalIntegral.integral_of_le (show (s : ℝ) ≤ t by exact_mod_cast hst)]

/-- Absolute continuity and the actual a.e. time derivative give the
primitive identity on every deterministic subinterval. -/
theorem ac_primitive {E : Type*} (H : ℝ≥0) (G q : ℝ → E → ℝ)
    (hG : ∀ z, AbsolutelyContinuousOnInterval (fun r ↦ G r z) 0 (H : ℝ))
    (hd : ∀ᵐ r : ℝ, r ∈ Ioo (0 : ℝ) (H : ℝ) → ∀ z, HasDerivAt (fun r ↦ G r z) (q r z) r)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) (z : E) :
    G t z - G s z = ∫ r, (Ioc s t).indicator (fun r : ℝ≥0 ↦ q r z) r
      ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
  have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hsub : uIcc (s : ℝ) (t : ℝ) ⊆ uIcc (0 : ℝ) (H : ℝ) := by
    rw [uIcc_of_le hstR, uIcc_of_le H.coe_nonneg]
    exact Icc_subset_Icc s.coe_nonneg (by exact_mod_cast htH)
  have hac := (hG z).mono hsub
  have he : deriv (fun r ↦ G r z) =ᵐ[volume.restrict (Ioc (s : ℝ) (t : ℝ))] (fun r ↦ q r z) := by
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc (s : ℝ) (t : ℝ))).ae_ne (t : ℝ)] with r hd hr hne
    exact (hd ⟨s.coe_nonneg.trans_lt hr.1,
      (lt_of_le_of_ne hr.2 hne).trans_le (by exact_mod_cast htH)⟩ z).deriv
  rw [clock_cell H s t hst htH (fun r ↦ q r z), ← hac.integral_deriv_eq_sub]
  exact intervalIntegral.integral_congr_ae_restrict (by simpa only [uIoc_of_le hstR] using he)

/-- The time term for the EXACT regular-test interface. Endpoint values
of the derivative are discarded on a time-null set; integrable envelopes
may be singular at the endpoints. -/
theorem regular_time_sums {n : ℕ} (H : ℝ≥0)
    (G dG : ℝ → SHE.GaussianItoTest.State n → ℝ)
    (hG : SHE.GaussianItoTest.RegularTest 0 (H : ℝ) G dG)
    (x : ℝ≥0 → SHE.GaussianItoTest.State n) (hx : ContinuousOn x (Icc 0 H)) :
    Filter.Tendsto (fun m ↦ ∑ k ∈ Finset.range m,
      (G (MathFin.QuadraticVariationL2.unifPart H m (k + 1))
          (x (MathFin.QuadraticVariationL2.unifPart H m (k + 1))) -
        G (MathFin.QuadraticVariationL2.unifPart H m k)
          (x (MathFin.QuadraticVariationL2.unifPart H m (k + 1))))) Filter.atTop
      (𝓝 (∫ r, dG r (x r) ∂MathFin.ItoIntegralCLM.timeMeasure_T H)) := by
  obtain ⟨v, hv, hve⟩ := hG.derivative_envelope
  let q : ℝ → SHE.GaussianItoTest.State n → ℝ := fun r z ↦ if r < H then dG r z else 0
  have hm (z : SHE.GaussianItoTest.State n) : Measurable (fun r : ℝ≥0 ↦ q r z) := by
    apply Measurable.ite (measurableSet_lt measurable_coe_nnreal_real measurable_const)
      (hG.derivative_measurable.comp (measurable_coe_nnreal_real.prodMk measurable_const)) measurable_const
  have hc (r : ℝ≥0) : Continuous (q r) := by
    dsimp [q]
    split_ifs
    · exact hG.derivative_state_continuous _
    · exact continuous_const
  have hiv : Integrable (fun r : ℝ≥0 ↦ |v r|) (MathFin.ItoIntegralCLM.timeMeasure_T H) := by
    rw [← timeMeasure_eq]
    exact (timeMeasurePreserving H).integrable_comp_of_integrable hv.abs.1
  have hqb (r : ℝ≥0) (hr : r ∈ Ioc 0 H) (z : SHE.GaussianItoTest.State n) : |q r z| ≤ |v r| := by
    dsimp [q]
    split_ifs with h
    · have hb : |dG r z| ≤ v r := by
        simpa only [Real.norm_eq_abs] using hve r ⟨by exact_mod_cast hr.1, h⟩ z
      exact hb.trans (le_abs_self _)
    · exact (abs_zero).le.trans (abs_nonneg _)
  have hqd : ∀ᵐ r : ℝ, r ∈ Ioo (0 : ℝ) (H : ℝ) → ∀ z, HasDerivAt (fun r ↦ G r z) (q r z) r := by
    filter_upwards [hG.time_derivative] with r hr hmem z
    simpa only [q, hmem.2, ite_true] using hr hmem z
  have ht := RightFrozenTimeSums.tendsto_increments H (fun r z ↦ G r z) (fun r z ↦ q r z)
    x hx hm hc (fun r ↦ |v r|) hiv hqb
    (fun s t hst htH z ↦ ac_primitive H G q hG.time_absolutelyContinuous hqd s t hst htH z)
  letI : NullSingletonClass (MathFin.ItoIntegralCLM.timeMeasure_T H) := by
    rw [← timeMeasure_eq]
    infer_instance
  have he : (∫ r, q r (x r) ∂MathFin.ItoIntegralCLM.timeMeasure_T H) =
      ∫ r, dG r (x r) ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := MathFin.ItoIntegralL2.timeMeasure)
      (measurableSet_Ioc (a := 0) (b := H)),
      (MathFin.ItoIntegralCLM.timeMeasure_T H).ae_ne H] with r hr hne
    have hrH : (r : ℝ) < H := by exact_mod_cast lt_of_le_of_ne hr.2 hne
    simp only [q, hrH, ite_true]
  rwa [he] at ht

end SHEStochastic.FiniteItoTimeCalculus
