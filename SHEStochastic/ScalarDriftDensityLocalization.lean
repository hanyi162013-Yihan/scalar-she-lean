module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarDriftDensityLocalization
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Energy localization preserves the entire mass of the limiting tilt.
The estimate uses the energy under each stopped tilted law. -/
theorem mass_one (A : Ω → ℝ≥0) (hA : Measurable A)
    (density : Ω → ℝ≥0∞) (stopped : ℕ → Ω → ℝ≥0∞)
    (hStopped : ∀ n, Measurable (stopped n))
    (hOne : ∀ n, (∫⁻ x, stopped n x ∂μ) = 1)
    (hAgree : ∀ n : ℕ, ∀ᵐ x ∂μ, A x < (n : ℝ≥0) → stopped n x = density x)
    (C : ℝ≥0) (hEnergy : ∀ n, (∫⁻ x, (A x : ℝ≥0∞) ∂(μ.withDensity (stopped n))) ≤ C) :
    (∫⁻ x, density x ∂μ) = 1 := by
  have hConverges : ∀ᵐ x ∂μ, Tendsto (fun n => stopped n x) atTop (𝓝 (density x)) := by
    filter_upwards [ae_all_iff.mpr hAgree] with x hx
    obtain ⟨N, hN⟩ := exists_nat_gt (A x)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (hx n (hN.trans_le (Nat.cast_le.mpr hn))).symm
  have hUpper : (∫⁻ x, density x ∂μ) ≤ 1 := by
    calc
      _ = ∫⁻ x, liminf (fun n => stopped n x) atTop ∂μ :=
        lintegral_congr_ae (hConverges.mono (fun _ hx => hx.liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ x, stopped n x ∂μ) atTop := lintegral_liminf_le hStopped
      _ = 1 := by simp only [hOne,liminf_const]
  have hLower (n : ℕ) (hn : 0 < n) :
      (1 : ℝ≥0∞) ≤ (∫⁻ x, density x ∂μ)+(C : ℝ≥0∞)*(n : ℝ≥0∞)⁻¹ := by
    let good := {x | A x < (n : ℝ≥0)}
    have hGood : MeasurableSet good := measurableSet_lt hA measurable_const
    let Q := μ.withDensity (stopped n)
    have hOn : Q good ≤ ∫⁻ x, density x ∂μ := by
      rw [show Q good = ∫⁻ x in good, stopped n x ∂μ from withDensity_apply _ hGood]
      have he : stopped n =ᵐ[μ.restrict good] density := by
        filter_upwards [ae_restrict_of_ae (hAgree n),ae_restrict_mem hGood] with x hx hg
        exact hx hg
      exact (lintegral_congr_ae he).le.trans (setLIntegral_le_lintegral good density)
    have hBad : Q goodᶜ ≤ (C : ℝ≥0∞)*(n : ℝ≥0∞)⁻¹ := by
      have hE : AEMeasurable (fun x => (A x : ℝ≥0∞)) Q := hA.coe_nnreal_ennreal.aemeasurable
      have ht : goodᶜ = {x | (n : ℝ≥0∞) ≤ (A x : ℝ≥0∞)} := by
        ext x
        simp [good,not_lt,← ENNReal.coe_natCast]
      rw [ht,← div_eq_mul_inv]
      exact (meas_ge_le_lintegral_div hE (by positivity) (by simp)).trans
        (by rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (hEnergy n) (by positivity))
    have hQ : Q univ = 1 := by
      change (μ.withDensity (stopped n)) univ = 1
      rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      exact hOne n
    rw [←hQ,←measure_add_measure_compl hGood]
    exact add_le_add hOn hBad
  have hT : Tendsto (fun n : ℕ => (C : ℝ≥0∞)*(n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (a := (C : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
  have hSum : Tendsto (fun n : ℕ => (∫⁻ x, density x ∂μ)+(C : ℝ≥0∞)*(n : ℝ≥0∞)⁻¹)
      atTop (𝓝 (∫⁻ x, density x ∂μ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hT
  have hLo : 1 ≤ ∫⁻ x, density x ∂μ :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hSum <| by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact hLower n hn
  exact hUpper.antisymm hLo

/-- A finite strictly positive full density defines an equivalent law. -/
theorem equivalent (density : Ω → ℝ≥0∞) (hD : AEMeasurable density μ)
    (hPos : ∀ᵐ x ∂μ, density x ≠ 0) :
    μ.withDensity density ≪ μ ∧ μ ≪ μ.withDensity density :=
  ⟨withDensity_absolutelyContinuous μ density,withDensity_absolutelyContinuous' hD hPos⟩

end SHEStochastic.ScalarDriftDensityLocalization
