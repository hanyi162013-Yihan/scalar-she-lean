module

public import SHEStochastic.DoobL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.CountableDoobL2
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι Ω : Type*} [LinearOrder ι] [Countable ι] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {F : Filtration ι ‹MeasurableSpace Ω›}
  {Y : ι → Ω → ℝ}

/-- On a countable time set Doob's L² inequality needs no path
regularity. This avoids completing a filtration merely to choose a
globally continuous representative. -/
theorem submartingale (hm : Submartingale Y F μ) (hn : 0 ≤ Y)
    (T : ι) (hT : MemLp (Y T) 2 μ) :
    (∫⁻ ω, (⨆ t ≤ T, ENNReal.ofReal (Y t ω)) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (Y T ω ^ 2) ∂μ := by
  let A (ω : Ω) := ⨆ t ≤ T, ENNReal.ofReal (Y t ω)
  let D (ω : Ω) := (A ω).toReal
  have hYm (t : ι) : Measurable (Y t) := (hm.stronglyMeasurable t).measurable.mono (F.le t) le_rfl
  have hAm : Measurable A := Measurable.iSup fun t ↦ Measurable.iSup fun _ ↦ (hYm t).ennreal_ofReal
  have hAf : ∀ᵐ ω ∂μ, A ω ≠ ∞ := hm.iSup_ofReal_ne_top hn T
  have hw : MaximalL2.WeakBound μ D (Y T) := by
    intro r hr
    let S := {ω | ENNReal.ofReal r ≤ A ω}
    have hS : MeasurableSet S := measurableSet_le measurable_const hAm
    have hraw : r * μ.real S ≤ ∫ ω in S, Y T ω ∂μ := by
      simpa only [NNReal.smul_def, smul_eq_mul, ENNReal.coe_nnreal_eq,
        Real.coe_toNNReal r hr.le] using
        maximal_ineq_countable_ennreal hm hn r.toNNReal T
    have hh := ENNReal.ofReal_le_ofReal hraw
    have hmeasure : ENNReal.ofReal (μ.real S) = μ S :=
      ENNReal.ofReal_toReal (measure_ne_top μ S)
    rw [ENNReal.ofReal_mul hr.le, hmeasure,
      ofReal_integral_eq_lintegral_ofReal (hm.integrable T).integrableOn
        (Eventually.of_forall fun ω ↦ hn T ω)] at hh
    have he : {ω | r ≤ D ω} =ᵐ[μ] S := by
      filter_upwards [hAf] with ω hω
      apply propext
      change (r ≤ D ω) ↔ ENNReal.ofReal r ≤ A ω
      rw [show A ω = ENNReal.ofReal (D ω) from (ENNReal.ofReal_toReal hω).symm]
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).symm
    rw [measure_congr he, Measure.restrict_congr_set he]
    exact hh
  have hh := MaximalL2.lintegral_bound μ hAm.ennreal_toReal (hYm T)
    (fun _ ↦ ENNReal.toReal_nonneg) (hn T) hT hw
  have he : (∫⁻ ω, A ω ^ 2 ∂μ) = ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hAf] with ω hω
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω]
  exact he.trans_le hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ι → Ω → E}

theorem martingale_norm_power (hm : Martingale X F μ) (p : ℕ) (T : ι)
    (hMom : ∀ t, Integrable (fun ω ↦ ‖X t ω‖ ^ p) μ)
    (hT : MemLp (fun ω ↦ ‖X T ω‖ ^ p) 2 μ) :
    (∫⁻ ω, (⨆ t ≤ T, ENNReal.ofReal (‖X t ω‖ ^ p)) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (‖X T ω‖ ^ (2 * p)) ∂μ := by
  have hs := hm.submartingale_convex_comp
    (convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) p) (continuous_norm.pow p) hMom
  have hh := submartingale hs (fun _ _ ↦ pow_nonneg (norm_nonneg _) p) T hT
  simpa only [Function.comp_def, Pi.pow_apply, ← pow_mul, Nat.mul_comm p 2] using hh

end SHEStochastic.CountableDoobL2
