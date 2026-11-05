module

public import SHE.GaussianRowGramCurve
public import SHE.OldIntervalVariance
public import SHE.CovarianceEndpoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.GaussianHeatRowWindow
open MeasureTheory Set SHE SHE.StoppedFourier
open scoped NNReal ENNReal Matrix.Norms.Elementwise
variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] {k : ℕ}

theorem square_integrable (R : ℝ → C) (hR : Measurable R) {a b U : ℝ} (hab : a ≤ b)
    (hb : ∀ r ∈ Ioo a b, ‖R r‖^2 ≤ U*(1+heatConstant*(b-r)^(-(1/2 : ℝ)))) :
    IntervalIntegrable (fun r => ‖R r‖^2) volume a b := by
  apply (CovarianceEndpoint.endpoint_majorant_integrable (q := a) (s := b) U).mono_fun'
  · exact (hR.norm.pow_const 2).aestronglyMeasurable
  · rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne b)] with r hr hne
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hb r ⟨hr.1,lt_of_le_of_ne hr.2 hne⟩

/-- Integrated heat-row mass, with no restrictions on any other rows. -/
theorem square_mass_bound (R : ℝ → C) {a b U : ℝ}
    (hab : a < b) (hspan : b-a ≤ 1) (hU : 0 ≤ U)
    (hRi : IntervalIntegrable (fun r => ‖R r‖^2) volume a b)
    (hbound : ∀ r ∈ Ioo a b, ‖R r‖^2 ≤ U*(1+heatConstant*(b-r)^(-(1/2 : ℝ)))) :
    (∫ r in a..b, ‖R r‖^2) ≤ ProfileVariance.upperConstant*U*(b-a)^(1/2 : ℝ) := by
  rw [intervalIntegral.integral_of_le hab.le]
  have hi := hRi.1
  have hp := (OldIntervalVariance.window_power_integrable hab).1.const_mul (U*(1+heatConstant))
  have hle : ∀ᵐ r ∂volume.restrict (Ioc a b), ‖R r‖^2 ≤ U*(1+heatConstant)*(b-r)^(-(1/2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne b)] with r hr hne
    have hbr : r < b := lt_of_le_of_ne hr.2 hne
    have ht : 1 ≤ (b-r)^(-(1/2 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (sub_pos.mpr hbr) (by linarith [hr.1]) (by norm_num)
    have hu := mul_le_mul_of_nonneg_left ht hU
    have hb := hbound r ⟨hr.1,hbr⟩
    nlinarith only [hu,hb]
  have hb := integral_mono_ae hi hp hle
  have he : (∫ r, U*(1+heatConstant)*(b-r)^(-(1/2 : ℝ)) ∂volume.restrict (Ioc a b)) =
      ProfileVariance.upperConstant*U*(b-a)^(1/2 : ℝ) := by
    rw [← intervalIntegral.integral_of_le hab.le,intervalIntegral.integral_const_mul,
      OldIntervalVariance.window_power_mass hab]
    unfold ProfileVariance.upperConstant
    ring
  exact hb.trans_eq he


/-- The literal Gram of a heat-row window has the original square-root
interval variance gain. Its targets need not equal the stopping endpoint. -/
theorem diagonal_bound (R : Fin k → ℝ → C) (hR : ∀ i, Measurable (R i))
    {a b U : ℝ} (hab : a < b) (hspan : b-a ≤ 1) (hU : 0 ≤ U)
    (hRi : ∀ i, IntervalIntegrable (fun r => ‖R i r‖^2) volume a b)
    (hbound : ∀ i r, r ∈ Ioo a b → ‖R i r‖^2 ≤ U*(1+heatConstant*(b-r)^(-(1/2 : ℝ)))) (i : Fin k) :
    (GaussianMatrixGramCurve.path (GaussianRowGramCurve.density R hR a b hab.le hRi) a).val i i ≤
      ProfileVariance.upperConstant*U*(b-a)^(1/2 : ℝ) := by
  rw [GaussianMatrixGramCurve.path_eq _ (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩)]
  change (∫ r in a..b, inner ℝ (R i r) (R i r)) ≤ _
  simp_rw [real_inner_self_eq_norm_sq]
  exact square_mass_bound (R i) hab hspan hU (hRi i) (hbound i)

end SHEStochastic.GaussianHeatRowWindow
