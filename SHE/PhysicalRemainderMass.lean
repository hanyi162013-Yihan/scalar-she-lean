module

public import SHE.PhysicalRemainderBound
public import SHE.UniformSmooth

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Explicit integrated heat domination for actual physical remainders. -/
noncomputable section
namespace SHE.PhysicalRemainderMass
open Set MeasureTheory ProbabilityTheory StoppedFourier Filter
open WordRecursion CovarianceEndpoint GaussianItoTest PhysicalIto PhysicalRemainderBound UniformSmooth
open intervalIntegral

abbrev State (n : ℕ) := WordRecursion.State n

theorem heat_majorant_mass {q s : ℝ} (hqs : q ≤ s) :
    (∫ t in q..s, 1 + StoppedFourier.heatConstant * (s - t)^(-(1 / 2 : ℝ))) =
      (s - q) + 2 * StoppedFourier.heatConstant * (s - q)^(1 / 2 : ℝ) := by
  have hi : IntervalIntegrable (fun t : ℝ => (s - t)^(-(1 / 2 : ℝ))) volume q s := by
    have hh : IntervalIntegrable (fun t : ℝ => t^(-(1 / 2 : ℝ))) volume 0 (s - q) :=
      intervalIntegrable_rpow' (by norm_num)
    simpa only [sub_self, sub_sub_cancel, sub_zero] using (hh.comp_sub_left s).symm
  have hr : (∫ t in q..s, (s - t)^(-(1 / 2 : ℝ))) = 2 * (s - q)^(1 / 2 : ℝ) := by
    rw [integral_comp_sub_left (fun u : ℝ => u^(-(1 / 2 : ℝ))) s, sub_self,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
    norm_num
    ring
  rw [integral_add intervalIntegrable_const (hi.const_mul _), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, hr]
  simp only [smul_eq_mul, mul_one]
  ring

def heatMass (h : ℝ) : ℝ := h + 2 * StoppedFourier.heatConstant * h^(1 / 2 : ℝ)

theorem heatMass_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ heatMass h :=
  add_nonneg hh (mul_nonneg (mul_nonneg (by norm_num) StoppedFourier.heatConstant_pos.le)
    (Real.rpow_nonneg hh _))

theorem heatMass_mono {h k : ℝ} (hh : 0 ≤ h) (hhk : h ≤ k) : heatMass h ≤ heatMass k := by
  apply add_le_add hhk
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh hhk (by norm_num))
    (mul_nonneg (by norm_num) StoppedFourier.heatConstant_pos.le)

theorem remainder_horizon_bound {n : ℕ} (W : EndpointWindow n) {a : ℝ → ℝ}
    {A B M h : ℝ} (hA : 0 ≤ A) (ha : ∀ z, |a z| ≤ A) (hB : 0 ≤ B)
    (hupper : W.upper ≤ M) (hleft : 0 ≤ W.left) (hright : W.right ≤ h)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {C L : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ C) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) :
    ‖wordRemainder W a U X F‖ ≤ ((1 / 2 : ℝ) * (A + M) * B * n) * heatMass h := by
  have hb := remainder_norm_bound W hA ha hB U X hF hbound hD hDD
  rw [intervalIntegral.integral_const_mul, heat_majorant_mass W.ordered] at hb
  change ‖wordRemainder W a U X F‖ ≤ ((1 / 2 : ℝ) * (A + M) * B * n) * heatMass h
  have hgap : 0 ≤ W.right - W.left := sub_nonneg.mpr W.ordered
  have hhm := heatMass_mono hgap (by linarith : W.right - W.left ≤ h)
  have hc : 0 ≤ (1 / 2 : ℝ) * (A + W.upper) * B * n :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hA W.upper_nonneg)) hB) (Nat.cast_nonneg _)
  have hc' : (1 / 2 : ℝ) * (A + W.upper) * B * n ≤ (1 / 2 : ℝ) * (A + M) * B * n := by
    gcongr
  exact hb.trans (mul_le_mul hc' hhm (heatMass_nonneg hgap)
    (by have hM := W.upper_nonneg.trans hupper; positivity))

theorem uniform_remainders_integrable {P : Type*} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    {n : ℕ} (W : P → EndpointWindow n) {a : ℝ → ℝ} {A M h : ℝ}
    (hA : 0 ≤ A) (ha : ∀ z, |a z| ≤ A) (hM : 0 ≤ M)
    (hupper : ∀ p, (W p).upper ≤ M) (hleft : ∀ p, 0 ≤ (W p).left) (hright : ∀ p, (W p).right ≤ h)
    (U : P → ℝ → CircleL2) (X : P → ℝ × HeatCircle → ℝ)
    {F : P → State n → ℝ} (hF : UniformBoundedSmooth F)
    (hmeas : Measurable (fun p => wordRemainder (W p) a (U p) (X p) (F p))) :
    Integrable (fun p => wordRemainder (W p) a (U p) (X p) (F p)) μ := by
  obtain ⟨C, _, hC⟩ := hF.norm_bound
  obtain ⟨L, _, hL⟩ := hF.fderiv.norm_bound
  obtain ⟨B, hBn, hB⟩ := hF.fderiv.fderiv.norm_bound
  apply (integrable_const (((1 / 2 : ℝ) * (A + M) * B * n) * heatMass h)).mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall (fun p => remainder_horizon_bound (W p) hA ha hBn (hupper p) (hleft p) (hright p)
    (U p) (X p) ((hF.smooth p).of_le (by simp)) (hC p) (hL p) (hB p))

end SHE.PhysicalRemainderMass
