module

public import SHE.Kernels
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

@[expose] public section
set_option autoImplicit false

/-! Analytic resolvent identities behind stopped-history damping.
The contraction below has explicit input and output histories. -/
noncomputable section
namespace SHE
open Set MeasureTheory
open scoped InnerProductSpace Topology

/-- Integration by parts gives the exact positive energy removed by a backward
resolvent, including its initial boundary term. -/
theorem stopped_resolvent_energy_identity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {U V : ℝ → E} {q T Λ κ : ℝ} (hqT : q ≤ T)
    (hU : ∀ t ∈ Icc q T, HasDerivAt U (V t) t)
    (hV : ContinuousOn V (Icc q T)) (hterminal : U T = 0) :
    (∫ t in q..T, ‖(Λ + κ) • U t - V t‖ ^ 2) -
      (∫ t in q..T, ‖κ • U t - V t‖ ^ 2) =
      Λ * (Λ + 2 * κ) * (∫ t in q..T, ‖U t‖ ^ 2) + Λ * ‖U q‖ ^ 2 := by
  have hUc : ContinuousOn U (Icc q T) := by
    intro t ht
    exact (hU t ht).continuousAt.continuousWithinAt
  have hFi : IntervalIntegrable (fun t => ‖(Λ + κ) • U t - V t‖ ^ 2) volume q T :=
    (((continuousOn_const.smul hUc).sub hV).norm.pow 2).intervalIntegrable_of_Icc hqT
  have hGi : IntervalIntegrable (fun t => ‖κ • U t - V t‖ ^ 2) volume q T :=
    (((continuousOn_const.smul hUc).sub hV).norm.pow 2).intervalIntegrable_of_Icc hqT
  have hNi : IntervalIntegrable (fun t => ‖U t‖ ^ 2) volume q T :=
    (hUc.norm.pow 2).intervalIntegrable_of_Icc hqT
  have hIi : IntervalIntegrable (fun t => 2 * ⟪U t, V t⟫_ℝ) volume q T :=
    (continuousOn_const.mul (hUc.inner hV)).intervalIntegrable_of_Icc hqT
  have hFTC : (∫ t in q..T, 2 * ⟪U t, V t⟫_ℝ) = ‖U T‖ ^ 2 - ‖U q‖ ^ 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hqT] at ht
      exact (hU t ht).norm_sq
    · exact hIi
  have heq : ∀ t : ℝ,
      ‖(Λ + κ) • U t - V t‖ ^ 2 - ‖κ • U t - V t‖ ^ 2 =
        (Λ * (Λ + 2 * κ)) * ‖U t‖ ^ 2 - Λ * (2 * ⟪U t, V t⟫_ℝ) := by
    intro t
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left]
    ring
  rw [← intervalIntegral.integral_sub hFi hGi]
  rw [intervalIntegral.integral_congr (fun t _ => heq t)]
  rw [intervalIntegral.integral_sub (hNi.const_mul _) (hIi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hFTC,
    hterminal, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub]
  ring

/-- Actual finite-interval contraction for the explicit resolvent input
`F=(Λ+κ)U-U'` and output `G=κU-U'`. -/
theorem stopped_resolvent_contraction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {U V : ℝ → E} {q T Λ κ : ℝ} (hqT : q ≤ T)
    (hΛ : 0 ≤ Λ) (hκ : 0 ≤ κ)
    (hU : ∀ t ∈ Icc q T, HasDerivAt U (V t) t)
    (hV : ContinuousOn V (Icc q T)) (hterminal : U T = 0) :
    (∫ t in q..T, ‖κ • U t - V t‖ ^ 2) ≤
      (∫ t in q..T, ‖(Λ + κ) • U t - V t‖ ^ 2) := by
  have he := stopped_resolvent_energy_identity hqT hU hV hterminal (Λ := Λ) (κ := κ)
  have hi : 0 ≤ ∫ t in q..T, ‖U t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hqT (fun t _ => sq_nonneg ‖U t‖)
  have hprod : 0 ≤ Λ * (Λ + 2 * κ) * (∫ t in q..T, ‖U t‖ ^ 2) :=
    mul_nonneg (mul_nonneg hΛ (by linarith)) hi
  have hb : 0 ≤ Λ * ‖U q‖ ^ 2 := mul_nonneg hΛ (sq_nonneg _)
  linarith

/-- The stopped-history Fourier multiplier has modulus at most one. -/
theorem stopped_history_multiplier_le_one {Λ κ ω : ℝ} (hΛ : 0 ≤ Λ) (hκ : 0 ≤ κ) :
    ‖((κ : ℂ) - (ω : ℂ) * Complex.I) /
      (((Λ + κ : ℝ) : ℂ) - (ω : ℂ) * Complex.I)‖ ≤ 1 := by
  have hnorm : ‖(κ : ℂ) - (ω : ℂ) * Complex.I‖ ≤
      ‖((Λ + κ : ℝ) : ℂ) - (ω : ℂ) * Complex.I‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    nlinarith
  rw [norm_div]
  by_cases hz : (((Λ + κ : ℝ) : ℂ) - (ω : ℂ) * Complex.I) = 0
  · rw [hz, norm_zero, div_zero]
    norm_num
  · exact (div_le_one (norm_pos_iff.mpr hz)).mpr hnorm

/-- Exact integration of one stopped damping history. -/
theorem stopped_exponential_integral {Λ u σ : ℝ} (hΛ : 0 < Λ) :
    (∫ v in u..σ, Real.exp (-Λ * (v - u))) =
      (1 - Real.exp (-Λ * (σ - u))) / Λ := by
  rw [intervalIntegral.integral_comp_sub_right (fun v : ℝ => Real.exp (-Λ * v)) u]
  simp only [sub_self]
  rw [intervalIntegral.integral_comp_mul_left Real.exp (show -Λ ≠ 0 by linarith), integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul, inv_neg]
  ring

/-- The heat-semigroup factors telescope inside each stopped scalar history. -/
theorem stopped_heat_resolvent_integral {Λ κ u σ T : ℝ} (hΛ : 0 < Λ) :
    (∫ v in u..σ, Real.exp (-Λ * (v - u)) * Real.exp (-(v - u) * κ) *
      Real.exp (-(T - v) * κ)) =
      ((1 - Real.exp (-Λ * (σ - u))) / Λ) * Real.exp (-(T - u) * κ) := by
  have heq : ∀ v : ℝ,
      Real.exp (-Λ * (v - u)) * Real.exp (-(v - u) * κ) * Real.exp (-(T - v) * κ) =
        Real.exp (-Λ * (v - u)) * Real.exp (-(T - u) * κ) := by
    intro v
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [intervalIntegral.integral_congr (fun v _ => heq v), intervalIntegral.integral_mul_const,
    stopped_exponential_integral hΛ]

/-- Exact scalar stopped-history resolvent identity with the original target age. -/
theorem stopped_heat_resolvent_identity {Λ κ u σ T : ℝ} (hΛ : 0 < Λ) :
    Real.exp (-(T - u) * κ) - Λ *
      (∫ v in u..σ, Real.exp (-Λ * (v - u)) * Real.exp (-(v - u) * κ) *
        Real.exp (-(T - v) * κ)) =
      Real.exp (-Λ * (σ - u)) * Real.exp (-(T - u) * κ) := by
  rw [stopped_heat_resolvent_integral hΛ]
  field_simp
  ring

/-- A monotone older history cannot concentrate its mass in the younger interval. -/
theorem early_history_fraction {f : ℝ → ℝ} {a b : ℝ} (hb : 0 ≤ b) (hba : b < a)
    (hf : MonotoneOn f (Icc 0 a)) :
    (∫ u in (0 : ℝ)..b, f u) ≤ (b / (a - b)) * ∫ u in b..a, f u := by
  have ha : 0 ≤ a := hb.trans hba.le
  have hfull : IntervalIntegrable f volume 0 a := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le ha] using hf
  have hearly : IntervalIntegrable f volume 0 b := by
    apply hfull.mono_set
    rw [uIcc_of_le ha, uIcc_of_le hb]
    exact Icc_subset_Icc le_rfl hba.le
  have hlate : IntervalIntegrable f volume b a := by
    apply hfull.mono_set
    rw [uIcc_of_le ha, uIcc_of_le hba.le]
    exact Icc_subset_Icc hb le_rfl
  have hleft : (∫ u in (0 : ℝ)..b, f u) ≤ b * f b := by
    calc
      _ ≤ ∫ _u in (0 : ℝ)..b, f b := by
        apply intervalIntegral.integral_mono_on hb hearly intervalIntegrable_const
        intro u hu
        exact hf ⟨hu.1, hu.2.trans hba.le⟩ ⟨hb, hba.le⟩ hu.2
      _ = _ := by simp
  have hright : (a - b) * f b ≤ ∫ u in b..a, f u := by
    calc
      _ = ∫ _u in b..a, f b := by simp
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hba.le intervalIntegrable_const hlate
        intro u hu
        exact hf ⟨hb, hba.le⟩ ⟨hb.trans hu.1, hu.2⟩ hu.1
  have hratio : 0 ≤ b / (a - b) := div_nonneg hb (by linarith)
  calc
    _ ≤ b * f b := hleft
    _ = (b / (a - b)) * ((a - b) * f b) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hright hratio

/-- Geometric age separation yields the scalar covariance-frame fraction. -/
theorem early_history_age_separation {f : ℝ → ℝ} {a b A : ℝ} (hb : 0 ≤ b)
    (hba : b < a) (hA : 1 < A) (hsep : A * b ≤ a)
    (hf : MonotoneOn f (Icc 0 a)) (hn : ∀ u ∈ Icc 0 a, 0 ≤ f u) :
    (∫ u in (0 : ℝ)..b, f u) ≤ (A - 1)⁻¹ * ∫ u in (0 : ℝ)..a, f u := by
  have ha : 0 ≤ a := hb.trans hba.le
  have hfull : IntervalIntegrable f volume 0 a := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le ha] using hf
  have hearly : IntervalIntegrable f volume 0 b := by
    apply hfull.mono_set
    rw [uIcc_of_le ha, uIcc_of_le hb]
    exact Icc_subset_Icc le_rfl hba.le
  have hlate : IntervalIntegrable f volume b a := by
    apply hfull.mono_set
    rw [uIcc_of_le ha, uIcc_of_le hba.le]
    exact Icc_subset_Icc hb le_rfl
  have hearlyn : 0 ≤ ∫ u in (0 : ℝ)..b, f u := by
    apply intervalIntegral.integral_nonneg hb
    intro u hu
    exact hn u ⟨hu.1, hu.2.trans hba.le⟩
  have hlaten : 0 ≤ ∫ u in b..a, f u := by
    apply intervalIntegral.integral_nonneg hba.le
    intro u hu
    exact hn u ⟨hb.trans hu.1, hu.2⟩
  have hsum := intervalIntegral.integral_add_adjacent_intervals hearly hlate
  have hfrac : b / (a - b) ≤ (A - 1)⁻¹ := by
    rw [← one_div]
    apply (div_le_div_iff₀ (by linarith : 0 < a - b) (by linarith : 0 < A - 1)).mpr
    nlinarith
  calc
    _ ≤ (b / (a - b)) * ∫ u in b..a, f u := early_history_fraction hb hba hf
    _ ≤ (A - 1)⁻¹ * ∫ u in b..a, f u := mul_le_mul_of_nonneg_right hfrac hlaten
    _ ≤ (A - 1)⁻¹ * ∫ u in (0 : ℝ)..a, f u := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith

theorem norm_resolvent_intervalIntegrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {U V : ℝ → E} {q T : ℝ} (hqT : q ≤ T)
    (hUc : ContinuousOn U (Icc q T))
    (hVm : AEStronglyMeasurable V (volume.restrict (Ioc q T)))
    (hV2 : IntervalIntegrable (fun t => ‖V t‖ ^ 2) volume q T) (c : ℝ) :
    IntervalIntegrable (fun t => ‖c • U t - V t‖ ^ 2) volume q T := by
  have hU2 : IntervalIntegrable (fun t => ‖U t‖ ^ 2) volume q T :=
    (hUc.norm.pow 2).intervalIntegrable_of_Icc hqT
  have hUm : AEStronglyMeasurable U (volume.restrict (Ioc q T)) :=
    (hUc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  apply ((hU2.const_mul (2 * c ^ 2)).add (hV2.const_mul 2)).mono_fun'
  · rw [uIoc_of_le hqT]
    have hCm : AEStronglyMeasurable (fun _t : ℝ => c) (volume.restrict (Ioc q T)) :=
      aestronglyMeasurable_const
    exact ((hCm.smul hUm).sub hVm).norm.pow 2
  · rw [uIoc_of_le hqT]
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn := norm_sub_le (c • U t) (V t)
    rw [norm_smul, Real.norm_eq_abs] at hn
    have hnF := norm_nonneg (c • U t - V t)
    have hnU := norm_nonneg (U t)
    have hnV := norm_nonneg (V t)
    have hab := abs_nonneg c
    nlinarith [sq_abs c, sq_nonneg (|c| * ‖U t‖ - ‖V t‖)]

/-- The energy identity remains valid for right differentiable resolvents with
square-integrable derivative, allowing the jumps of finitely stopped histories. -/
theorem stopped_resolvent_energy_identity_right {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {U V : ℝ → E} {q T Λ κ : ℝ} (hqT : q ≤ T)
    (hUc : ContinuousOn U (Icc q T))
    (hU : ∀ t ∈ Ioo q T, HasDerivWithinAt U (V t) (Ioi t) t)
    (hVm : AEStronglyMeasurable V (volume.restrict (Ioc q T)))
    (hV2 : IntervalIntegrable (fun t => ‖V t‖ ^ 2) volume q T) (hterminal : U T = 0) :
    (∫ t in q..T, ‖(Λ + κ) • U t - V t‖ ^ 2) -
      (∫ t in q..T, ‖κ • U t - V t‖ ^ 2) =
      Λ * (Λ + 2 * κ) * (∫ t in q..T, ‖U t‖ ^ 2) + Λ * ‖U q‖ ^ 2 := by
  have hFi := norm_resolvent_intervalIntegrable hqT hUc hVm hV2 (Λ + κ)
  have hGi := norm_resolvent_intervalIntegrable hqT hUc hVm hV2 κ
  have hNi : IntervalIntegrable (fun t => ‖U t‖ ^ 2) volume q T :=
    (hUc.norm.pow 2).intervalIntegrable_of_Icc hqT
  have hUm : AEStronglyMeasurable U (volume.restrict (Ioc q T)) :=
    (hUc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hIi : IntervalIntegrable (fun t => 2 * ⟪U t, V t⟫_ℝ) volume q T := by
    apply (hNi.add hV2).mono_fun'
    · rw [uIoc_of_le hqT]
      exact (hUm.inner hVm).const_mul 2
    · rw [uIoc_of_le hqT]
      filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [abs_real_inner_le_norm (U t) (V t), sq_nonneg (‖U t‖ - ‖V t‖)]
  have hFTC : (∫ t in q..T, 2 * ⟪U t, V t⟫_ℝ) = ‖U T‖ ^ 2 - ‖U q‖ ^ 2 := by
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hqT (hUc.norm.pow 2)
      (fun t ht => (hU t ht).norm_sq) hIi
  have heq : ∀ t : ℝ,
      ‖(Λ + κ) • U t - V t‖ ^ 2 - ‖κ • U t - V t‖ ^ 2 =
        (Λ * (Λ + 2 * κ)) * ‖U t‖ ^ 2 - Λ * (2 * ⟪U t, V t⟫_ℝ) := by
    intro t
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left]
    ring
  rw [← intervalIntegral.integral_sub hFi hGi]
  rw [intervalIntegral.integral_congr (fun t _ => heq t)]
  rw [intervalIntegral.integral_sub (hNi.const_mul _) (hIi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hFTC,
    hterminal, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub]
  ring

theorem stopped_resolvent_contraction_right {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {U V : ℝ → E} {q T Λ κ : ℝ} (hqT : q ≤ T)
    (hΛ : 0 ≤ Λ) (hκ : 0 ≤ κ) (hUc : ContinuousOn U (Icc q T))
    (hU : ∀ t ∈ Ioo q T, HasDerivWithinAt U (V t) (Ioi t) t)
    (hVm : AEStronglyMeasurable V (volume.restrict (Ioc q T)))
    (hV2 : IntervalIntegrable (fun t => ‖V t‖ ^ 2) volume q T) (hterminal : U T = 0) :
    (∫ t in q..T, ‖κ • U t - V t‖ ^ 2) ≤
      (∫ t in q..T, ‖(Λ + κ) • U t - V t‖ ^ 2) := by
  have he := stopped_resolvent_energy_identity_right hqT hUc hU hVm hV2 hterminal
    (Λ := Λ) (κ := κ)
  have hi : 0 ≤ ∫ t in q..T, ‖U t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hqT (fun t _ => sq_nonneg ‖U t‖)
  have hp : 0 ≤ Λ * (Λ + 2 * κ) * (∫ t in q..T, ‖U t‖ ^ 2) :=
    mul_nonneg (mul_nonneg hΛ (by linarith)) hi
  have hb : 0 ≤ Λ * ‖U q‖ ^ 2 := mul_nonneg hΛ (sq_nonneg _)
  linarith

/-- One undamped stopped heat mode at a fixed nonnegative spatial frequency. -/
def stoppedModeF (κ σ target u : ℝ) : ℝ :=
  if u < σ then Real.exp (-(target - u) * κ) else 0

/-- Its explicit backward resolvent. The positive part makes continuity at the stop visible. -/
def stoppedModeU (Λ κ σ target u : ℝ) : ℝ :=
  Real.exp (-(target - u) * κ) * (1 - Real.exp (-Λ * max (σ - u) 0)) / Λ

theorem stoppedModeU_continuous (Λ κ σ target : ℝ) :
    Continuous (stoppedModeU Λ κ σ target) := by
  unfold stoppedModeU
  fun_prop

theorem stoppedModeF_measurable (κ σ target : ℝ) : Measurable (stoppedModeF κ σ target) := by
  unfold stoppedModeF
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
  · have hf : Continuous (fun u : ℝ => Real.exp (-(target - u) * κ)) := by fun_prop
    exact hf.measurable
  · exact measurable_const

theorem stoppedModeU_zero {Λ κ σ target u : ℝ} (hu : σ ≤ u) :
    stoppedModeU Λ κ σ target u = 0 := by
  simp [stoppedModeU, max_eq_right (show σ - u ≤ 0 by linarith)]

theorem stoppedModeU_before {Λ κ σ target u : ℝ} (hu : u < σ) :
    stoppedModeU Λ κ σ target u =
      Real.exp (-(target - u) * κ) * (1 - Real.exp (-Λ * (σ - u))) / Λ := by
  simp only [stoppedModeU, max_eq_left (show 0 ≤ σ - u by linarith)]

/-- The resolvent ODE holds from the right even at a stopping time. -/
theorem stoppedModeU_hasDerivWithinAt {Λ κ σ target u : ℝ} (hΛ : 0 < Λ) :
    HasDerivWithinAt (stoppedModeU Λ κ σ target)
      ((Λ + κ) * stoppedModeU Λ κ σ target u - stoppedModeF κ σ target u) (Ioi u) u := by
  by_cases hu : u < σ
  · have hE : HasDerivAt (fun v : ℝ => Real.exp (-(target - v) * κ))
        (κ * Real.exp (-(target - u) * κ)) u := by
      have hlin : HasDerivAt (fun v : ℝ => κ * (v - target)) κ u := by
        convert ((hasDerivAt_id u).sub_const target).const_mul κ using 1 <;> simp
      convert hlin.exp using 1
      · ext v
        congr 1
        ring
      · have he : -(target - u) * κ = κ * (u - target) := by ring
        rw [he]
        ring
    have hD : HasDerivAt (fun v : ℝ => 1 - Real.exp (-Λ * (σ - v)))
        (-Λ * Real.exp (-Λ * (σ - u))) u := by
      have hlin : HasDerivAt (fun v : ℝ => Λ * (v - σ)) Λ u := by
        convert ((hasDerivAt_id u).sub_const σ).const_mul Λ using 1 <;> simp
      convert (hasDerivAt_const u 1).sub hlin.exp using 1
      · ext v
        dsimp
        congr 2
        ring
      · have he : -Λ * (σ - u) = Λ * (u - σ) := by ring
        rw [he]
        ring
    have hS := (hE.mul hD).div_const Λ
    have hder :
        (κ * Real.exp (-(target - u) * κ) * (1 - Real.exp (-Λ * (σ - u))) +
          Real.exp (-(target - u) * κ) * (-Λ * Real.exp (-Λ * (σ - u)))) / Λ =
          (Λ + κ) * stoppedModeU Λ κ σ target u - stoppedModeF κ σ target u := by
      rw [stoppedModeU_before hu]
      simp only [stoppedModeF, ite_eq_left hu]
      field_simp
      ring
    rw [hder] at hS
    apply hS.hasDerivWithinAt.congr_of_eventuallyEq
    · have he : stoppedModeU Λ κ σ target =ᶠ[𝓝 u]
          (fun v => Real.exp (-(target - v) * κ) * (1 - Real.exp (-Λ * (σ - v))) / Λ) := by
        filter_upwards [Iio_mem_nhds hu] with v hv
        exact stoppedModeU_before hv
      exact he.filter_mono nhdsWithin_le_nhds
    · exact stoppedModeU_before hu
  · have huσ : σ ≤ u := le_of_not_gt hu
    rw [stoppedModeU_zero huσ]
    simp only [stoppedModeF, ite_eq_right hu, mul_zero, sub_zero]
    apply (hasDerivWithinAt_const u (Ioi u) (0 : ℝ)).congr
    · intro v hv
      exact stoppedModeU_zero (huσ.trans hv.le)
    · exact stoppedModeU_zero huσ

theorem stoppedModeF_square_integrable (κ σ target q T : ℝ) :
    IntervalIntegrable (fun u => ‖stoppedModeF κ σ target u‖ ^ 2) volume q T := by
  have hi : IntervalIntegrable (fun u : ℝ => Real.exp (-(target - u) * κ) ^ 2) volume q T := by
    apply Continuous.intervalIntegrable
    fun_prop
  apply hi.mono_fun'
  · exact ((stoppedModeF_measurable κ σ target).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hu : u < σ
    · simp only [stoppedModeF, ite_eq_left hu, Real.norm_eq_abs, sq_abs]
      exact le_rfl
    · simp only [stoppedModeF, ite_eq_right hu, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity

/-- The explicit stopped resolvent has a square-integrable right derivative. -/
theorem stoppedModeU_derivative_square_integrable {Λ : ℝ} (_hΛ : 0 < Λ)
    (κ σ target q T : ℝ) (hqT : q ≤ T) :
    IntervalIntegrable (fun u =>
      ‖(Λ + κ) * stoppedModeU Λ κ σ target u - stoppedModeF κ σ target u‖ ^ 2) volume q T := by
  simpa only [smul_eq_mul] using norm_resolvent_intervalIntegrable hqT
    (stoppedModeU_continuous Λ κ σ target).continuousOn
    (stoppedModeF_measurable κ σ target).aestronglyMeasurable
    (stoppedModeF_square_integrable κ σ target q T) (Λ + κ)

theorem stoppedMode_damping_identity {Λ κ σ target u : ℝ} (hΛ : 0 < Λ) :
    stoppedModeF κ σ target u - Λ * stoppedModeU Λ κ σ target u =
      Real.exp (-Λ * (σ - u)) * stoppedModeF κ σ target u := by
  by_cases hu : u < σ
  · rw [stoppedModeU_before hu]
    simp only [stoppedModeF, ite_eq_left hu]
    field_simp
    ring
  · rw [stoppedModeU_zero (le_of_not_gt hu)]
    simp only [stoppedModeF, ite_eq_right hu, mul_zero, sub_zero]

theorem norm_sq_add_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {q T : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (uIoc q T)))
    (hgm : AEStronglyMeasurable g (volume.restrict (uIoc q T)))
    (hf : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume q T)
    (hg : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume q T) :
    IntervalIntegrable (fun t => ‖f t + g t‖ ^ 2) volume q T := by
  apply ((hf.const_mul 2).add (hg.const_mul 2)).mono_fun'
  · exact (hfm.add hgm).norm.pow 2
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn := norm_add_le (f t) (g t)
    have hf0 := norm_nonneg (f t)
    have hg0 := norm_nonneg (g t)
    have hfg := norm_nonneg (f t + g t)
    nlinarith [sq_nonneg (‖f t‖ - ‖g t‖)]

theorem finite_L2_sum {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ι) (f : ι → ℝ → E) {q T : ℝ}
    (hm : ∀ i ∈ I, AEStronglyMeasurable (f i) (volume.restrict (uIoc q T)))
    (hi : ∀ i ∈ I, IntervalIntegrable (fun t => ‖f i t‖ ^ 2) volume q T) :
    AEStronglyMeasurable (fun t => ∑ i ∈ I, f i t) (volume.restrict (uIoc q T)) ∧
      IntervalIntegrable (fun t => ‖∑ i ∈ I, f i t‖ ^ 2) volume q T := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨aestronglyMeasurable_const, (continuous_const.norm.pow 2).intervalIntegrable _ _⟩
  | @insert i I hiI ih =>
    have hrest := ih (fun j hj => hm j (Finset.mem_insert_of_mem hj))
      (fun j hj => hi j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hiI]
    exact ⟨(hm i (Finset.mem_insert_self _ _)).add hrest.1,
      norm_sq_add_integrable (hm i (Finset.mem_insert_self _ _)) hrest.1
        (hi i (Finset.mem_insert_self _ _)) hrest.2⟩

/-- Genuine time-L2 contraction for every finite signed family of stopped heat modes.
All stop collisions and unequal original target ages are allowed. -/
theorem finite_stopped_history_contraction {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (I : Finset ι) (z : ι → E) (σ target : ι → ℝ)
    {Λ κ q T : ℝ} (hΛ : 0 < Λ) (hκ : 0 ≤ κ) (hqT : q ≤ T)
    (hstops : ∀ i ∈ I, σ i ≤ T) :
    (∫ u in q..T, ‖∑ i ∈ I,
      (Real.exp (-Λ * (σ i - u)) * stoppedModeF κ (σ i) (target i) u) • z i‖ ^ 2) ≤
      (∫ u in q..T, ‖∑ i ∈ I, stoppedModeF κ (σ i) (target i) u • z i‖ ^ 2) := by
  let U : ℝ → E := fun u => ∑ i ∈ I, stoppedModeU Λ κ (σ i) (target i) u • z i
  let V : ℝ → E := fun u => ∑ i ∈ I,
    ((Λ + κ) * stoppedModeU Λ κ (σ i) (target i) u - stoppedModeF κ (σ i) (target i) u) • z i
  have hUc : Continuous U := by
    apply continuous_finsetSum
    intro i hi
    exact (stoppedModeU_continuous Λ κ (σ i) (target i)).smul continuous_const
  have hder : ∀ u : ℝ, HasDerivWithinAt U (V u) (Ioi u) u := by
    intro u
    exact HasDerivWithinAt.fun_sum (fun i _ => (stoppedModeU_hasDerivWithinAt hΛ).smul_const (z i))
  have hVmodes : ∀ i ∈ I, AEStronglyMeasurable
      (fun u => ((Λ + κ) * stoppedModeU Λ κ (σ i) (target i) u -
        stoppedModeF κ (σ i) (target i) u) • z i) (volume.restrict (uIoc q T)) := by
    intro i hi
    have hm : AEStronglyMeasurable (fun u => (Λ + κ) * stoppedModeU Λ κ (σ i) (target i) u -
        stoppedModeF κ (σ i) (target i) u) (volume.restrict (uIoc q T)) :=
      ((measurable_const.mul (stoppedModeU_continuous Λ κ (σ i) (target i)).measurable).sub
        (stoppedModeF_measurable κ (σ i) (target i))).aestronglyMeasurable
    exact hm.smul aestronglyMeasurable_const
  have hVmode2 : ∀ i ∈ I, IntervalIntegrable
      (fun u => ‖((Λ + κ) * stoppedModeU Λ κ (σ i) (target i) u -
        stoppedModeF κ (σ i) (target i) u) • z i‖ ^ 2) volume q T := by
    intro i hi
    have he := (stoppedModeU_derivative_square_integrable hΛ κ (σ i) (target i) q T hqT).const_mul (‖z i‖ ^ 2)
    simpa only [norm_smul, mul_pow, mul_comm] using he
  have hV := finite_L2_sum I _ hVmodes hVmode2
  have hterminal : U T = 0 := by
    dsimp [U]
    apply Finset.sum_eq_zero
    intro i hi
    rw [stoppedModeU_zero (hstops i hi), zero_smul]
  have he := stopped_resolvent_contraction_right hqT hΛ.le hκ hUc.continuousOn
    (fun u _ => hder u) (by simpa only [uIoc_of_le hqT] using hV.1) hV.2 hterminal
  have hinput : ∀ u : ℝ, (Λ + κ) • U u - V u =
      ∑ i ∈ I, stoppedModeF κ (σ i) (target i) u • z i := by
    intro u
    dsimp [U, V]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul, ← sub_smul]
    congr 1
    ring
  have houtput : ∀ u : ℝ, κ • U u - V u =
      ∑ i ∈ I, (Real.exp (-Λ * (σ i - u)) * stoppedModeF κ (σ i) (target i) u) • z i := by
    intro u
    dsimp [U, V]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul, ← sub_smul]
    congr 1
    calc
      _ = stoppedModeF κ (σ i) (target i) u - Λ * stoppedModeU Λ κ (σ i) (target i) u := by ring
      _ = _ := stoppedMode_damping_identity hΛ
  simpa only [hinput, houtput] using he

theorem intervalIntegrable_of_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {q T : ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict (uIoc q T)))
    (h2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume q T) :
    IntervalIntegrable f volume q T := by
  apply (intervalIntegrable_const.add h2).mono_fun'
  · exact hm
  · filter_upwards [] with t
    have hsq := sq_nonneg (‖f t‖ - 1)
    change ‖f t‖ ≤ (1 : ℝ) + ‖f t‖ ^ 2
    nlinarith [norm_nonneg (f t)]

/-- Cauchy--Schwarz on a finite time interval, with an explicit interval length. -/
theorem interval_integral_norm_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {q T : ℝ} (hqT : q < T)
    (hm : AEStronglyMeasurable f (volume.restrict (uIoc q T)))
    (h2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume q T) :
    ‖∫ t in q..T, f t‖ ^ 2 ≤ (T - q) * ∫ t in q..T, ‖f t‖ ^ 2 := by
  have hfi := intervalIntegrable_of_norm_sq hm h2
  let A : ℝ := ∫ t in q..T, ‖f t‖
  let L : ℝ := T - q
  have hL : 0 < L := by dsimp [L]; linarith
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg hqT.le (fun t _ => norm_nonneg _)
  have hvar : 0 ≤ ∫ t in q..T, (‖f t‖ - A / L) ^ 2 :=
    intervalIntegral.integral_nonneg hqT.le (fun t _ => sq_nonneg _)
  have heq : (∫ t in q..T, (‖f t‖ - A / L) ^ 2) =
      (∫ t in q..T, ‖f t‖ ^ 2) - 2 * (A / L) * A + (A / L) ^ 2 * L := by
    rw [intervalIntegral.integral_congr (fun t _ =>
      show (‖f t‖ - A / L) ^ 2 = ‖f t‖ ^ 2 - (2 * (A / L)) * ‖f t‖ + (A / L) ^ 2 by ring)]
    rw [intervalIntegral.integral_add (h2.sub (hfi.norm.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub h2 (hfi.norm.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    dsimp [A, L]
    ring
  have halg : L * ((∫ t in q..T, ‖f t‖ ^ 2) - 2 * (A / L) * A + (A / L) ^ 2 * L) =
      L * (∫ t in q..T, ‖f t‖ ^ 2) - A ^ 2 := by field_simp; ring
  rw [heq] at hvar
  have hmul := mul_nonneg hL.le hvar
  rw [halg] at hmul
  have hn : ‖∫ t in q..T, f t‖ ≤ A := intervalIntegral.norm_integral_le_integral_norm hqT.le
  have hn2 := (sq_le_sq₀ (norm_nonneg _) hA).mpr hn
  dsimp [L] at hmul
  linarith

/-- A backward resolvent on an interval of length `T-q` gains its square-root length
at the current endpoint. This is the small-mass bridge for the `R` row. -/
theorem stopped_resolvent_boundary_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {U V : ℝ → E} {q T c : ℝ}
    (hqT : q < T) (hc : 0 ≤ c) (hUc : ContinuousOn U (Icc q T))
    (hU : ∀ t ∈ Ioo q T, HasDerivWithinAt U (V t) (Ioi t) t)
    (hVm : AEStronglyMeasurable V (volume.restrict (Ioc q T)))
    (hV2 : IntervalIntegrable (fun t => ‖V t‖ ^ 2) volume q T) (hterminal : U T = 0) :
    ‖U q‖ ^ 2 ≤ (T - q) * ∫ t in q..T, ‖c • U t - V t‖ ^ 2 := by
  have hVm' : AEStronglyMeasurable V (volume.restrict (uIoc q T)) := by
    simpa only [uIoc_of_le hqT.le] using hVm
  have hVi := intervalIntegrable_of_norm_sq hVm' hV2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hqT.le hUc hU hVi
  rw [hterminal, zero_sub] at hFTC
  have hC := interval_integral_norm_sq_le hqT hVm' hV2
  rw [hFTC, norm_neg] at hC
  have hR := stopped_resolvent_contraction_right hqT.le hc (κ := 0) (by norm_num)
    hUc hU hVm hV2 hterminal
  simp only [zero_smul, zero_sub, norm_neg, add_zero] at hR
  exact hC.trans (mul_le_mul_of_nonneg_left hR (by linarith))

/-- The small-mass current difference estimate for an actual finite stopped family. -/
theorem finite_stopped_resolvent_boundary {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (I : Finset ι) (z : ι → E) (σ target : ι → ℝ)
    {Λ κ q T : ℝ} (hΛ : 0 < Λ) (hκ : 0 ≤ κ) (hqT : q < T)
    (hstops : ∀ i ∈ I, σ i ≤ T) :
    ‖∑ i ∈ I, ((1 - Real.exp (-Λ * (σ i - q))) * stoppedModeF κ (σ i) (target i) q) • z i‖ ^ 2 ≤
      (Λ ^ 2 * (T - q)) * (∫ u in q..T, ‖∑ i ∈ I, stoppedModeF κ (σ i) (target i) u • z i‖ ^ 2) := by
  let U : ℝ → E := fun u => ∑ i ∈ I, stoppedModeU Λ κ (σ i) (target i) u • z i
  let V : ℝ → E := fun u => ∑ i ∈ I,
    ((Λ + κ) * stoppedModeU Λ κ (σ i) (target i) u - stoppedModeF κ (σ i) (target i) u) • z i
  have hUc : Continuous U := by
    apply continuous_finsetSum
    intro i hi
    exact (stoppedModeU_continuous Λ κ (σ i) (target i)).smul continuous_const
  have hder : ∀ u : ℝ, HasDerivWithinAt U (V u) (Ioi u) u := by
    intro u
    exact HasDerivWithinAt.fun_sum (fun i _ => (stoppedModeU_hasDerivWithinAt hΛ).smul_const (z i))
  have hVmodes : ∀ i ∈ I, AEStronglyMeasurable
      (fun u => ((Λ + κ) * stoppedModeU Λ κ (σ i) (target i) u -
        stoppedModeF κ (σ i) (target i) u) • z i) (volume.restrict (uIoc q T)) := by
    intro i hi
    have hm : AEStronglyMeasurable (fun u => (Λ + κ) * stoppedModeU Λ κ (σ i) (target i) u -
        stoppedModeF κ (σ i) (target i) u) (volume.restrict (uIoc q T)) :=
      ((measurable_const.mul (stoppedModeU_continuous Λ κ (σ i) (target i)).measurable).sub
        (stoppedModeF_measurable κ (σ i) (target i))).aestronglyMeasurable
    exact hm.smul aestronglyMeasurable_const
  have hVmode2 : ∀ i ∈ I, IntervalIntegrable
      (fun u => ‖((Λ + κ) * stoppedModeU Λ κ (σ i) (target i) u -
        stoppedModeF κ (σ i) (target i) u) • z i‖ ^ 2) volume q T := by
    intro i hi
    have he := (stoppedModeU_derivative_square_integrable hΛ κ (σ i) (target i) q T hqT.le).const_mul (‖z i‖ ^ 2)
    simpa only [norm_smul, mul_pow, mul_comm] using he
  have hV := finite_L2_sum I _ hVmodes hVmode2
  have hterminal : U T = 0 := by
    dsimp [U]
    apply Finset.sum_eq_zero
    intro i hi
    rw [stoppedModeU_zero (hstops i hi), zero_smul]
  have he := stopped_resolvent_boundary_bound hqT (show 0 ≤ Λ + κ by linarith)
    hUc.continuousOn (fun u _ => hder u)
    (by simpa only [uIoc_of_le hqT.le] using hV.1) hV.2 hterminal
  have hinput : ∀ u : ℝ, (Λ + κ) • U u - V u =
      ∑ i ∈ I, stoppedModeF κ (σ i) (target i) u • z i := by
    intro u
    dsimp [U, V]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul, ← sub_smul]
    congr 1
    ring
  simp only [hinput] at he
  have hrow : (∑ i ∈ I, ((1 - Real.exp (-Λ * (σ i - q))) *
      stoppedModeF κ (σ i) (target i) q) • z i) = Λ • U q := by
    dsimp [U]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul]
    congr 1
    have hdi := stoppedMode_damping_identity (Λ := Λ) (κ := κ) (σ := σ i) (target := target i) (u := q) hΛ
    nlinarith
  rw [hrow, norm_smul, Real.norm_eq_abs, abs_of_pos hΛ, mul_pow]
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg Λ)
  nlinarith

/-- Endpoint-open version, allowing a history to stop at the older age `a`. -/
theorem early_history_fraction_open {f : ℝ → ℝ} {a b : ℝ} (hb : 0 ≤ b) (hba : b < a)
    (hfi : IntervalIntegrable f volume 0 a) (hf : MonotoneOn f (Ico 0 a)) :
    (∫ u in (0 : ℝ)..b, f u) ≤ (b / (a - b)) * ∫ u in b..a, f u := by
  have ha : 0 ≤ a := hb.trans hba.le
  have hearly : IntervalIntegrable f volume 0 b := by
    apply hfi.mono_set
    rw [uIcc_of_le ha, uIcc_of_le hb]
    exact Icc_subset_Icc le_rfl hba.le
  have hlate : IntervalIntegrable f volume b a := by
    apply hfi.mono_set
    rw [uIcc_of_le ha, uIcc_of_le hba.le]
    exact Icc_subset_Icc hb le_rfl
  have hleft : (∫ u in (0 : ℝ)..b, f u) ≤ b * f b := by
    calc
      _ ≤ ∫ _u in (0 : ℝ)..b, f b := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hb hearly intervalIntegrable_const
        intro u hu
        exact hf ⟨hu.1.le, hu.2.trans hba⟩ ⟨hb, hba⟩ hu.2.le
      _ = _ := by simp
  have hright : (a - b) * f b ≤ ∫ u in b..a, f u := by
    calc
      _ = ∫ _u in b..a, f b := by simp
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hba.le intervalIntegrable_const hlate
        intro u hu
        exact hf ⟨hb, hba⟩ ⟨hb.trans hu.1.le, hu.2⟩ hu.1.le
  calc
    _ ≤ b * f b := hleft
    _ = (b / (a - b)) * ((a - b) * f b) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hright (div_nonneg hb (by linarith))

end SHE
