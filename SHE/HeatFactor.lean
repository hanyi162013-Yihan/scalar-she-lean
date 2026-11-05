module

public import SHE.HeatAnnihilator
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Group.Integral

/-! Explicit stable first-order Gaussian factors. These are analytic estimates
for the actual variation-of-constants operator used by finite heat spans. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatFactor
open MeasureTheory Set SHE.HeatAnnihilator
open scoped Interval

def realGaussian (p : Parameter) (x : ℝ) : ℂ := gaussian p (x : ℂ)

theorem hasDerivAt_realGaussian (p : Parameter) (x : ℝ) :
    HasDerivAt (realGaussian p)
      ((-2 * p.1 * (x : ℂ) + p.2) * realGaussian p x) x :=
  (hasDerivAt_gaussian p (x : ℂ)).comp_ofReal

theorem continuous_realGaussian (p : Parameter) : Continuous (realGaussian p) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_realGaussian p x).continuousAt)

theorem norm_realGaussian (p : Parameter) (x : ℝ) :
    ‖realGaussian p x‖ = Real.exp (-p.1.re * x ^ 2 + p.2.re * x) := by
  unfold realGaussian gaussian
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re]

theorem realGaussian_mul_neg (p : Parameter) (x : ℝ) :
    realGaussian p x * realGaussian (-p) x = 1 := by
  unfold realGaussian gaussian
  rw [← Complex.exp_add]
  have he : -p.1 * (x : ℂ) ^ 2 + p.2 * x +
      (-(-p).1 * (x : ℂ) ^ 2 + (-p).2 * x) = 0 := by simp; ring
  rw [he, Complex.exp_zero]

def factorSolve (p : Parameter) (c : ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  realGaussian p x * (c + ∫ u in (0 : ℝ)..x, realGaussian (-p) u * g u)

theorem factorSolve_zero (p : Parameter) (c : ℂ) (g : ℝ → ℂ) :
    factorSolve p c g 0 = c := by simp [factorSolve, realGaussian, gaussian]

theorem hasDerivAt_factorSolve (p : Parameter) (c : ℂ) (g : ℝ → ℂ)
    (hg : Continuous g) (x : ℝ) :
    HasDerivAt (factorSolve p c g)
      (g x - (2 * p.1 * (x : ℂ) - p.2) * factorSolve p c g x) x := by
  have hcont := (continuous_realGaussian (-p)).mul hg
  have hi := intervalIntegral.integral_hasDerivAt_right (a := 0)
    (hcont.intervalIntegrable 0 x) hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hd := (hasDerivAt_realGaussian p x).mul (hi.const_add c)
  convert! hd using 1
  dsimp only [factorSolve, Pi.mul_apply]
  have h := realGaussian_mul_neg p x
  linear_combination -(g x) * h

theorem continuous_factorSolve (p : Parameter) (c : ℂ) (g : ℝ → ℂ) (hg : Continuous g) :
    Continuous (factorSolve p c g) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_factorSolve p c g hg x).continuousAt)

def tailKernel (k B x : ℝ) : ℝ := Real.exp (-k * x ^ 2 + B * |x|)

theorem tailKernel_nonneg (k B x : ℝ) : 0 ≤ tailKernel k B x := (Real.exp_pos _).le

theorem tailKernel_le_gaussian {k : ℝ} (hk : 0 < k) (B x : ℝ) :
    tailKernel k B x ≤ Real.exp (B ^ 2 / (2 * k)) * Real.exp (-(k / 2) * x ^ 2) := by
  have hh : B * |x| - k / 2 * x ^ 2 ≤ B ^ 2 / (2 * k) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * k)).mpr
    rw [← sq_abs x]
    nlinarith [sq_nonneg (k * |x| - B)]
  rw [tailKernel, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem integrable_tailKernel {k : ℝ} (hk : 0 < k) (B : ℝ) : Integrable (tailKernel k B) := by
  have h := (integrable_exp_neg_mul_sq (show 0 < k / 2 by positivity)).const_mul
    (Real.exp (B ^ 2 / (2 * k)))
  apply h.mono'
  · unfold tailKernel
    fun_prop
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tailKernel_nonneg k B x)]
      exact tailKernel_le_gaussian hk B x)

/-- Between zero and an endpoint, the Gaussian integrating-factor kernel is
dominated by a translated integrable Gaussian. This is uniform in imaginary
linear phases, so it applies to physical and Fourier heat spans alike. -/
theorem weighted_factor_kernel_bound (p : Parameter) {γ k B x u : ℝ}
    (hk : 0 < k) (ha : γ + k ≤ p.1.re) (hb : |p.2.re| ≤ B)
    (hu : u ∈ uIcc (0 : ℝ) x) :
    ‖realGaussian p x * realGaussian (-p) u‖ * Real.exp (-γ * u ^ 2) ≤
      Real.exp (-γ * x ^ 2) * tailKernel k B (x - u) := by
  have hbetween : (x - u) ^ 2 ≤ x ^ 2 - u ^ 2 := by
    rcases le_total (0 : ℝ) x with hx | hx
    · rw [uIcc_of_le hx] at hu
      nlinarith [hu.1, hu.2]
    · rw [uIcc_of_ge hx] at hu
      nlinarith [hu.1, hu.2]
  have hdiff : 0 ≤ x ^ 2 - u ^ 2 := (sq_nonneg (x - u)).trans hbetween
  have hlin : p.2.re * (x - u) ≤ B * |x - u| :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hb (abs_nonneg _)))
  rw [norm_mul, norm_realGaussian, norm_realGaussian]
  simp only [Prod.fst_neg, Prod.snd_neg, Complex.neg_re]
  rw [← Real.exp_add, ← Real.exp_add, tailKernel, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right ha hdiff
  have h2 := mul_le_mul_of_nonneg_left hbetween hk.le
  nlinarith

theorem homogeneous_factor_bound (p : Parameter) {γ k B : ℝ}
    (hk : 0 < k) (ha : γ + k ≤ p.1.re) (hb : |p.2.re| ≤ B) (x : ℝ) :
    ‖realGaussian p x‖ ≤ Real.exp (B ^ 2 / (2 * k)) * Real.exp (-γ * x ^ 2) := by
  have h := weighted_factor_kernel_bound p (x := x) (u := 0) hk ha hb (by simp)
  have hzero : realGaussian (-p) 0 = 1 := by simp [realGaussian, gaussian]
  simp only [hzero, mul_one, zero_pow (by decide : 2 ≠ 0), mul_zero,
    Real.exp_zero, sub_zero] at h
  have hK := tailKernel_le_gaussian hk B x
  have hE : Real.exp (-(k / 2) * x ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hconst := hK.trans (mul_le_of_le_one_right (Real.exp_pos _).le hE)
  exact h.trans (by nlinarith [Real.exp_pos (-γ * x ^ 2)])

/-- A stable first-order variation-of-constants operator preserves a fixed
weakened Gaussian envelope on both half-lines, with an explicit finite mass. -/
theorem factorSolve_gaussian_bound (p : Parameter) (c : ℂ) (g : ℝ → ℂ)
    (hg : Continuous g) {γ k B M : ℝ} (hk : 0 < k) (hM : 0 ≤ M)
    (ha : γ + k ≤ p.1.re) (hb : |p.2.re| ≤ B)
    (hgbound : ∀ u, ‖g u‖ ≤ M * Real.exp (-γ * u ^ 2)) (x : ℝ) :
    ‖factorSolve p c g x‖ ≤
      (Real.exp (B ^ 2 / (2 * k)) * ‖c‖ + M * (∫ v, tailKernel k B v)) * Real.exp (-γ * x ^ 2) := by
  let F : ℝ → ℂ := fun u => realGaussian p x * realGaussian (-p) u * g u
  let D : ℝ := M * Real.exp (-γ * x ^ 2)
  have hD : 0 ≤ D := mul_nonneg hM (Real.exp_pos _).le
  have hF : IntervalIntegrable F volume 0 x :=
    ((continuous_const.mul (continuous_realGaussian (-p))).mul hg).intervalIntegrable 0 x
  have hshift : Integrable (fun u => tailKernel k B (x - u)) :=
    (volume.measurePreserving_sub_left x).integrable_comp_of_integrable (integrable_tailKernel hk B)
  have hpoint : ∀ᵐ u ∂volume.restrict (uIoc (0 : ℝ) x), ‖F u‖ ≤ D * tailKernel k B (x - u) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    have hker := weighted_factor_kernel_bound p hk ha hb (uIoc_subset_uIcc hu)
    have hh := mul_le_mul_of_nonneg_left (hgbound u) (norm_nonneg (realGaussian p x * realGaussian (-p) u))
    have hm := mul_le_mul_of_nonneg_left hker hM
    dsimp only [F, D]
    rw [norm_mul]
    nlinarith
  have hInt : ‖∫ u in (0 : ℝ)..x, F u‖ ≤ D * (∫ v, tailKernel k B v) := by
    calc
      _ ≤ ∫ u in uIoc (0 : ℝ) x, ‖F u‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ u in uIoc (0 : ℝ) x, D * tailKernel k B (x - u) :=
        integral_mono_ae ((intervalIntegrable_iff.mp hF).norm) ((hshift.const_mul D).restrict) hpoint
      _ = D * ∫ u in uIoc (0 : ℝ) x, tailKernel k B (x - u) := integral_const_mul _ _
      _ ≤ D * ∫ u, tailKernel k B (x - u) :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hshift
          (ae_of_all _ (fun u => tailKernel_nonneg k B (x - u)))) hD
      _ = D * ∫ v, tailKernel k B v := by rw [integral_sub_left_eq_self]
  have hEq : factorSolve p c g x = realGaussian p x * c + ∫ u in (0 : ℝ)..x, F u := by
    unfold factorSolve
    rw [mul_add, ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only [F]
    ring
  rw [hEq]
  have hh := homogeneous_factor_bound p hk ha hb x
  have hc := mul_le_mul_of_nonneg_right hh (norm_nonneg c)
  have hnorm := norm_add_le (realGaussian p x * c) (∫ u in (0 : ℝ)..x, F u)
  rw [norm_mul] at hnorm
  dsimp only [D] at hInt
  nlinarith

/-- Genuine variation of constants recovers every continuously forced solution
of a stable factor from its initial value. -/
theorem factorSolve_eq_of_hasDerivAt (p : Parameter) (f g : ℝ → ℂ) (hg : Continuous g)
    (hf : ∀ x, HasDerivAt f (g x - (2 * p.1 * (x : ℂ) - p.2) * f x) x) :
    factorSolve p (f 0) g = f := by
  have hd : ∀ x, HasDerivAt (fun u => realGaussian (-p) u * f u)
      (realGaussian (-p) x * g x) x := by
    intro x
    convert! (hasDerivAt_realGaussian (-p) x).mul (hf x) using 1
    simp only [Prod.fst_neg, Prod.snd_neg]
    ring
  funext x
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := x) (fun u _ => hd u)
    (((continuous_realGaussian (-p)).mul hg).intervalIntegrable 0 x)
  unfold factorSolve
  rw [hInt]
  have hzero : realGaussian (-p) 0 = 1 := by simp [realGaussian, gaussian]
  rw [hzero, one_mul]
  calc
    _ = (realGaussian p x * realGaussian (-p) x) * f x := by ring
    _ = _ := by rw [realGaussian_mul_neg, one_mul]

theorem factorSolve_affine_integral (p : Parameter) (c : ℂ) (g : ℝ → ℂ) (x : ℝ) :
    factorSolve p c g x = realGaussian p x *
      (c + (x : ℂ) * ∫ t in Icc (0 : ℝ) 1, realGaussian (-p) (x * t) * g (x * t)) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := fun u => realGaussian (-p) u * g u) (a := 0) (b := 1) x
  simp only [mul_zero, mul_one, Complex.real_smul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  unfold factorSolve
  rw [h]

theorem continuous_realGaussian_joint : Continuous (fun q : Parameter × ℝ => realGaussian q.1 q.2) := by
  unfold realGaussian gaussian
  fun_prop

/-- Joint continuity in factor parameters, initial value, forcing parameter
and endpoint follows from a genuine integral on one fixed compact interval. -/
theorem continuous_factorSolve_family {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (p : X → Parameter) (c : X → ℂ) (g : X → ℝ → ℂ)
    (hp : Continuous p) (hc : Continuous c) (hg : Continuous (Function.uncurry g)) :
    Continuous (fun q : X × ℝ => factorSolve (p q.1) (c q.1) (g q.1) q.2) := by
  have harg : Continuous (fun q : (X × ℝ) × ℝ => q.1.2 * q.2) := continuous_fst.snd.mul continuous_snd
  have hG : Continuous (fun q : (X × ℝ) × ℝ =>
      realGaussian (-(p q.1.1)) (q.1.2 * q.2)) :=
    continuous_realGaussian_joint.comp (((hp.comp continuous_fst.fst).neg).prodMk harg)
  have hg' : Continuous (fun q : (X × ℝ) × ℝ => g q.1.1 (q.1.2 * q.2)) :=
    hg.comp (continuous_fst.fst.prodMk harg)
  have hI : Continuous (fun q : X × ℝ => ∫ t in Icc (0 : ℝ) 1,
      realGaussian (-(p q.1)) (q.2 * t) * g q.1 (q.2 * t)) :=
    continuous_parametric_integral_of_continuous (hG.mul hg') isCompact_Icc
  have hP : Continuous (fun q : X × ℝ => realGaussian (p q.1) q.2) :=
    continuous_realGaussian_joint.comp ((hp.comp continuous_fst).prodMk continuous_snd)
  have hOut := hP.mul ((hc.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul hI))
  convert! hOut using 1
  funext q
  exact factorSolve_affine_integral (p q.1) (c q.1) (g q.1) q.2

end SHE.HeatFactor
