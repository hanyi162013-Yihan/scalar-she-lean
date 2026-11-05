module

public import SHE.CompactMollifier
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.CompactConvolutionHolder
open Set MeasureTheory Real SmoothConvolution
open scoped ContDiff

/-- Every positive-order derivative of an actual compact smooth kernel
has zero integral. This supplies the Holder cancellation in Bernstein
estimates, rather than charging a bound on the rough coefficient. -/
theorem integral_jet_succ_zero {k : ℝ→ℝ} (hk : ContDiff ℝ ∞ k)
    (hc : HasCompactSupport k) (n : ℕ) : ∫ y,iteratedDeriv (n+1) k y=0 := by
  rw [iteratedDeriv_succ]
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x=>((smooth_jet hk n).differentiable (by simp) x).hasDerivAt)
    (by simpa only [iteratedDeriv_succ] using
      ((smooth_jet hk (n+1)).continuous.integrable_of_hasCompactSupport (compact_jet hc (n+1)) :
        Integrable (iteratedDeriv (n+1) k) volume))
    ((smooth_jet hk n).continuous.integrable_of_hasCompactSupport (compact_jet hc n))

theorem tsupport_jet_subset (k : ℝ→ℝ) (n : ℕ) :
    tsupport (iteratedDeriv n k)⊆tsupport k := by
  induction n with
  | zero=>simpa only [iteratedDeriv_zero] using (Subset.rfl : tsupport k⊆tsupport k)
  | succ n ih=>rw [iteratedDeriv_succ];exact tsupport_deriv_subset.trans ih

/-- A genuine centered convolution keeps the Holder increment of the
rough input. Its derivative kernel is allowed to change sign. -/
theorem centered_bound {a k : ℝ→ℝ} (ha : Continuous a) (hk : Continuous k)
    (hki : Integrable k) {B H β r : ℝ} (hB : ∀ x,|a x|≤B)
    (hH : 0≤H) (hβ : 0≤β) (hr : 0≤r)
    (hholder : ∀ x y,|a x-a y|≤H*|x-y|^β)
    (hzero : (∫ y,k y)=0) (hsupp : Function.support k⊆Icc (-r) r) (x : ℝ) :
    |convolve a k x|≤H*r^β*(∫ y,‖k y‖) := by
  have hi : Integrable (fun y=>a (x-y)*k y) := by
    apply (hki.norm.const_mul B).mono' (by fun_prop)
    exact ae_of_all _ (fun y=>by
      rw [Real.norm_eq_abs,abs_mul]
      simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_right (hB (x-y)) (abs_nonneg (k y)))
  have hcenter : convolve a k x=∫ y,(a (x-y)-a x)*k y := by
    rw [convolve_eq]
    simp only [smul_eq_mul,sub_mul]
    rw [integral_sub hi (hki.const_mul (a x)),integral_const_mul,hzero,mul_zero,sub_zero]
  rw [hcenter,←Real.norm_eq_abs]
  have hdom (y : ℝ) : ‖(a (x-y)-a x)*k y‖≤(H*r^β)*‖k y‖ := by
    by_cases hz : k y=0
    · simp only [hz,mul_zero,norm_zero]
      exact le_rfl
    · have hs:=hsupp hz
      have hyr : |y|≤r:=abs_le.mpr hs
      have hh:=hholder (x-y) x
      simp only [sub_sub_cancel_left,abs_neg] at hh
      have hp:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg y) hyr hβ) hH
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_right (hh.trans hp) (abs_nonneg _)
  have hh:=norm_integral_le_of_norm_le (f:=fun y=>(a (x-y)-a x)*k y)
    (hki.norm.const_mul (H*r^β)) (ae_of_all _ hdom)
  simpa only [integral_const_mul] using hh

end SHE.CompactConvolutionHolder
