module

public import SHE.SmoothConvolution
public import SHE.ScalarReduction
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.CompactMollifier
open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff Topology

def bump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) where
  rIn := r/2
  rOut := r
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def kernel (r : ℝ) (hr : 0 < r) : ℝ → ℝ := (bump r hr).normed volume

def mollify (r : ℝ) (hr : 0 < r) (a : ℝ → ℝ) : ℝ → ℝ :=
  SmoothConvolution.convolve a (kernel r hr)

theorem kernel_nonneg (r : ℝ) (hr : 0 < r) (x : ℝ) : 0 ≤ kernel r hr x :=
  (bump r hr).nonneg_normed x

theorem kernel_integrable (r : ℝ) (hr : 0 < r) : Integrable (kernel r hr) :=
  (bump r hr).integrable_normed

theorem kernel_mass (r : ℝ) (hr : 0 < r) : (∫ x,kernel r hr x)=1 :=
  (bump r hr).integral_normed

theorem kernel_smooth (r : ℝ) (hr : 0 < r) : ContDiff ℝ ∞ (kernel r hr) :=
  (bump r hr).contDiff_normed

theorem kernel_compact (r : ℝ) (hr : 0 < r) : HasCompactSupport (kernel r hr) :=
  (bump r hr).hasCompactSupport_normed

theorem mollify_eq (r : ℝ) (hr : 0 < r) (a : ℝ → ℝ) (x : ℝ) :
    mollify r hr a x=∫ y,kernel r hr y*a (x-y) := by
  rw [mollify,SmoothConvolution.convolve_eq]
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => by simp only [smul_eq_mul,mul_comm])

theorem mollify_eq_left (r : ℝ) (hr : 0 < r) (a : ℝ → ℝ) :
    mollify r hr a = kernel r hr ⋆[lsmul ℝ ℝ,volume] a := by
  funext x
  rw [mollify_eq]
  rfl

theorem mollify_boundedSmooth (r : ℝ) (hr : 0 < r) {a : ℝ → ℝ}
    (ha : Continuous a) {M : ℝ} (hM : ∀ x,|a x| ≤ M) :
    SmoothCylinders.BoundedSmooth (mollify r hr a) :=
  SmoothConvolution.convolve_boundedSmooth ha hM (kernel_smooth r hr) (kernel_compact r hr)

theorem mollify_integrand_integrable (r : ℝ) (hr : 0 < r) {a : ℝ → ℝ}
    (ha : Continuous a) {M : ℝ} (hM : ∀ x,|a x| ≤ M) (x : ℝ) :
    Integrable (fun y => kernel r hr y*a (x-y)) := by
  apply ((kernel_integrable r hr).norm.const_mul M).mono'
    (((kernel_smooth r hr).continuous.mul (ha.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
  exact ae_of_all _ (fun y => by
    change |kernel r hr y*a (x-y)| ≤ M*‖kernel r hr y‖
    rw [abs_mul,abs_of_nonneg (kernel_nonneg r hr y)]
    simpa only [Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg r hr y),mul_comm] using
      mul_le_mul_of_nonneg_left (hM (x-y)) (kernel_nonneg r hr y))

theorem mollify_elliptic (r : ℝ) (hr : 0 < r) {a : ℝ → ℝ}
    (ha : Continuous a) {ell M : ℝ} (hell : 0 ≤ ell)
    (hb : ∀ x,ell ≤ a x ∧ a x ≤ M) (x : ℝ) :
    ell ≤ mollify r hr a x ∧ mollify r hr a x ≤ M := by
  have hM : ∀ x,|a x| ≤ M := fun x => by rw [abs_of_nonneg (hell.trans (hb x).1)]; exact (hb x).2
  have hi := mollify_integrand_integrable r hr ha hM x
  have hlo := integral_mono ((kernel_integrable r hr).mul_const ell) hi
    (fun y => mul_le_mul_of_nonneg_left (hb (x-y)).1 (kernel_nonneg r hr y))
  have hhi := integral_mono hi ((kernel_integrable r hr).mul_const M)
    (fun y => mul_le_mul_of_nonneg_left (hb (x-y)).2 (kernel_nonneg r hr y))
  rw [integral_mul_const,kernel_mass,one_mul] at hlo hhi
  exact ⟨by simpa only [mollify_eq] using hlo,by simpa only [mollify_eq] using hhi⟩

theorem mollify_error (r : ℝ) (hr : 0 < r) {a : ℝ → ℝ} (ha : Continuous a)
    {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hh : ∀ x y,|a x-a y| ≤ H*|x-y|^β) (x : ℝ) :
    |mollify r hr a x-a x| ≤ H*r^β := by
  rw [mollify_eq_left]
  change dist (((bump r hr).normed volume ⋆[lsmul ℝ ℝ,volume] a) x) (a x) ≤ H*r^β
  apply (bump r hr).dist_normed_convolution_le ha.aestronglyMeasurable
  intro y hy
  have hd : |y-x| ≤ r := le_of_lt (by simpa only [Metric.mem_ball,Real.dist_eq,bump] using hy)
  simpa only [Real.dist_eq] using (hh y x).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hd hβ) hH)

theorem mollify_holder (r : ℝ) (hr : 0 < r) {a : ℝ → ℝ}
    (ha : Continuous a) {M H β : ℝ} (hM : ∀ x,|a x| ≤ M)
    (hh : ∀ x y,|a x-a y| ≤ H*|x-y|^β) (x z : ℝ) :
    |mollify r hr a x-mollify r hr a z| ≤ H*|x-z|^β := by
  have hix := mollify_integrand_integrable r hr ha hM x
  have hiz := mollify_integrand_integrable r hr ha hM z
  rw [mollify_eq,mollify_eq,← integral_sub hix hiz]
  calc
    _ ≤ ∫ y,|kernel r hr y*a (x-y)-kernel r hr y*a (z-y)| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun y => kernel r hr y*a (x-y)-kernel r hr y*a (z-y))
    _ ≤ ∫ y,kernel r hr y*(H*|x-z|^β) := by
      apply integral_mono (hix.sub hiz).norm ((kernel_integrable r hr).mul_const _)
      intro y
      change |kernel r hr y*a (x-y)-kernel r hr y*a (z-y)| ≤ _
      rw [← mul_sub,abs_mul,abs_of_nonneg (kernel_nonneg r hr y)]
      exact mul_le_mul_of_nonneg_left (by simpa only [sub_sub_sub_cancel_right] using hh (x-y) (z-y))
        (kernel_nonneg r hr y)
    _ = _ := by rw [integral_mul_const,kernel_mass,one_mul]

def radius (n : ℕ) : ℝ := (2:ℝ)⁻¹^n

theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

def approximant (a : ℝ → ℝ) (n : ℕ) : ℝ → ℝ := mollify (radius n) (radius_pos n) a

theorem approximant_boundedSmooth {a : ℝ → ℝ} (ha : Continuous a) {M : ℝ}
    (hM : ∀ x,|a x| ≤ M) (n : ℕ) : SmoothCylinders.BoundedSmooth (approximant a n) :=
  mollify_boundedSmooth _ _ ha hM

theorem approximant_elliptic {a : ℝ → ℝ} (ha : Continuous a) {ell M : ℝ}
    (hell : 0 ≤ ell) (hb : ∀ x,ell ≤ a x ∧ a x ≤ M) (n : ℕ) (x : ℝ) :
    ell ≤ approximant a n x ∧ approximant a n x ≤ M :=
  mollify_elliptic _ _ ha hell hb x

theorem approximant_holder {a : ℝ → ℝ} (ha : Continuous a) {M H β : ℝ}
    (hM : ∀ x,|a x| ≤ M) (hh : ∀ x y,|a x-a y| ≤ H*|x-y|^β)
    (n : ℕ) (x z : ℝ) : |approximant a n x-approximant a n z| ≤ H*|x-z|^β :=
  mollify_holder _ _ ha hM hh x z

theorem approximant_error {a : ℝ → ℝ} (ha : Continuous a) {H β : ℝ}
    (hH : 0 ≤ H) (hβ : 0 ≤ β) (hh : ∀ x y,|a x-a y| ≤ H*|x-y|^β) (n : ℕ) (x : ℝ) :
    |approximant a n x-a x| ≤ H*radius n^β :=
  mollify_error _ _ ha hH hβ hh x

theorem radius_tendsto : Filter.Tendsto radius Filter.atTop (𝓝 (0:ℝ)) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Uniform approximation uses one deterministic sequence, and retains
the very same ellipticity and Hölder constants at every approximation. -/
theorem approximant_tendstoUniformly {a : ℝ → ℝ} (ha : Continuous a) {H β : ℝ}
    (hH : 0 ≤ H) (hβ : 0 < β) (hh : ∀ x y,|a x-a y| ≤ H*|x-y|^β) :
    TendstoUniformly (approximant a) a Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have ht : Filter.Tendsto (fun n => H*radius n^β) Filter.atTop (𝓝 (0:ℝ)) := by
    simpa only [Real.zero_rpow hβ.ne',mul_zero] using
      (radius_tendsto.rpow_const (Or.inr hβ.le)).const_mul H
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x
  have hb : dist (a x) (approximant a n x) ≤ H*radius n^β := by
    simpa only [Real.dist_eq,abs_sub_comm] using approximant_error ha hH hβ.le hh n x
  exact hb.trans_lt hn

end SHE.CompactMollifier
