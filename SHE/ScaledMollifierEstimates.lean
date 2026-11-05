module

public import SHE.CompactConvolutionHolder
public import SHE.ScaledMollifierKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ScaledMollifierEstimates
open Set MeasureTheory Real SmoothConvolution ScaledMollifierKernel CompactConvolutionHolder
open scoped ContDiff

def mollify (r : ℝ) (a : ℝ→ℝ) : ℝ→ℝ:=convolve a (kernel r)
def jetConstant (n : ℕ) : ℝ:=∫ y,‖iteratedDeriv n unitKernel y‖

theorem jetConstant_nonneg (n : ℕ) : 0≤jetConstant n:=integral_nonneg (fun _=>norm_nonneg _)

theorem mollify_boundedSmooth {a : ℝ→ℝ} (ha : Continuous a) {B : ℝ}
    (hB : ∀ x,|a x|≤B) {r : ℝ} (hr : 0<r) :
    SmoothCylinders.BoundedSmooth (mollify r a):=
  convolve_boundedSmooth ha hB (kernel_smooth r) (kernel_compact hr)

/-- All positive-order derivatives of the ACTUAL smoothing preserve
one Holder increment, with the exact scale r^(beta-n). -/
theorem mollify_jet_holder {a : ℝ→ℝ} (ha : Continuous a) {B H β r : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β) (hr : 0<r)
    (hholder : ∀ x y,|a x-a y|≤H*|x-y|^β) (n : ℕ) (hn : 0<n) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (mollify r a) x‖≤H*jetConstant n*r^(β-(n:ℝ)) := by
  obtain ⟨m,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hzero:=integral_jet_succ_zero (kernel_smooth r) (kernel_compact hr) m
  have hsupp : Function.support (iteratedDeriv (m+1) (kernel r))⊆Icc (-r) r:=
    (subset_tsupport _).trans ((tsupport_jet_subset (kernel r) (m+1)).trans (kernel_tsupport hr))
  have hb:=centered_bound ha (smooth_jet (kernel_smooth r) (m+1)).continuous
    ((smooth_jet (kernel_smooth r) (m+1)).continuous.integrable_of_hasCompactSupport
      (compact_jet (kernel_compact hr) (m+1))) hB hH hβ hr.le hholder hzero hsupp x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv (m+1) (convolve a (kernel r)) x‖≤_
  rw [iteratedDeriv_convolve ha (kernel_smooth r) (kernel_compact hr)]
  calc
    _≤H*r^β*(∫ y,‖iteratedDeriv (m+1) (kernel r) y‖):=by
      simpa only [Real.norm_eq_abs] using hb
    _=H*jetConstant (m+1)*r^(β-((m+1:ℕ):ℝ)):=by
      rw [kernel_jet_l1 hr]
      have hi : (r⁻¹)^(m+1)=r^(-((m+1:ℕ):ℝ)):=by
        rw [Real.rpow_neg hr.le,Real.rpow_natCast,inv_pow]
      rw [hi]
      have hp : r^β*r^(-((m+1:ℕ):ℝ))=r^(β-((m+1:ℕ):ℝ)):=by
        rw [←Real.rpow_add hr]
        congr 1
      unfold jetConstant
      calc
        _=H*(∫ y,‖iteratedDeriv (m+1) unitKernel y‖)*(r^β*r^(-((m+1:ℕ):ℝ))):=by ring
        _=_:=by rw [hp]

/-- Uniform approximation by the same scaled compact kernels used for
the Bernstein derivative estimate. -/
theorem mollify_error {a : ℝ→ℝ} (ha : Continuous a) {B H β r : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β) (hr : 0<r)
    (hholder : ∀ x y,|a x-a y|≤H*|x-y|^β) (x : ℝ) :
    |mollify r a x-a x|≤H*r^β := by
  have hi : Integrable (fun y=>a (x-y)*kernel r y) := by
    apply ((kernel_integrable hr).norm.const_mul B).mono'
      (((ha.comp (continuous_const.sub continuous_id)).mul (kernel_smooth r).continuous).aestronglyMeasurable)
    exact ae_of_all _ (fun y=>by
      change ‖a (x-y)*kernel r y‖≤B*‖kernel r y‖
      rw [Real.norm_eq_abs,abs_mul]
      simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_right (hB (x-y)) (abs_nonneg (kernel r y)))
  have hc : mollify r a x-a x=∫ y,(a (x-y)-a x)*kernel r y := by
    rw [mollify,convolve_eq]
    simp only [smul_eq_mul,sub_mul]
    rw [integral_sub hi ((kernel_integrable hr).const_mul (a x)),integral_const_mul,kernel_mass hr,mul_one]
  rw [hc,←Real.norm_eq_abs]
  have hdom (y : ℝ) : ‖(a (x-y)-a x)*kernel r y‖≤(H*r^β)*kernel r y:=by
    by_cases hz : kernel r y=0
    · simp only [hz,mul_zero,norm_zero]
      exact le_rfl
    · have hs:=kernel_tsupport hr (subset_tsupport _ hz)
      have hp:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg y) (abs_le.mpr hs) hβ) hH
      have hh:=hholder (x-y) x
      simp only [sub_sub_cancel_left,abs_neg] at hh
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (kernel_nonneg hr.le y)]
      exact mul_le_mul_of_nonneg_right (hh.trans hp) (kernel_nonneg hr.le y)
  have hh:=norm_integral_le_of_norm_le (f:=fun y=>(a (x-y)-a x)*kernel r y)
    ((kernel_integrable hr).const_mul (H*r^β)) (ae_of_all _ hdom)
  simpa only [integral_const_mul,kernel_mass hr,mul_one] using hh

end SHE.ScaledMollifierEstimates
